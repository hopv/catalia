use std::io::Write as IoWrite;
use std::panic;
use std::path::PathBuf;
use std::time::Duration;

use super::catamorphism_parser;
use super::chc::{AbsInstance, CEX};
use super::enc::{EncodeCtx, Encoder};
use crate::common::{smt::FullParser as Parser, *};
use crate::dtyp;

const MAX_LLM_ATTEMPTS: usize = 5;
const ENC_CHECK_TIMEOUT: usize = 4;
const HTTP_TIMEOUT_SECS: u64 = 120;

// ---------------------------------------------------------------------------
// Query logging
// ---------------------------------------------------------------------------

struct QueryLogger {
    dir: PathBuf,
}

impl QueryLogger {
    fn new() -> Self {
        let dir = std::env::temp_dir().join(format!("catalia-llm-{}", std::process::id()));
        if let Err(e) = std::fs::create_dir_all(&dir) {
            log_info!("Warning: failed to create LLM log dir {:?}: {}", dir, e);
        } else {
            log_info!("LLM query logs: {}", dir.display());
        }
        Self { dir }
    }

    fn log_query(&self, attempt: usize, messages: &[Message], response: &str) {
        // Write input (conversation sent to LLM)
        let input_path = self.dir.join(format!("attempt-{}-input.txt", attempt));
        if let Ok(mut f) = std::fs::File::create(&input_path) {
            for msg in messages {
                let _ = writeln!(f, "=== {} ===", msg.role);
                let _ = writeln!(f, "{}", msg.content);
                let _ = writeln!(f);
            }
        }

        // Write output (LLM response)
        let output_path = self.dir.join(format!("attempt-{}-output.txt", attempt));
        if let Ok(mut f) = std::fs::File::create(&output_path) {
            let _ = write!(f, "{}", response);
        }
    }

    fn log_error(&self, attempt: usize, messages: &[Message], error: &str) {
        let input_path = self.dir.join(format!("attempt-{}-input.txt", attempt));
        if let Ok(mut f) = std::fs::File::create(&input_path) {
            for msg in messages {
                let _ = writeln!(f, "=== {} ===", msg.role);
                let _ = writeln!(f, "{}", msg.content);
                let _ = writeln!(f);
            }
        }

        let error_path = self.dir.join(format!("attempt-{}-error.txt", attempt));
        if let Ok(mut f) = std::fs::File::create(&error_path) {
            let _ = write!(f, "{}", error);
        }
    }
}

// ---------------------------------------------------------------------------
// LLM provider abstraction
// ---------------------------------------------------------------------------

struct Message {
    role: String,
    content: String,
}

trait LlmProvider {
    fn name(&self) -> &str;
    fn request(&self, messages: &[Message]) -> Res<String>;
}

// ---------------------------------------------------------------------------
// OpenAI provider
// ---------------------------------------------------------------------------

struct OpenAiProvider {
    api_key: String,
    model: String,
    base_url: String,
}

impl OpenAiProvider {
    fn new() -> Res<Self> {
        let api_key = std::env::var("OPENAI_API_KEY").map_err(|_| {
            Error::from_kind(crate::errors::ErrorKind::Msg(
                "OPENAI_API_KEY not set".into(),
            ))
        })?;
        let model = std::env::var("OPENAI_MODEL").unwrap_or_else(|_| "gpt-5-mini".into());
        log_info!("Using OpenAI model: {}", model);
        let mut base_url =
            std::env::var("OPENAI_BASE_URL").unwrap_or_else(|_| "https://api.openai.com".into());
        // Strip trailing /v1 to avoid double /v1/v1/... when we append the path
        base_url = base_url.trim_end_matches('/').to_string();
        if base_url.ends_with("/v1") {
            base_url.truncate(base_url.len() - 3);
        }
        Ok(Self {
            api_key,
            model,
            base_url,
        })
    }
}

fn extract_openai_output_text(resp_body: &serde_json::Value) -> Option<String> {
    let output = resp_body.get("output")?.as_array()?;
    for item in output {
        if item.get("type")?.as_str()? != "message" {
            continue;
        }
        let content = item.get("content")?.as_array()?;
        for part in content {
            if part.get("type")?.as_str()? == "output_text" {
                if let Some(t) = part.get("text").and_then(|v| v.as_str()) {
                    return Some(t.to_string());
                }
            }
        }
    }
    None
}

impl LlmProvider for OpenAiProvider {
    fn name(&self) -> &str {
        "OpenAI"
    }

    fn request(&self, messages: &[Message]) -> Res<String> {
        let url = format!("{}/v1/responses", self.base_url);

        // The Responses API uses a top-level "instructions" field for system
        // messages; "role: system" is not valid inside the "input" array.
        let instructions: String = messages
            .iter()
            .filter(|m| m.role == "system")
            .map(|m| m.content.as_str())
            .collect::<Vec<_>>()
            .join("\n");

        let input: Vec<serde_json::Value> = messages
            .iter()
            .filter(|m| m.role != "system")
            .map(|m| {
                serde_json::json!({
                    "role": m.role,
                    "content": m.content,
                })
            })
            .collect();

        let mut body = serde_json::json!({
            "model": self.model,
            "input": input,
        });
        if !instructions.is_empty() {
            body["instructions"] = serde_json::Value::String(instructions);
        }
        body["max_output_tokens"] = serde_json::Value::Number(1600.into());
        body["reasoning"] = serde_json::json!({"effort":"low"}); // for development

        let agent = ureq::AgentBuilder::new()
            .timeout_connect(Duration::from_secs(30))
            .timeout_read(Duration::from_secs(HTTP_TIMEOUT_SECS))
            .timeout_write(Duration::from_secs(30))
            .build();

        let resp = match agent
            .post(&url)
            .set("Authorization", &format!("Bearer {}", self.api_key))
            .set("Content-Type", "application/json")
            .send_string(&body.to_string())
        {
            Ok(r) => r,
            Err(ureq::Error::Status(code, r)) => {
                let text = r
                    .into_string()
                    .unwrap_or_else(|_| "<failed to read body>".into());
                return Err(Error::from_kind(crate::errors::ErrorKind::Msg(format!(
                    "OpenAI API request failed: HTTP {}: {}",
                    code, text
                ))));
            }
            Err(e) => {
                return Err(Error::from_kind(crate::errors::ErrorKind::Msg(format!(
                    "OpenAI API request failed: {}",
                    e
                ))));
            }
        };

        let resp_body: serde_json::Value = resp.into_json().map_err(|e| {
            Error::from_kind(crate::errors::ErrorKind::Msg(format!(
                "Failed to parse OpenAI response: {}",
                e
            )))
        })?;

        extract_openai_output_text(&resp_body).ok_or_else(|| {
            Error::from_kind(crate::errors::ErrorKind::Msg(format!(
                "Unexpected OpenAI response format: {}",
                resp_body
            )))
        })
    }
}

// ---------------------------------------------------------------------------
// Anthropic provider
// ---------------------------------------------------------------------------

struct AnthropicProvider {
    api_key: String,
    model: String,
}

impl AnthropicProvider {
    fn new() -> Res<Self> {
        let api_key = std::env::var("ANTHROPIC_API_KEY").map_err(|_| {
            Error::from_kind(crate::errors::ErrorKind::Msg(
                "ANTHROPIC_API_KEY not set".into(),
            ))
        })?;
        let model =
            std::env::var("ANTHROPIC_MODEL").unwrap_or_else(|_| "claude-sonnet-4-20250514".into());
        Ok(Self { api_key, model })
    }
}

impl LlmProvider for AnthropicProvider {
    fn name(&self) -> &str {
        "Anthropic"
    }
    fn request(&self, messages: &[Message]) -> Res<String> {
        let url = "https://api.anthropic.com/v1/messages";

        // Separate system message from user/assistant messages
        let system_text: String = messages
            .iter()
            .filter(|m| m.role == "system")
            .map(|m| m.content.clone())
            .collect::<Vec<_>>()
            .join("\n");

        let msgs: Vec<serde_json::Value> = messages
            .iter()
            .filter(|m| m.role != "system")
            .map(|m| {
                serde_json::json!({
                    "role": m.role,
                    "content": m.content,
                })
            })
            .collect();

        let body = serde_json::json!({
            "model": self.model,
            "max_tokens": 4096,
            "system": system_text,
            "messages": msgs,
        });

        let agent = ureq::AgentBuilder::new()
            .timeout_connect(Duration::from_secs(30))
            .timeout_read(Duration::from_secs(HTTP_TIMEOUT_SECS))
            .timeout_write(Duration::from_secs(30))
            .build();

        let resp = agent
            .post(url)
            .set("x-api-key", &self.api_key)
            .set("anthropic-version", "2023-06-01")
            .set("Content-Type", "application/json")
            .send_string(&body.to_string())
            .map_err(|e| {
                Error::from_kind(crate::errors::ErrorKind::Msg(format!(
                    "Anthropic API request failed: {}",
                    e
                )))
            })?;

        let resp_body: serde_json::Value = resp.into_json().map_err(|e| {
            Error::from_kind(crate::errors::ErrorKind::Msg(format!(
                "Failed to parse Anthropic response: {}",
                e
            )))
        })?;

        resp_body["content"][0]["text"]
            .as_str()
            .map(|s| s.to_string())
            .ok_or_else(|| {
                Error::from_kind(crate::errors::ErrorKind::Msg(format!(
                    "Unexpected Anthropic response format: {}",
                    resp_body
                )))
            })
    }
}

// ---------------------------------------------------------------------------
// Provider selection
// ---------------------------------------------------------------------------

fn create_provider() -> Res<Box<dyn LlmProvider>> {
    if std::env::var("ANTHROPIC_API_KEY").is_ok() {
        Ok(Box::new(AnthropicProvider::new()?))
    } else if std::env::var("OPENAI_API_KEY").is_ok() {
        Ok(Box::new(OpenAiProvider::new()?))
    } else {
        bail!("LLM learning requires ANTHROPIC_API_KEY or OPENAI_API_KEY to be set")
    }
}

// ---------------------------------------------------------------------------
// Prompt construction
// ---------------------------------------------------------------------------

fn build_system_prompt() -> String {
    r#"You are an expert in program verification, abstract interpretation, and Horn clause solving.

Your task is to synthesize catamorphism encoders for algebraic data types (ADTs).
A catamorphism maps each constructor of an ADT to a fixed-length tuple of integers.
Each tuple component is defined as an SMT-LIB integer expression over the constructor's selector arguments.

A selector argument contributes parameters as follows:

- If the selector has type Int:
  it contributes exactly ONE integer parameter (its value).

- If the selector has ADT type T, and T is encoded as an N-component tuple:
  it contributes exactly N integer parameters, representing the recursive encoding result.

Parameters appear in the SAME ORDER as selector declarations, and recursive components appear in tuple order.

Your objective is to produce a sound and simple structural encoding. Prefer the smallest number of components sufficient to represent structural measures (for example length, size, sum, or similar).

------------------------------------------------------------
OUTPUT FORMAT (STRICT)
------------------------------------------------------------

Produce EXACTLY ONE s-expression block.
Do NOT include explanations, comments, markdown, or any extra text.

The structure must be:

(
  ("DatatypeName1"
    ("Constructor1"
      ((param1 param2 ...) expr1 expr2 ...)
    )
    ("Constructor2"
      ((param1 param2 ...) expr1 expr2 ...)
    )
    ...
  )
  ("DatatypeName2"
    ("Constructor1"
      ((param1 ...) expr1 ...)
    )
    ...
  )
)

IMPORTANT: each constructor body is wrapped in an EXTRA pair of parentheses.
The inner list contains FIRST the parameter list, then the result expressions.
("ConstructorName" ((params...) expr1 expr2 ...))
                   ^                             ^
                   extra outer parens around the entire body

------------------------------------------------------------
MANDATORY RULES
------------------------------------------------------------

1. Include EVERY datatype listed in the Required Datatypes section.
2. Include EVERY constructor of each datatype.
3. Every constructor of the SAME datatype MUST produce the SAME number of result expressions.
4. This number defines the encoding dimension of that datatype.
5. Parameter lists MUST contain exactly one parameter per Int selector and exactly N parameters per recursive selector, where N is the encoding dimension of that recursive datatype.
6. Constructors with no selectors MUST use an empty parameter list: ()
7. All result expressions MUST be integer expressions.
8. Use ONLY SMT-LIB syntax:

   (+ a b)
   (- a b)
   (* a b)
   (ite cond then else)
   (= a b)
   (>= a b)
   (> a b)
   (<= a b)
   (< a b)
   (and ...)
   (or ...)
   (not ...)

9. Do NOT use division, quantifiers, let bindings, or uninterpreted functions.
10. Parameter names must be simple ASCII identifiers (example: x, y, l0, l1, r0).
11. The entire output must be wrapped in ONE outer parenthesized list.

------------------------------------------------------------
PARAMETER ORDERING EXAMPLE
------------------------------------------------------------

Datatype:

  cons(head:Int, tail:List)

If List has a 2-component encoding, the parameters are:

  (head tail_0 tail_1)

NOT:

  (head tail)

------------------------------------------------------------
EXAMPLE: length encoding
------------------------------------------------------------

(
  ("IList"
    ("nil"
      (() 0)
    )
    ("cons"
      ((x t) (+ t 1))
    )
  )
)

------------------------------------------------------------
EXAMPLE: length and sum encoding
------------------------------------------------------------

(
  ("IList"
    ("nil"
      (() 0 0)
    )
    ("cons"
      ((x t_len t_sum)
        (+ t_len 1)
        (+ t_sum x)
      )
    )
  )
)

------------------------------------------------------------
CRITICAL
------------------------------------------------------------

Output ONLY the s-expression.
Any additional text is invalid.
"#.to_string()
}

/// Build the required datatypes section listing all datatypes and their constructors
fn build_required_datatypes(encs: &BTreeMap<Typ, Encoder>) -> String {
    let mut s = "## Required Datatypes\n\nYou MUST provide encoders for ALL of the following datatypes and constructors:\n\n".to_string();
    for (typ, enc) in encs.iter() {
        let (dt, prms) = typ.dtyp_inspect().unwrap();
        s += &format!("- Datatype `{}`:\n", dt.name);
        for (constr_name, sels) in dt.news.iter() {
            let sel_descs: Vec<String> = sels
                .iter()
                .map(|(sel_name, sel_ty)| {
                    let ty = sel_ty.to_type(Some(prms)).unwrap();
                    if encs.contains_key(&ty) {
                        format!(
                            "{} (recursive, encoded as {} int(s))",
                            sel_name, enc.n_params
                        )
                    } else {
                        format!("{}: {}", sel_name, ty)
                    }
                })
                .collect();
            if sel_descs.is_empty() {
                s += &format!("  - `{}` (no arguments)\n", constr_name);
            } else {
                s += &format!("  - `{}` ({})\n", constr_name, sel_descs.join(", "));
            }
        }
    }
    s
}

fn build_chc_context(instance: &AbsInstance, encs: &BTreeMap<Typ, Encoder>) -> String {
    let mut chc_buf = Vec::new();
    match instance.dump_as_smt2(&mut chc_buf, "", false) {
        Ok(()) => {}
        Err(e) => {
            log_info!(
                "Warning: CHC dump failed (LLM will get partial context): {}",
                e
            );
        }
    }
    let chc_str = String::from_utf8_lossy(&chc_buf);

    let mut enc_str = String::new();
    for (tag, e) in encs.iter() {
        enc_str += &format!("[{}] {}\n", tag, e);
    }

    format!(
        "{}\n\n## CHC Problem (SMT-LIB format)\n\n```smt2\n{}\n```\n\n## Current Encoders\n\n```\n{}\n```\n\n\
The current encoders are insufficient. Please propose better encoders that can help \
distinguish the spurious counterexample from real ones.",
        build_required_datatypes(encs),
        chc_str, enc_str
    )
}

fn build_cex_feedback(cex: &CEX, prev_attempt: Option<&str>) -> String {
    let mut s = format!(
        "## Spurious Counterexample\n\n```\n{}\n```\n\n\
The encoder must make this CEX unsatisfiable when the ADT variables are replaced \
by their encoded integer representations.",
        cex
    );
    if let Some(prev) = prev_attempt {
        // Only include a short note about the previous attempt, not the full response
        // (the full response is already in the conversation as an assistant message)
        let truncated = if prev.len() > 200 {
            format!("{}...(truncated)", &prev[..200])
        } else {
            prev.to_string()
        };
        s += &format!(
            "\n\n## Previous Attempt (failed)\n\nYour previous proposal did not refute the CEX. \
First few chars: `{}`\n\nPlease try a different encoding strategy.",
            truncated
        );
    }
    s
}

// ---------------------------------------------------------------------------
// Response parsing
// ---------------------------------------------------------------------------

/// Extract the outermost s-expression from an LLM response, stripping markdown fences
fn extract_sexp(response: &str) -> Option<String> {
    let text = strip_markdown_fences(response);
    let bytes = text.as_bytes();

    // find first '('
    let start = bytes.iter().position(|&b| b == b'(')?;

    let mut depth = 0i32;
    for (i, &b) in bytes[start..].iter().enumerate() {
        match b {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(text[start..start + i + 1].to_string());
                }
            }
            _ => {}
        }
    }
    None
}

fn strip_markdown_fences(text: &str) -> String {
    let mut result = String::new();
    let mut in_fence = false;
    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("```") {
            in_fence = !in_fence;
            if !in_fence {
                // closing fence, skip
                continue;
            }
            // opening fence, skip
            continue;
        }
        if in_fence || !trimmed.is_empty() {
            result.push_str(line);
            result.push('\n');
        }
    }
    result
}

/// Parse an LLM response into encoders, catching panics from the parser
fn parse_llm_response(
    response: &str,
    encs: &BTreeMap<Typ, Encoder>,
) -> Res<BTreeMap<Typ, Encoder>> {
    let sexp = extract_sexp(response).ok_or_else(|| {
        Error::from_kind(crate::errors::ErrorKind::Msg(
            "Could not find s-expression in LLM response".into(),
        ))
    })?;

    // The catamorphism parser has unwrap!/assert! paths that can panic on
    // malformed input. Since LLM output is untrusted, catch panics and
    // convert them to Err so the retry loop can continue.
    let sexp_clone = sexp.clone();
    // TODO: fix this, by returning a Result from the parser instead of panicking on errors
    let parse_result =
        panic::catch_unwind(move || catamorphism_parser::parse_catamorphism_str(&sexp_clone));

    let parsed = match parse_result {
        Ok(Ok(p)) => p,
        Ok(Err(e)) => return Err(e),
        Err(panic_info) => {
            let msg = if let Some(s) = panic_info.downcast_ref::<String>() {
                s.clone()
            } else if let Some(s) = panic_info.downcast_ref::<&str>() {
                s.to_string()
            } else {
                "unknown panic in parser".to_string()
            };
            return Err(Error::from_kind(crate::errors::ErrorKind::Msg(format!(
                "Parser panicked on LLM output: {}",
                msg
            ))));
        }
    };

    let build_result = panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        catamorphism_parser::build_encoding_from_approx(parsed, encs)
    }));

    match build_result {
        Ok(Ok(new_encs)) => Ok(new_encs),
        Ok(Err(e)) => Err(e),
        Err(panic_info) => {
            let msg = if let Some(s) = panic_info.downcast_ref::<String>() {
                s.clone()
            } else if let Some(s) = panic_info.downcast_ref::<&str>() {
                s.to_string()
            } else {
                "unknown panic in encoder build".to_string()
            };
            Err(Error::from_kind(crate::errors::ErrorKind::Msg(format!(
                "Encoder build panicked on LLM output: {}",
                msg
            ))))
        }
    }
}

// ---------------------------------------------------------------------------
// Structural validation of encoder proposals
// ---------------------------------------------------------------------------

/// Validate that proposed encoders have the correct structure:
/// - Every datatype present in the original encoders is covered
/// - Every constructor of each datatype is present
/// - All constructors produce the same number of result expressions
/// - Parameter counts match expected selector counts
fn validate_encoder_structure(
    new_encs: &BTreeMap<Typ, Encoder>,
    original_encs: &BTreeMap<Typ, Encoder>,
) -> Res<()> {
    for (typ, _original_enc) in original_encs.iter() {
        let new_enc = new_encs.get(typ).ok_or_else(|| {
            Error::from_kind(crate::errors::ErrorKind::Msg(format!(
                "LLM proposal missing encoder for datatype {}",
                typ
            )))
        })?;

        let (dt, prms) = typ.dtyp_inspect().unwrap();

        // Check every constructor is present
        for (constr_name, sels) in dt.news.iter() {
            let approx = new_enc.approxs.get(constr_name).ok_or_else(|| {
                Error::from_kind(crate::errors::ErrorKind::Msg(format!(
                    "LLM proposal for {} missing constructor '{}'",
                    typ, constr_name
                )))
            })?;

            // Check parameter count: one param per selector, but recursive ADT
            // selectors contribute n_params integers instead of 1
            let mut expected_params = 0;
            for (_sel_name, sel_ty) in sels.iter() {
                let ty = sel_ty.to_type(Some(prms)).unwrap();
                if let Some(enc) = new_encs.get(&ty) {
                    expected_params += enc.n_params;
                } else {
                    expected_params += 1;
                }
            }
            if approx.args.len() != expected_params {
                return Err(Error::from_kind(crate::errors::ErrorKind::Msg(format!(
                    "LLM proposal for {}::{} has {} params, expected {}",
                    typ,
                    constr_name,
                    approx.args.len(),
                    expected_params
                ))));
            }

            // Check result expression count matches n_params
            if approx.terms.len() != new_enc.n_params {
                return Err(Error::from_kind(crate::errors::ErrorKind::Msg(format!(
                    "LLM proposal for {}::{} produces {} expressions, expected {} (n_params)",
                    typ,
                    constr_name,
                    approx.terms.len(),
                    new_enc.n_params
                ))));
            }
        }

        // Check no extra constructors
        for constr_name in new_enc.approxs.keys() {
            if !dt.news.contains_key(constr_name) {
                return Err(Error::from_kind(crate::errors::ErrorKind::Msg(format!(
                    "LLM proposal for {} has unknown constructor '{}'",
                    typ, constr_name
                ))));
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// SMT validation: check if encoders refute the CEX
// ---------------------------------------------------------------------------

fn check_enc_refutes_cex(
    encs: &BTreeMap<Typ, Encoder>,
    cex: &CEX,
    solver: &mut Solver<Parser>,
) -> Res<bool> {
    solver.reset()?;

    // Define datatypes
    dtyp::write_all(solver, "")?;

    // Define encoding functions
    let ctx = EncodeCtx::new(encs);
    let mut funs = Vec::new();
    for enc in encs.values() {
        enc.generate_enc_fun(&ctx, &mut funs)?;
    }
    let funs_strs = funs.into_iter().map(|(funname, ty, term)| {
        let args = vec![("v_0", ty.to_string())];
        let body = term.to_string();
        (funname, args, "Int", body)
    });
    solver.define_funs_rec(funs_strs)?;

    // Assert the CEX under the encoding
    cex.define_assert_with_enc(solver, encs)?;

    // Set timeout
    solver.set_option(":timeout", &format!("{}000", ENC_CHECK_TIMEOUT))?;

    // Check satisfiability: UNSAT means the encoder refutes the CEX
    match solver.check_sat() {
        Ok(false) => Ok(true), // UNSAT = refuted
        Ok(true) => Ok(false), // SAT = not refuted
        Err(e) => {
            let e: Error = e.into();
            if e.is_timeout() {
                Ok(false) // timeout = treat as not refuted
            } else {
                Err(e)
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Main entry point
// ---------------------------------------------------------------------------

pub fn work(
    encs: &mut BTreeMap<Typ, Encoder>,
    cex: &CEX,
    solver: &mut Solver<Parser>,
    profiler: &Profiler,
    instance: &AbsInstance,
) -> Res<()> {
    let provider = match create_provider() {
        Ok(p) => p,
        Err(e) => {
            panic!("LLM provider unavailable: {}", e);
        }
    };
    log_info!("Using {} for LLM-based encoder learning", provider.name());
    let logger = QueryLogger::new();

    let mut conversation = vec![
        Message {
            role: "system".into(),
            content: build_system_prompt(),
        },
        Message {
            role: "user".into(),
            content: format!(
                "{}\n\n{}",
                build_chc_context(instance, encs),
                build_cex_feedback(cex, None)
            ),
        },
    ];

    for attempt in 0..MAX_LLM_ATTEMPTS {
        log_info!("LLM attempt {}/{}", attempt + 1, MAX_LLM_ATTEMPTS);

        // Call LLM
        let response = match provider.request(&conversation) {
            Ok(r) => r,
            Err(e) => {
                log_info!("LLM request failed: {}", e);
                logger.log_error(attempt + 1, &conversation, &e.to_string());
                // Feed error back and retry
                conversation.push(Message {
                    role: "assistant".into(),
                    content: format!("(error: {})", e),
                });
                conversation.push(Message {
                    role: "user".into(),
                    content: "The API call failed. Please try again with a valid response.".into(),
                });
                continue;
            }
        };

        log_debug!("LLM response:\n{}", response);
        logger.log_query(attempt + 1, &conversation, &response);

        // Parse response into encoders (catches panics from parser)
        let new_encs = match parse_llm_response(&response, encs) {
            Ok(e) => e,
            Err(e) => {
                log_info!("Failed to parse LLM response: {}", e);
                conversation.push(Message {
                    role: "assistant".into(),
                    content: response,
                });
                conversation.push(Message {
                    role: "user".into(),
                    content: format!(
                        "Your response could not be parsed: {}. \
Please produce a valid s-expression in the exact format described.",
                        e
                    ),
                });
                continue;
            }
        };

        // Structural validation: check constructor coverage, param counts, etc.
        if let Err(e) = validate_encoder_structure(&new_encs, encs) {
            log_info!("LLM encoder failed structural validation: {}", e);
            conversation.push(Message {
                role: "assistant".into(),
                content: response,
            });
            conversation.push(Message {
                role: "user".into(),
                content: format!(
                    "Your encoder has structural issues: {}. \
Please ensure you provide encoders for ALL required datatypes and constructors \
with the correct number of parameters and result expressions.",
                    e
                ),
            });
            continue;
        }

        log_info!("new_encs (LLM):");
        for (tag, enc) in new_encs.iter() {
            log_info!("  {}: {}", tag, enc);
        }

        // Validate: does it refute the CEX?
        match check_enc_refutes_cex(&new_encs, cex, solver) {
            Ok(true) => {
                log_info!("LLM encoder refutes CEX! Accepting.");
                *encs = new_encs;
                return Ok(());
            }
            Ok(false) => {
                log_info!("LLM encoder does NOT refute CEX, retrying...");
                conversation.push(Message {
                    role: "assistant".into(),
                    content: response.clone(),
                });
                conversation.push(Message {
                    role: "user".into(),
                    content: build_cex_feedback(cex, Some(&response)),
                });
            }
            Err(e) => {
                log_info!("SMT check error: {}", e);
                conversation.push(Message {
                    role: "assistant".into(),
                    content: response,
                });
                conversation.push(Message {
                    role: "user".into(),
                    content: format!(
                        "SMT validation of your encoder failed with error: {}. \
Please try a different encoding.",
                        e
                    ),
                });
            }
        }
    }

    // Exhausted LLM attempts, fall back to template-based learning
    log_info!(
        "LLM learning exhausted {} attempts, falling back to template-based learning",
        MAX_LLM_ATTEMPTS
    );
    super::learn::work(encs, cex, solver, profiler)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_sexp_plain() {
        let input = r#"(("IList"
  (nil () 0)
  (insert (x l) (+ l 1))
))"#;
        let result = extract_sexp(input).unwrap();
        assert!(result.starts_with("(("));
        assert!(result.ends_with("))"));
        assert!(result.contains("IList"));
    }

    #[test]
    fn test_extract_sexp_with_markdown_fences() {
        let input = r#"Here is my proposal:

```smt2
(("IList"
  (nil () 0)
  (insert (x l) (+ l 1))
))
```

This encodes the length of the list."#;
        let result = extract_sexp(input).unwrap();
        assert!(result.starts_with("(("));
        assert!(result.contains("IList"));
        assert!(result.contains("insert"));
    }

    #[test]
    fn test_extract_sexp_with_surrounding_text() {
        let input = r#"I suggest the following encoding:

(("MyList"
  (mynil () 0 0)
  (mycons (x l0 l1) (+ l0 1) (+ l1 x))
))

This encodes both length and sum."#;
        let result = extract_sexp(input).unwrap();
        assert!(result.contains("MyList"));
        assert!(result.contains("mycons"));
    }

    #[test]
    fn test_extract_sexp_none_on_invalid() {
        assert!(extract_sexp("no parens here").is_none());
        assert!(extract_sexp("(single paren)").is_none());
    }

    #[test]
    fn test_strip_markdown_fences() {
        let input = "```smt2\nhello\n```\n";
        let result = strip_markdown_fences(input);
        assert_eq!(result.trim(), "hello");
    }

    #[test]
    fn test_parse_llm_response_catches_panic() {
        // Malformed input that would cause the parser to panic
        // (missing constructor body after name)
        let response = r#"(("BadType" (cons)))"#;
        let encs = BTreeMap::new();
        let result = parse_llm_response(response, &encs);
        // Should be Err, not a panic
        assert!(result.is_err());
    }
}
