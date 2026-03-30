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
    dir: Option<PathBuf>,
}

impl QueryLogger {
    fn new(dir: Option<PathBuf>) -> Self {
        if let Some(ref d) = dir {
            if let Err(e) = std::fs::create_dir_all(d) {
                log_info!("Warning: failed to create LLM log dir {:?}: {}", d, e);
            } else {
                log_info!("LLM query logs: {}", d.display());
            }
        }
        Self { dir }
    }

    fn log_query(&self, attempt: usize, messages: &[Message], response: &str) {
        let dir = match self.dir {
            Some(ref d) => d,
            None => return,
        };
        let input_path = dir.join(format!("attempt-{}-input.txt", attempt));
        if let Ok(mut f) = std::fs::File::create(&input_path) {
            for msg in messages {
                let _ = writeln!(f, "=== {} ===", msg.role);
                let _ = writeln!(f, "{}", msg.content);
                let _ = writeln!(f);
            }
        }
        let output_path = dir.join(format!("attempt-{}-output.txt", attempt));
        if let Ok(mut f) = std::fs::File::create(&output_path) {
            let _ = write!(f, "{}", response);
        }
    }

    fn log_error(&self, attempt: usize, messages: &[Message], error: &str) {
        let dir = match self.dir {
            Some(ref d) => d,
            None => return,
        };
        let input_path = dir.join(format!("attempt-{}-input.txt", attempt));
        if let Ok(mut f) = std::fs::File::create(&input_path) {
            for msg in messages {
                let _ = writeln!(f, "=== {} ===", msg.role);
                let _ = writeln!(f, "{}", msg.content);
                let _ = writeln!(f);
            }
        }
        let error_path = dir.join(format!("attempt-{}-error.txt", attempt));
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
        body["max_output_tokens"] = serde_json::Value::Number(16384.into());

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
            "max_tokens": 16384,
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
    r#"You are solving a **Constrained Horn Clause (CHC)** problem over **algebraic data types (ADTs)** and integer arithmetic. I want a **catamorphism-based solution** in the spirit of Katsura et al., *Automated Catamorphism Synthesis for Solving Constrained Horn Clauses over Algebraic Data Types*.

Your task is to analyze the given SMT-LIB HORN instance and do the following.

## What to produce

1. Decide whether the CHCs are **SAT** or **UNSAT**.
2. If **SAT**, produce:
   - an **intuitive / intended model** for the predicates if possible,
   - a suitable **catamorphism** from each relevant ADT to integers or tuples of integers,
   - the corresponding **range / admissibility predicate** for the image of the catamorphism,
   - an **abstract integer-domain model** for the predicates after applying the catamorphism,
   - the induced **original ADT-domain model** obtained by lifting back through the catamorphism.
3. If **UNSAT**, explain the contradiction in the **original CHCs**, not only in the abstraction.

---

## High-level overview of the paper's approach / pipeline

The core problem is that CHCs over ADTs often require models that are naturally stated using inductive functions such as list length, list sum, alternating sum, or numeric value of Peano naturals. Standard CHC solvers are often much better at solving CHCs over **integers** than over ADTs directly.

The paper's key idea is therefore:

1. **Choose a catamorphism** `C` from the ADT to integers or tuples of integers.
   - A catamorphism is a fold-like summary map defined by one structure map per constructor.
   - Example patterns:
     - `Nat`: `Z -> 0`, `S(x) -> x + 1`
     - `List`: `nil -> 0`, `cons(x,l) -> 1 + l` (length)
     - `List`: `nil -> 0`, `cons(x,l) -> x + l` (sum)
     - `List`: `nil -> 0`, `cons(x,l) -> x - l` (alternating sum)
     - tuple-valued folds when one scalar is insufficient.

2. **Augment the original CHCs with an admissibility predicate** `P_delta` for each ADT sort.
   - This predicate represents "being in the image / being a valid abstractable value".
   - This matters because abstraction without range restrictions is often too coarse and can introduce spurious counterexamples.
   - In the abstract system, every universally quantified ADT variable is replaced by an integer variable together with a condition such as `P_delta(x)`.

3. **Abstract the CHCs into integer CHCs** by replacing each constructor application with the corresponding structure map of the catamorphism.
   - ADT equality is abstracted soundly by equality of catamorphism images.
   - The result is a CHC system over integer arithmetic, often much easier to solve.

4. **Solve the abstract CHCs**.
   - If the abstract system is SAT, then by soundness the original CHCs are SAT.
   - A model for the original predicates can be obtained by composing the abstract model with the catamorphism.

5. **If the abstract system is UNSAT**, check whether the UNSAT proof corresponds to a real contradiction in the original CHCs.
   - Extract a candidate counterexample / proof obligation from the abstract UNSAT derivation.
   - If that counterexample is genuinely satisfiable in the original ADT world, conclude **UNSAT**.
   - Otherwise it is **spurious**, meaning the current catamorphism was too weak.

6. **Refine the catamorphism**.
   - Search for a better catamorphism using templates, usually linear or affine folds first.
   - The paper uses a **counterexample-guided template synthesis** loop:
     - abstract,
     - solve,
     - extract spurious counterexample if needed,
     - strengthen the catamorphism so the same spurious proof becomes impossible,
     - repeat.

7. **Prefer simple catamorphisms first**, then richer tuple-valued ones if needed.
   - The paper uses a sequence of templates of increasing expressiveness.
   - In practice, many examples are solved by a small scalar or 2D/3D fold.

In short, the pipeline is:

**guess / synthesize fold -> add range predicate -> abstract to integer CHCs -> solve -> if spurious UNSAT, refine fold -> otherwise lift model back**.

---

## Key ideas you should actively use while solving

Follow the methodology below, not just generic CHC reasoning.

### A. First infer the semantic role of each predicate

Try to understand what each predicate is tracking:
- arithmetic relation between arguments,
- structural size,
- length of a list,
- sum of elements,
- alternating sum,
- parity,
- relation between two accumulators,
- generated family of ADT values,
- safety property in the final `false` clause.

Many CHC predicates correspond to a fold-derived invariant.

### B. Prefer simple folds first

Start with simple, interpretable catamorphisms:
- natural numbers -> numeric value / size,
- lists -> length,
- lists -> sum,
- lists -> alternating sum,
- tuples such as `(length, sum)`, `(sum_even_minus_odd, length)`, etc.

If one scalar summary is not enough, try a **tuple-valued catamorphism**.

### C. Use linear / affine templates first

A very common successful pattern is a linear catamorphism:
- `C(nil) = d`
- `C(cons(x,l)) = a*C(l) + b*x + c`

or tuple combinations of these.

For naturals:
- `C(Z) = a`
- `C(S(n)) = b*C(n) + c`

Try low-complexity coefficients first.

### D. Always think about the range predicate

Do **not** forget the image restriction / admissibility predicate.

Without it, the abstraction may be too coarse and may yield false contradictions or incorrect arithmetic states that no concrete ADT term can realize.

When the image is all integers, the range predicate may simplify to `true`; when the image is restricted, spell that out explicitly.

### E. Clause-by-clause validation matters

Once you propose a catamorphism and abstract model, check **every Horn clause** carefully.

For SAT cases, verify that each abstract clause is satisfied by your abstract predicate definitions.

For UNSAT cases, identify the concrete contradiction in the original clauses.

### F. Lift the abstract model back explicitly

If the abstract model defines e.g.
- `P_abs(u,v,w) := u + v = w`

and the ADT arguments are abstracted by `C`, then the original model should be written as
- `P(x,y,z) := P_abs(C(x), C(y), C(z))`

or equivalently with `C(x), C(y), ...` substituted directly.

---

## Heuristics that often work on these tasks

Use these aggressively.

- For Peano naturals, the right catamorphism is often simply the numeric value / size.
- For list-processing CHCs, the hidden invariant is often one of:
  - length,
  - sum,
  - alternating sum,
  - parity,
  - a pair/triple of such measures.
- Generator predicates often characterize a family of ADTs with a very simple abstract image.
- Safety clauses often directly reveal the needed invariant:
  - `false <- ...` frequently says exactly what arithmetic relation must hold.
- Recurrences like
  - `P(cons(x,l), x+n, m) <- P(l, m, n)`
  often suggest alternating-sum or accumulator-swap structure.
- If the abstraction becomes UNSAT too early, suspect that the catamorphism is too weak rather than the original problem being UNSAT.
- Equality on ADTs becomes equality of summaries only as a **sound abstraction**; do not silently treat it as full equivalence.

---

## Important requirement: output the catamorphism in Catalia-readable format

When you present the catamorphism, you MUST wrap it between the markers `<<START-CATA>>` and `<<END-CATA>>`.

The catamorphism must be a valid s-expression in the following format:

- The whole catamorphism is a list of ADT-sort entries.
- Each ADT-sort entry has the form:
  - `( "SortName" ...constructor-entries... )`
- Each constructor entry has the form:
  - `( "CtorName" ( (arg1 arg2 ...) body1 body2 ... ) )`
- The argument list contains:
  - first, ordinary non-recursive constructor arguments (one parameter per Int selector),
  - then, for recursive ADT arguments, the already-catamorphically-mapped components (N parameters per recursive selector, where N is the encoding dimension of that ADT).
- A scalar catamorphism returns one body expression.
- A tuple-valued catamorphism returns multiple body expressions, one per component.
- Parameters appear in the SAME ORDER as selector declarations.
- Constructors with no selectors MUST use an empty parameter list: `()`
- All result expressions MUST be integer-valued SMT-LIB expressions.
- Use ONLY: `(+ a b)`, `(- a b)`, `(* a b)`, `(ite cond then else)`, `(= a b)`, `(>= a b)`, `(> a b)`, `(<= a b)`, `(< a b)`, `(and ...)`, `(or ...)`, `(not ...)`.
- Do NOT use division, quantifiers, let bindings, or uninterpreted functions.
- You may include `;; ...` comments inside the block for clarity.

### Catamorphism example 1

<<START-CATA>>
(
  ;; Bool_265 |-> (0/1)
  ( "Bool_265"
    ( "false_265"
      ( ()
        0
      )
    )
    ( "true_265"
      ( ()
        1
      )
    )
  )

  ;; list_194 |-> (ok, first, emp)
  ( "list_194"
    ( "cons_194"
      ( (x ok first emp)
        (* ok (ite (= emp 1) 1 (ite (<= x first) 1 0)))
        x
        0
      )
    )
    ( "nil_220"
      ( ()
        1
        0
        1
      )
    )
  )

  ;; pair_82 |-> (b, ok, first, emp)
  ( "pair_82"
    ( "pair_83"
      ( (b ok first emp)
        b
        ok
        first
        emp
      )
    )
  )
)
<<END-CATA>>

### Catamorphism example 2

<<START-CATA>>
(
  ( "Nat_0"
    ( "S_0"
      ( (x)
        (+ x 1)
      )
    )
    ( "Z_0"
      ( ()
        0
      )
    )
  )

  ;; list_0 |-> int (length)
  ( "list_0"
    ( "cons_0"
      ( (x y)
        (+ y 1)
      )
    )
    ( "nil_0"
      ( ()
        0
      )
    )
  )
)
<<END-CATA>>

You MUST include EVERY datatype and EVERY constructor listed in the Required Datatypes section.
All constructors of the SAME datatype MUST produce the SAME number of result expressions.
The catamorphism block between the markers is the ONLY part that will be parsed by the tool.
You are free to explain your reasoning, analysis, and model outside of the markers.

---

## Required output format

Use exactly this structure.

### 1. Verdict
State `SAT` or `UNSAT`.

### 2. High-level idea
Briefly explain the invariant and why a catamorphism is appropriate.

### 3. Chosen catamorphism
Define the catamorphism precisely for each constructor.
Include the **Catalia-style catamorphism block** wrapped in `<<START-CATA>>` / `<<END-CATA>>` markers.
If tuple-valued, clearly name each component.

### 4. Range / admissibility predicate
Define the image predicate `P_delta`.
If it simplifies to `true`, say so and justify briefly.

### 5. Abstract model
Give explicit definitions of the predicates in the abstract integer domain.

### 6. Clause check
Check each Horn clause against the abstract model.

### 7. Lifted original model
Translate the abstract model back to the original ADT domain via the catamorphism.

### 8. If UNSAT
If the verdict is `UNSAT`, explain the contradiction in the original CHCs.

---

## Additional instructions

- Be mathematically explicit.
- Do not give only intuition; give actual formulas.
- If one catamorphism fails, refine it rather than giving up.
- If the intended model is recursive but the non-recursive one is easier to verify, provide both.
- Prefer concise but rigorous reasoning.
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
The current encoders are insufficient and produce spurious counterexamples. \
Analyze the CHC problem and propose a catamorphism that captures the essential invariant.",
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

const CATA_START_MARKER: &str = "<<START-CATA>>";
const CATA_END_MARKER: &str = "<<END-CATA>>";

/// Extract the catamorphism s-expression from an LLM response.
///
/// First looks for `<<START-CATA>>` / `<<END-CATA>>` markers. If found, extracts the
/// content between them and finds the outermost balanced s-expression within.
/// Falls back to the legacy behaviour of finding the first balanced s-expression
/// in the full response (after stripping markdown fences).
fn extract_sexp(response: &str) -> Option<String> {
    // Try marker-based extraction first
    if let Some(sexp) = extract_sexp_from_markers(response) {
        return Some(sexp);
    }

    // Fallback: strip markdown fences and find first balanced s-expression
    let text = strip_markdown_fences(response);
    extract_first_balanced_sexp(&text)
}

/// Extract catamorphism from between <<START-CATA>> and <<END-CATA>> markers.
fn extract_sexp_from_markers(response: &str) -> Option<String> {
    let start_idx = response.find(CATA_START_MARKER)?;
    let after_start = start_idx + CATA_START_MARKER.len();
    let end_idx = response[after_start..].find(CATA_END_MARKER)?;
    let between = &response[after_start..after_start + end_idx];

    // Strip comments (lines starting with ;;) are fine for lexpr, but strip
    // markdown fences that might appear inside the marker block
    let cleaned = strip_markdown_fences(between);
    extract_first_balanced_sexp(&cleaned)
}

/// Find the first balanced parenthesized s-expression in the given text.
fn extract_first_balanced_sexp(text: &str) -> Option<String> {
    let bytes = text.as_bytes();

    // find first '('
    let start = bytes.iter().position(|&b| b == b'(')?;

    let mut depth = 0i32;
    let mut in_string = false;
    let mut escape_next = false;
    let mut in_comment = false;
    for (i, &b) in bytes[start..].iter().enumerate() {
        if escape_next {
            escape_next = false;
            continue;
        }
        if in_comment {
            if b == b'\n' {
                in_comment = false;
            }
            continue;
        }
        if in_string {
            match b {
                b'\\' => escape_next = true,
                b'"' => in_string = false,
                _ => {}
            }
            continue;
        }
        match b {
            b';' => in_comment = true,
            b'"' => in_string = true,
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

    // TODO: fix this, by returning a Result from the parser instead of panicking on errors
    // The catamorphism parser has unwrap!/assert! paths that can panic on
    // malformed input. Since LLM output is untrusted, catch panics and
    // convert them to Err so the retry loop can continue.
    let sexp_clone = sexp.clone();
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
    log_dir: Option<PathBuf>,
) -> Res<()> {
    let provider = match create_provider() {
        Ok(p) => p,
        Err(e) => {
            panic!("LLM provider unavailable: {}", e);
        }
    };
    log_info!("Using {} for LLM-based encoder learning", provider.name());
    let logger = QueryLogger::new(log_dir);

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
Please ensure the catamorphism s-expression is wrapped between <<START-CATA>> and <<END-CATA>> markers \
in the exact format described.",
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

    // ---------------------------------------------------------------------------
    // Helpers for correct-case tests
    // ---------------------------------------------------------------------------

    use crate::absadt::enc::{Approx, Enc};

    /// Build a minimal initial encoder map for `List<Int>` with n_params=1.
    /// The actual approx bodies don't matter here; only the Typ key is used by
    /// `build_encoding_from_approx` to look up the datatype name.
    fn make_list_encs() -> BTreeMap<Typ, Encoder> {
        dtyp::create_list_dtyp();
        let list_typ = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());
        let mut approxs = BTreeMap::new();
        approxs.insert("nil".to_string(), Approx::len_nil());
        approxs.insert("insert".to_string(), Approx::len_cons());
        let enc = Enc {
            typ: list_typ.clone(),
            n_params: 1,
            approxs,
        };
        let mut encs = BTreeMap::new();
        encs.insert(list_typ, enc);
        encs
    }

    // ---------------------------------------------------------------------------
    // Correct-case tests
    // ---------------------------------------------------------------------------

    #[test]
    fn test_parse_llm_response_valid_length_encoding() {
        // 1-param length encoding for List<Int>.
        // "insert" has head:Int (1 param) + tail:List (1 recursive param) = 2 params.
        let response = r#"(
  ("List"
    ("nil"
      (() 0)
    )
    ("insert"
      ((head tail) (+ tail 1))
    )
  )
)"#;
        let encs = make_list_encs();
        let result = parse_llm_response(response, &encs);
        assert!(result.is_ok(), "expected Ok, got {:?}", result);
        let new_encs = result.unwrap();
        assert_eq!(new_encs.len(), 1);
        let enc = new_encs.values().next().unwrap();
        assert_eq!(enc.n_params, 1);
        assert!(enc.approxs.contains_key("nil"));
        assert!(enc.approxs.contains_key("insert"));
    }

    #[test]
    fn test_parse_llm_response_valid_two_param_encoding() {
        // 2-param (length + sum) encoding for List<Int>.
        // "insert": head:Int (1) + tail:List (2 recursive) = 3 params total.
        let response = r#"(
  ("List"
    ("nil"
      (() 0 0)
    )
    ("insert"
      ((head t0 t1)
        (+ t0 1)
        (+ t1 head)
      )
    )
  )
)"#;
        let encs = make_list_encs();
        let result = parse_llm_response(response, &encs);
        assert!(result.is_ok(), "expected Ok, got {:?}", result);
        let new_encs = result.unwrap();
        let enc = new_encs.values().next().unwrap();
        assert_eq!(enc.n_params, 2);
        // nil produces (0, 0), insert produces (t0+1, t1+head)
        assert_eq!(enc.approxs["nil"].terms.len(), 2);
        assert_eq!(enc.approxs["insert"].terms.len(), 2);
    }

    #[test]
    fn test_parse_llm_response_valid_in_markdown_fences() {
        // Same length encoding but wrapped in markdown, as an LLM would actually respond.
        let response = r#"Here is the encoding:

```smt2
(
  ("List"
    ("nil"
      (() 0)
    )
    ("insert"
      ((head tail) (+ tail 1))
    )
  )
)
```

This encodes the length of the list."#;
        let encs = make_list_encs();
        let result = parse_llm_response(response, &encs);
        assert!(result.is_ok(), "expected Ok, got {:?}", result);
        let enc = result.unwrap().into_values().next().unwrap();
        assert_eq!(enc.n_params, 1);
    }

    #[test]
    fn test_parse_llm_response_valid_with_ite() {
        // Encoding that uses ite, a common LLM pattern.
        // Encodes max(head, max_of_tail).
        let response = r#"(
  ("List"
    ("nil"
      (() 0)
    )
    ("insert"
      ((head tail) (ite (>= head tail) head tail))
    )
  )
)"#;
        let encs = make_list_encs();
        let result = parse_llm_response(response, &encs);
        assert!(result.is_ok(), "expected Ok, got {:?}", result);
    }

    #[test]
    fn test_parse_llm_response_wrong_datatype_name() {
        // Response uses a datatype name not present in encs → error from build_encoding_from_approx.
        let response = r#"(
  ("WrongName"
    ("nil"
      (() 0)
    )
    ("insert"
      ((head tail) (+ tail 1))
    )
  )
)"#;
        let encs = make_list_encs();
        let result = parse_llm_response(response, &encs);
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_llm_response_no_sexp() {
        let encs = make_list_encs();
        let result = parse_llm_response("sorry, I cannot help with that", &encs);
        assert!(result.is_err());
    }

    // ---------------------------------------------------------------------------
    // Marker-based extraction tests
    // ---------------------------------------------------------------------------

    #[test]
    fn test_extract_sexp_with_markers() {
        let input = r#"### 1. Verdict
SAT

### 3. Chosen catamorphism
The list length is sufficient.

<<START-CATA>>
(("IList"
  ("nil" (() 0))
  ("insert" ((x l) (+ l 1)))
))
<<END-CATA>>

### 5. Abstract model
P(l) := l >= 0
"#;
        let result = extract_sexp(input).unwrap();
        assert!(result.contains("IList"));
        assert!(result.contains("insert"));
        // Should NOT grab the surrounding text
        assert!(!result.contains("Verdict"));
    }

    #[test]
    fn test_extract_sexp_markers_with_comments() {
        let input = r#"Some reasoning here.

<<START-CATA>>
(
  ;; list_0 |-> int (length)
  ( "List"
    ( "nil"
      ( ()
        0
      )
    )
    ( "insert"
      ( (x t)
        (+ t 1)
      )
    )
  )
)
<<END-CATA>>

More text here."#;
        let result = extract_sexp(input).unwrap();
        assert!(result.contains("List"));
        assert!(result.contains("insert"));
    }

    #[test]
    fn test_extract_sexp_markers_with_markdown_inside() {
        let input = r#"<<START-CATA>>
```lisp
(("List"
  ("nil" (() 0))
  ("insert" ((x l) (+ l 1)))
))
```
<<END-CATA>>"#;
        let result = extract_sexp(input).unwrap();
        assert!(result.contains("List"));
    }

    #[test]
    fn test_extract_sexp_prefers_markers_over_earlier_sexp() {
        // There's an s-expression before the markers (in the reasoning),
        // but we should extract from the markers.
        let input = r#"The predicate P(x) := (>= x 0) is a candidate.

<<START-CATA>>
(("List"
  ("nil" (() 0))
  ("insert" ((x l) (+ l 1)))
))
<<END-CATA>>"#;
        let result = extract_sexp(input).unwrap();
        // Should get the List encoding, not (>= x 0)
        assert!(result.contains("List"));
    }

    #[test]
    fn test_parse_llm_response_with_markers() {
        let response = r#"### 1. Verdict
SAT

### 3. Chosen catamorphism

<<START-CATA>>
(
  ("List"
    ("nil"
      (() 0)
    )
    ("insert"
      ((head tail) (+ tail 1))
    )
  )
)
<<END-CATA>>

### 5. Abstract model
..."#;
        let encs = make_list_encs();
        let result = parse_llm_response(response, &encs);
        assert!(result.is_ok(), "expected Ok, got {:?}", result);
        let enc = result.unwrap().into_values().next().unwrap();
        assert_eq!(enc.n_params, 1);
    }
}
