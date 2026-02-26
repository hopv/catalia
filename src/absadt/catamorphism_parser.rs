use super::enc::*;
use crate::common::*;
use crate::errors;
use crate::info::VarInfo;

macro_rules! bop_int {
    () => {
        "=" | ">=" | ">" | "<=" | "<" | "+" | "-" | "*"
    };
}

macro_rules! bop_bool {
    () => {
        "or" | "and"
    };
}

/// Parser for a catamorphism from an s-expression string
pub fn parse_catamorphism_str(
    input_string: &str,
) -> Res<BTreeMap<String, (BTreeMap<String, Approx>, usize)>> {
    let mut approximations_per_system = BTreeMap::new();
    if let Ok(tokenized) = lexpr::from_str(input_string) {
        if let Some(datatype) = tokenized.as_cons() {
            for value in datatype.iter() {
                let value = value.car();
                let mut approximations_per_a_datatype = BTreeMap::new();
                let datatype_name = match value.as_cons().unwrap().car() {
                    lexpr::Value::String(name) => Ok(name),
                    _ => Err(Error::from_kind(errors::ErrorKind::Msg(
                        "I was expecting the datatype name".to_string(),
                    ))),
                }?;
				let list_of_approxs_to_parse = value.as_cons().ok_or_else(|| {
					Error::from_kind(errors::ErrorKind::Msg(format!(
						"Failed to convert {} to Cons",
						value
					)))
				})?;
				
				let single_approx_to_parse = list_of_approxs_to_parse.cdr().as_cons().ok_or_else(|| {
					Error::from_kind(errors::ErrorKind::Msg(format!(
						"Failed to convert {} to Cons",
						value
					)))
				})?;
				
				let approxs_to_parse = single_approx_to_parse.to_vec().0;

                for approximation_to_parse in approxs_to_parse.iter() {
                    let (constructor_name, terms, infos) =
                        from_cons_to_encoding_tuple(approximation_to_parse)?;
                    let approximation = Approx { args: infos, terms };
                    approximations_per_a_datatype
                        .insert(constructor_name.to_string(), approximation);
                }
                let mut iter = approximations_per_a_datatype.values();
                let first_len = iter.next().map(|v| v.terms.len()).unwrap_or(0);
                assert!(
                    iter.all(|v| v.terms.len() == first_len),
                    "The approximations have different lenght"
                );
                approximations_per_system.insert(
                    datatype_name.to_string(),
                    (approximations_per_a_datatype, first_len),
                );
            }
        }
        Ok(approximations_per_system)
    } else {
        Err(Error::from_kind(errors::ErrorKind::Msg(
            "Failed to tokenize file".to_string(),
        )))
    }
}

/// Parser for a catamorphism file
pub fn parse_catamorphism(
    catamorphism_file: &str,
) -> Res<BTreeMap<String, (BTreeMap<String, Approx>, usize)>> {
    let input_string: String = std::fs::read_to_string(catamorphism_file)?;
    parse_catamorphism_str(&input_string)
}

/// Once obtained an s-expression describing the encodings for a constructor
/// and its name, unpack it into a tuple (name, functions)
fn from_cons_to_encoding_tuple(input: &lexpr::Value) -> Res<(&str, Vec<Term>, VarInfos)> {
    match input {
        lexpr::Value::Cons(element) => {
            let mut vector_of_terms = Vec::new();
            let constructor_name = element.car().as_str().unwrap();
            let mut infos = VarInfos::new();
            match element.cdr() {
                lexpr::Value::Cons(current_term) => {
                    let function_vec = if let Some(vector) = current_term.car().to_vec() {
                        Ok(vector)
                    } else {
                        Err(Error::from_kind(errors::ErrorKind::Msg(format!(
                            "The constructor for {:?} was malformed",
                            constructor_name
                        ))))
                    }?;

                    assert!(function_vec.len() >= 2);
                    let args_list = &function_vec[0];
                    if let Some(args) = args_list.as_cons() {
                        for arg in args.iter() {
							let var_name = arg.car().as_name();
                            let var_idx = infos.next_index();
                            let info = VarInfo::new(var_name.unwrap(), typ::int(), var_idx);
                            infos.push(info);
                        }
                    }

                    for term in function_vec[1..].iter() {
                        vector_of_terms.push(from_expression_to_term(term, &infos)?);
                    }

                    Ok((constructor_name, vector_of_terms, infos))
                }
                _ => Err(Error::from_kind(errors::ErrorKind::Msg(format!(
                    "There was no `cdr` in the list {:?}",
                    element
                )))),
            }
        }
        _ => Err(Error::from_kind(errors::ErrorKind::Msg(format!(
            "The input should be a list, instead got {:?}",
            input
        )))),
    }
}

fn from_expression_to_term(expression: &lexpr::Value, infos: &VarInfos) -> Res<Term> {
    match expression {
        lexpr::Value::Number(n) => Ok(term::int(n.as_i64().unwrap())),

        lexpr::Value::Bool(b) => Ok(term::bool(*b)),

        lexpr::Value::Cons(_) => parse_list(expression, infos),
        lexpr::Value::Symbol(possible_var) => {
            if let Some(var) = infos.iter().find(|info| *info.name == **possible_var) {
                Ok(term::var(var.idx, typ::int()))
            } else {
                Err(Error::from_kind(errors::ErrorKind::Msg(format!(
                    "Variable {possible_var} has not be declared"
                ))))
            }
        }

        _ => Err(Error::from_kind(errors::ErrorKind::Msg(format!(
            "Expression {expression:?} not recognised"
        )))),
    }
}

fn from_expression_to_boolean_terms(
    expression: &Vec<lexpr::Value>,
    infos: &VarInfos,
) -> Res<Vec<Term>> {
    let mut return_vec = Vec::new();
    for value in expression {
        match value {
            lexpr::Value::Cons(_) => return_vec.push(parse_list(value, infos)?),

            _ => Err(Error::from_kind(errors::ErrorKind::Msg(format!(
                "Expression {expression:?} not recognised"
            ))))?,
        }
    }
    Ok(return_vec)
}

fn remove_operator_connector(expr: &lexpr::Value, function_name: &str) -> Res<Vec<lexpr::Value>> {
    // expr has the shape Cons(...)

    let tail = match expr {
        lexpr::Value::Cons(idk) => Ok(idk),

        _ => Err(Error::from_kind(errors::ErrorKind::Msg(format!(
            "{expr:?} is not a cons"
        )))),
    }?;

    let mut list = Vec::new();

    for elem in tail.iter() {
        list.push(elem.car().clone());
    }

    let list_len = list.len();

    match function_name {
        "ite" if list_len != 3 => {
            Err(Error::from_kind(errors::ErrorKind::Msg(format!(
            "The binary operator {function_name} should have 3 operands, it now has {} elementa i.e. {list:?}", list_len
        ))))
        }
        "=" | ">=" | ">" | "<=" | "<" | "+" | "-" | "*" if list_len != 2 => {
            Err(Error::from_kind(errors::ErrorKind::Msg(format!(
                "The binary operator {function_name} should have 2 operands it now has {} elementa i.e. {list:?}", list_len
            ))))
        }
		"not" if list_len != 1 => {
            Err(Error::from_kind(errors::ErrorKind::Msg(format!(
                "The binary operator not should have 3 operands it now has {} elementa i.e. {list:?}", list_len
            ))))
        }
        _ => Ok(()),
    }?;

    Ok(list)
}

fn parse_list(expr: &lexpr::Value, infos: &VarInfos) -> Res<Term> {
    let expression_exploded = if let Some(inner_list) = expr.as_cons() {
        Ok(inner_list)
    } else {
        Err(Error::from_kind(errors::ErrorKind::Msg(
            "un-able to convert to cons".to_string(),
        )))
    }?;

    // first element determines structure
    match expression_exploded.car() {
        lexpr::Value::Number(num) => Ok(term::int(num.as_i64().unwrap())),
        lexpr::Value::Symbol(s) => {
            match &**s {
                "not" => {
                    let list = remove_operator_connector(expression_exploded.cdr(), "not")?;
                    let term_to_negate = from_expression_to_term(&list[0], infos)?;
                    assert_eq!(term_to_negate.typ(), term::typ::bool());
                    Ok(term::not(term_to_negate))
                }
                "ite" => {
                    let list = remove_operator_connector(expression_exploded.cdr(), "ite")?;
                    let cond = from_expression_to_term(&list[0], infos)?;
                    let true_branch = from_expression_to_term(&list[1], infos)?;
                    let false_branch = from_expression_to_term(&list[2], infos)?;
                    assert_eq!(true_branch.typ(), false_branch.typ());
                    Ok(term::ite(cond, true_branch, false_branch))
                }
                bop_int!() => {
                    let list = remove_operator_connector(expression_exploded.cdr(), s)?;
                    let x = from_expression_to_term(&list[0], infos)?;
                    let y = from_expression_to_term(&list[1], infos)?;
                    assert_eq!(x.typ(), term::typ::int());
                    assert_eq!(y.typ(), term::typ::int());
                    match &**s {
                        "=" => Ok(term::eq(x, y)),
                        ">=" => Ok(term::ge(x, y)),
                        ">" => Ok(term::gt(x, y)),
                        "<=" => Ok(term::le(x, y)),
                        "<" => Ok(term::lt(x, y)),
                        "+" => Ok(term::add2(x, y)),
                        "-" => Ok(term::sub2(x, y)),
                        "*" => Ok(term::mul(vec![x, y])),
                        _ => Err(Error::from_kind(errors::ErrorKind::Msg(format!(
                            "Symbol {s} not recognised"
                        )))),
                    }
                }
                bop_bool!() => {
                    let list = remove_operator_connector(expression_exploded.cdr(), s)?;
                    let terms = from_expression_to_boolean_terms(&list, infos)?;
                    for term in &terms {
                        assert_eq!(term.typ(), term::typ::bool());
                    }
                    match &**s {
                        "and" => Ok(term::and(terms)),
                        "or" => Ok(term::or(terms)),
                        _ => Err(Error::from_kind(errors::ErrorKind::Msg(format!(
                            "Symbol {s} not recognised"
                        )))),
                    }
                }
                _ => Err(Error::from_kind(errors::ErrorKind::Msg(
                    "Unknown symbol".to_string(),
                ))),
            }
        }

        _ => Err(Error::from_kind(errors::ErrorKind::Msg(
            "The symbol should either an ite expression or a binary operator over integers"
                .to_string(),
        ))),
    }
}

pub fn build_encoding_from_approx(
    approxs: BTreeMap<String, (BTreeMap<String, Approx>, usize)>,
    encs: &BTreeMap<Typ, Encoder>,
) -> Res<BTreeMap<Typ, Encoder>> {
    let mut return_encs = BTreeMap::new();
    for (typ, _) in encs.iter() {
        match typ.get() {
            crate::term::typ::RTyp::DTyp { dtyp, .. } => {
                let (new_approxs, approximation_degree) =
                    if let Some((approxs, lenght)) = approxs.get(&dtyp.name) {
                        Ok((approxs, lenght))
                    } else {
                        Err(Error::from_kind(errors::ErrorKind::Msg(format!(
                            "You did not supply an approximation for type {}",
                            dtyp.name
                        ))))
                    }?;
                let enc = Enc {
                    approxs: new_approxs.clone(),
                    typ: typ.clone(),
                    n_params: *approximation_degree,
                };
                return_encs.insert(typ.clone(), enc);
            }
            _ => Err(Error::from_kind(errors::ErrorKind::Msg(
                "The ancoding keys should be datatype, I have found something else".to_string(),
            )))?,
        }
    }
    Ok(return_encs)
}
