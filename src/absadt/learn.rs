use super::chc::CEX;
use super::enc::*;
use crate::common::{smt::FullParser as Parser, Cex as Model, *};
use crate::info::VarInfo;

const CONSTRAINT_CHECK_TIMEOUT: usize = 1;
const THRESHOLD_BLASTING: usize = 10;
const THRESHOLD_BLASTING_MAX_RANGE: i64 = 3;

struct TemplateInfo {
    parameters: VarInfos,
    encs: BTreeMap<Typ, Enc<Template>>,
}

impl TemplateInfo {
    fn define_constraints(&self, solver: &mut Solver<Parser>) -> Res<()> {
        let constrs = if let Some(constrs) = self.constraint() {
            constrs
        } else {
            return Ok(());
        };

        writeln!(solver, "; Constraints on template variables")?;
        for c in constrs {
            writeln!(solver, "(assert {})", c)?;
        }
        writeln!(solver)?;

        Ok(())
    }
    /// Define paramter constants
    fn define_parameters(&self, solver: &mut Solver<Parser>) -> Res<()> {
        for var in self.parameters.iter() {
            solver.declare_const(&format!("v_{}", var.idx), &var.typ.to_string())?;
        }
        Ok(())
    }

    fn new_linear_approx(
        encs: &BTreeMap<Typ, Encoder>,
        n_encs: usize,
        min: Option<i64>,
        max: Option<i64>,
        structured: bool,
    ) -> TemplateInfo {
        let mut variables = VarInfos::new();
        let mut new_encs = BTreeMap::new();

        // prepare LinearApprox for each constructor
        for typ in encs.keys() {
            let mut approxs = BTreeMap::new();
            for constr in typ.dtyp_inspect().unwrap().0.news.keys() {
                // for each constructor, we prepare an approx
                let (ty, prms) = typ.dtyp_inspect().unwrap();
                // prepare function arguments
                let mut approx_args = VarInfos::new();
                let mut arg_components: Vec<Option<usize>> = Vec::new();
                for (sel, ty) in ty.selectors_of(constr).unwrap().iter() {
                    let ty = ty.to_type(Some(prms)).unwrap();
                    let is_recursive = encs.get(&ty).is_some();
                    let n_arg = if is_recursive { n_encs } else { 1 };
                    if !is_recursive {
                        assert!(ty.is_int());
                    }
                    for i in 0..n_arg {
                        let next_index = variables.next_index();
                        let info = VarInfo::new(
                            format!("arg-{}-{}", sel, i),
                            typ::int(),
                            next_index,
                        );
                        variables.push(info.clone());
                        approx_args.push(info);
                        if is_recursive {
                            arg_components.push(Some(i));
                        } else {
                            arg_components.push(None);
                        }
                    }
                }
                // create a LinearApprox
                approxs.insert(
                    constr.to_string(),
                    Template::Linear(LinearApprox::new(
                        approx_args,
                        n_encs,
                        &mut variables,
                        min,
                        max,
                        arg_components,
                        structured,
                    )),
                );
            }
            let enc = Enc {
                approxs,
                typ: typ.clone(),
                n_params: n_encs,
            };
            new_encs.insert(typ.clone(), enc);
        }

        TemplateInfo {
            parameters: variables,
            encs: new_encs,
        }
    }

    fn instantiate(&self, model: &Model) -> BTreeMap<Typ, Encoder> {
        self.encs
            .iter()
            .map(|(k, v)| (k.clone(), v.instantiate(&model)))
            .collect()
    }

    fn constraint(&self) -> Option<Vec<Term>> {
        let mut asserts = Vec::new();
        for enc in self.encs.values() {
            for approx in enc.approxs.values() {
                if let Some(constr) = approx.constraint() {
                    asserts.push(constr);
                }
            }
        }
        Some(asserts)
    }

    fn param_range(&self) -> Option<(i64, i64)> {
        let mut overall_min = i64::MAX;
        let mut overall_max = i64::MIN;
        for enc in self.encs.values() {
            for approx in enc.approxs.values() {
                let (min, max) = approx.param_range()?;
                if min < overall_min {
                    overall_min = min;
                }
                if max > overall_max {
                    overall_max = max;
                }
            }
        }
        assert!(overall_min <= overall_max);
        Some((overall_min, overall_max))
    }
}

/// Controls
///   1. which Template to use
///     - including their parameters
///   2. which range of the existing approximations to use
struct TemplateScheduler {
    idx: usize,
    enc: BTreeMap<Typ, Encoder>,
}

#[derive(Clone, Copy)]
enum TemplateType {
    BoundStructuredLinear { min: i64, max: i64 },
    BoundLinear { min: i64, max: i64 },
    Linear,
}

impl std::fmt::Display for TemplateType {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            TemplateType::BoundStructuredLinear { min, max } => {
                write!(f, "BoundStructuredLinear({}, {})", min, max)
            }
            TemplateType::BoundLinear { min, max } => write!(f, "BoundLinear({}, {})", min, max),
            TemplateType::Linear => write!(f, "Linear"),
        }
    }
}

#[derive(Clone, Copy)]
struct TemplateSchedItem {
    n_encs: usize,
    typ: TemplateType,
}

impl std::fmt::Display for TemplateSchedItem {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} (n_encs = {})", self.typ, self.n_encs)
    }
}

impl TemplateScheduler {
    const N_TEMPLATES: usize = 10;

    const TEMPLATE_SCHEDULING: [TemplateSchedItem; Self::N_TEMPLATES] = [
        TemplateSchedItem {
            n_encs: 1,
            typ: TemplateType::BoundLinear { min: -1, max: 1 },
        },
        TemplateSchedItem {
            n_encs: 2,
            typ: TemplateType::BoundStructuredLinear { min: -1, max: 1 },
        },
        TemplateSchedItem {
            n_encs: 2,
            typ: TemplateType::BoundLinear { min: -1, max: 1 },
        },
        TemplateSchedItem {
            n_encs: 3,
            typ: TemplateType::BoundStructuredLinear { min: -1, max: 1 },
        },
        TemplateSchedItem {
            n_encs: 3,
            typ: TemplateType::BoundLinear { min: -1, max: 1 },
        },
        TemplateSchedItem {
            n_encs: 3,
            typ: TemplateType::BoundLinear { min: -2, max: 2 },
        },
        TemplateSchedItem {
            n_encs: 3,
            typ: TemplateType::BoundLinear { min: -4, max: 4 },
        },
        TemplateSchedItem {
            n_encs: 3,
            typ: TemplateType::BoundLinear { min: -32, max: 32 },
        },
        TemplateSchedItem {
            n_encs: 3,
            typ: TemplateType::BoundLinear { min: -64, max: 64 },
        },
        TemplateSchedItem {
            n_encs: 3,
            typ: TemplateType::Linear,
        },
    ];

    fn new(enc: BTreeMap<Typ, Encoder>) -> Self {
        Self { idx: 0, enc }
    }
}

impl std::iter::Iterator for TemplateScheduler {
    type Item = TemplateInfo;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.idx >= Self::N_TEMPLATES {
                return None;
            }
            let next_template = &Self::TEMPLATE_SCHEDULING[self.idx];
            self.idx += 1;

            let r = match next_template.typ {
                TemplateType::BoundStructuredLinear { min, max } => TemplateInfo::new_linear_approx(
                    &self.enc,
                    next_template.n_encs,
                    Some(min),
                    Some(max),
                    true,
                ),
                TemplateType::BoundLinear { min, max } => {
                    TemplateInfo::new_linear_approx(
                        &self.enc,
                        next_template.n_encs,
                        Some(min),
                        Some(max),
                        false,
                    )
                }
                TemplateType::Linear => {
                    TemplateInfo::new_linear_approx(&self.enc, next_template.n_encs, None, None, false)
                }
            };
            log_info!("Template: {}", next_template);
            break Some(r);
        }
    }
}

pub struct LearnCtx<'a> {
    original_encs: &'a mut BTreeMap<Typ, Encoder>,
    cex: &'a CEX,
    solver: &'a mut Solver<Parser>,
    profiler: &'a Profiler,
    models: Vec<Model>,
}

enum Template {
    Linear(LinearApprox),
}

impl Approximation for Template {
    fn apply(&self, arg_terms: &[Term]) -> Vec<Term> {
        match self {
            Template::Linear(approx) => approx.apply(arg_terms),
        }
    }
}

impl Template {
    fn instantiate(&self, model: &Model) -> Approx {
        match self {
            Template::Linear(approx) => approx.instantiate(model),
        }
    }
    fn constraint(&self) -> Option<Term> {
        match self {
            Template::Linear(approx) => approx.constraint(),
        }
    }
    fn param_range(&self) -> Option<(i64, i64)> {
        match self {
            Template::Linear(approx) => {
                if let (Some(min), Some(max)) = (approx.min, approx.max) {
                    Some((min, max))
                } else {
                    None
                }
            }
        }
    }
}

struct LinearApprox {
    /// Existing approx
    approx: Approx,
    // approx template: one coefficient vector per encoded component
    coef: Vec<VarMap<Option<VarIdx>>>,
    cnst: VarMap<VarIdx>,
    min: Option<i64>,
    max: Option<i64>,
    arg_components: Vec<Option<usize>>,
    enforce_recursive_dependency: bool,
}

impl Approximation for LinearApprox {
    fn apply(&self, arg_terms: &[Term]) -> Vec<Term> {
        let subst_map: VarHMap<_> = self
            .approx
            .args
            .iter()
            .map(|x| x.idx)
            .zip(arg_terms.iter().cloned())
            .collect();
        let mut res = Vec::with_capacity(self.approx.terms.len());
        for term in self.approx.terms.iter() {
            res.push(term.subst(&subst_map).0);
        }
        res
    }
}

impl LinearApprox {
    fn constraint(&self) -> Option<Term> {
        let mut asserts = Vec::new();
        for c in self
            .coef
            .iter()
            .flat_map(|coefs| coefs.iter().filter_map(|c| *c))
            .chain(self.cnst.iter().copied())
        {
            if let Some(min) = self.min {
                let t = term::le(term::int(min), term::var(c, typ::int()));
                asserts.push(t);
            }

            if let Some(max) = self.max {
                let t = term::le(term::var(c, typ::int()), term::int(max));
                asserts.push(t);
            }
        }

        if self.enforce_recursive_dependency {
            for (term_idx, coefs) in self.coef.iter().enumerate() {
                let mut relevant = Vec::new();
                for (arg_pos, comp) in self.arg_components.iter().enumerate() {
                    if *comp != Some(term_idx) {
                        continue;
                    }
                    if let Some(coef) = coefs[VarIdx::from(arg_pos)] {
                        relevant.push(term::not(term::eq(
                            term::var(coef, typ::int()),
                            term::int_zero(),
                        )));
                    }
                }
                if !relevant.is_empty() {
                    asserts.push(term::or(relevant));
                }
            }
        }

        Some(term::and(asserts))
    }
    fn instantiate(&self, model: &Model) -> Approx {
        let mut subst_map: VarHMap<Term> = VarHMap::new();
        for cnst in self.cnst.iter() {
            subst_map.insert(*cnst, term::val(model[*cnst].clone()));
        }
        for coef in self.coef.iter().flat_map(|coefs| coefs.iter().filter_map(|c| *c)) {
            subst_map.insert(coef, term::val(model[coef].clone()));
        }

        let mut approx = self.approx.clone();
        approx.terms = approx
            .terms
            .into_iter()
            .map(|t| t.subst(&subst_map).0)
            .collect();
        approx
    }
}
impl LinearApprox {
    fn new(
        args: VarInfos,
        n_encs: usize,
        variables: &mut VarInfos,
        min: Option<i64>,
        max: Option<i64>,
        arg_components: Vec<Option<usize>>,
        structured: bool,
    ) -> Self {
        debug_assert_eq!(args.len(), arg_components.len());
        let structured = structured && n_encs > 1;

        let mut coef = Vec::with_capacity(n_encs);
        let mut cnst = VarMap::new();
        let mut terms = Vec::new();
        let enforce_recursive_dependency = structured;
        for term_idx in 0..n_encs {
            // prepare coefficients
            let varname = format!("coef-term-{term_idx}");
            let mut coefs: VarMap<Option<VarIdx>> = VarMap::new();
            for (arg_pos, arg_comp) in arg_components.iter().enumerate() {
                let allow = if structured {
                    match arg_comp {
                        // base arguments are always allowed
                        None => true,
                        // recursive arguments are only allowed on the diagonal
                        Some(c) => *c == term_idx,
                    }
                } else {
                    true
                };
                if allow {
                    let idx = variables.next_index();
                    let info = VarInfo::new(format!("{varname}-{arg_pos}"), typ::int(), idx);
                    variables.push(info);
                    coefs.push(Some(idx));
                } else {
                    coefs.push(None);
                }
            }

            // create const
            let const_idx = variables.next_index();
            let info = VarInfo::new(format!("const-term-{term_idx}"), typ::int(), const_idx);
            variables.push(info);

            // build term
            let mut parts = vec![term::var(const_idx, typ::int())];
            for (coef, arg) in coefs.iter().zip(args.iter()) {
                if let Some(coef) = coef {
                    let c = term::var(*coef, typ::int());
                    let v = term::var(arg.idx, arg.typ.clone());
                    parts.push(term::mul(vec![c, v]));
                }
            }
            terms.push(term::add(parts));

            coef.push(coefs);
            cnst.push(const_idx);
        }

        let approx = Approx {
            args,
            terms,
        };

        Self {
            coef,
            cnst,
            approx,
            min,
            max,
            arg_components,
            enforce_recursive_dependency,
        }
    }
}

impl Enc<Template> {
    fn instantiate(&self, model: &Model) -> Encoder {
        let mut approxs = BTreeMap::new();
        for (constr, approx) in self.approxs.iter() {
            let approx = approx.instantiate(model);
            approxs.insert(constr.clone(), approx);
        }
        Encoder {
            approxs,
            typ: self.typ.clone(),
            n_params: self.n_params,
        }
    }
}

#[test]
fn test_linear_approx_apply() {
    // dtyp = Cons(x)
    let mut args = VarInfos::new();
    let idx = VarIdx::from(0);
    args.push(VarInfo::new("x".to_string(), typ::int(), idx));
    let mut fvs = VarInfos::new();
    // mimic TemplateInfo behavior: template parameters start after the argument indices
    for arg in args.iter() {
        fvs.push(arg.clone());
    }
    let approx = LinearApprox::new(args, 1, &mut fvs, None, None, vec![None], false);

    let x = term::val(val::int(4));
    let argss = vec![x.clone()];
    let mut t = approx.apply(&argss);

    assert_eq!(t.len(), 1);
    let t = t.remove(0);

    let coef_idx = approx.coef[0][VarIdx::from(0)].unwrap();
    let cnst_idx = approx.cnst[VarIdx::from(0)];
    let t2 = term::add(vec![
        term::var(cnst_idx, typ::int()),
        term::mul(vec![term::var(coef_idx, typ::int()), x.clone()]),
    ]);
    println!("t: {}", t);
    println!("t2: {}", t2);
    for (a, b) in [(4i64, 3i64), (1, 2), (-4, 0)].into_iter() {
        let subst: VarHMap<_> = vec![
            (coef_idx, term::val(val::int(a))),
            (cnst_idx, term::val(val::int(b))),
        ]
        .into_iter()
        .collect();
        assert_eq!(
            t.subst_total(&subst).unwrap().0.as_val(),
            t2.subst_total(&subst).unwrap().0.as_val()
        );
    }
}

#[test]
fn test_linear_approx_apply_two_terms() {
    let mut args = VarInfos::new();
    let idx = VarIdx::from(0);
    args.push(VarInfo::new("x".to_string(), typ::int(), idx));
    let mut fvs = VarInfos::new();
    // mimic TemplateInfo behavior: template parameters start after the argument indices
    for arg in args.iter() {
        fvs.push(arg.clone());
    }
    let approx = LinearApprox::new(args, 2, &mut fvs, None, None, vec![None], false);

    let x = term::val(val::int(4));
    let argss = vec![x.clone()];
    let terms = approx.apply(&argss);
    assert_eq!(terms.len(), 2);

    let coef0 = approx.coef[0][VarIdx::from(0)].unwrap();
    let coef1 = approx.coef[1][VarIdx::from(0)].unwrap();
    let cnst0 = approx.cnst[VarIdx::from(0)];
    let cnst1 = approx.cnst[VarIdx::from(1)];

    // Assign concrete values and compare evaluated results.
    let subst: VarHMap<_> = vec![
        (coef0, term::val(val::int(2))),
        (coef1, term::val(val::int(3))),
        (cnst0, term::val(val::int(5))),
        (cnst1, term::val(val::int(7))),
    ]
    .into_iter()
    .collect();

    let values: Vec<_> = terms
        .into_iter()
        .map(|term| term.subst_total(&subst).unwrap().0.as_val())
        .collect();

    let expected0 = val::int(5 + 2 * 4);
    let expected1 = val::int(7 + 3 * 4);
    assert_eq!(values.len(), 2);
    assert!(values.contains(&expected0));
    assert!(values.contains(&expected1));
}

#[test]
fn test_solve_by_blasting_finds_model() {
    let mut parameters = VarInfos::new();
    let x_idx = parameters.next_index();
    parameters.push(VarInfo::new("x".to_string(), typ::int(), x_idx));
    let y_idx = parameters.next_index();
    parameters.push(VarInfo::new("y".to_string(), typ::int(), y_idx));

    let template_info = TemplateInfo {
        parameters,
        encs: BTreeMap::new(),
    };

    let x = term::var(x_idx, typ::int());
    let y = term::var(y_idx, typ::int());
    let form = term::and(vec![
        term::ge(x.clone(), term::int(-1)),
        term::le(x.clone(), term::int(1)),
        term::ge(y.clone(), term::int(-1)),
        term::le(y.clone(), term::int(1)),
        term::eq(term::add(vec![x.clone(), y.clone()]), term::int(1)),
    ]);

    let mut fvs = VarSet::new();
    fvs.insert(x_idx);
    fvs.insert(y_idx);

    let model = solve_by_blasting(&form, &template_info, &fvs, -1, 1)
        .expect("blasting should succeed")
        .expect("formula should be satisfiable");

    let x_val = model[x_idx].to_int().unwrap().unwrap();
    let y_val = model[y_idx].to_int().unwrap().unwrap();

    let lower: Int = (-1).into();
    let upper: Int = 1.into();
    assert!(x_val >= lower && x_val <= upper);
    assert!(y_val >= lower && y_val <= upper);

    let sum = x_val + y_val;
    assert_eq!(sum, 1.into());
}

#[test]
fn test_solve_by_blasting_unsat() {
    let mut parameters = VarInfos::new();
    let x_idx = parameters.next_index();
    parameters.push(VarInfo::new("x".to_string(), typ::int(), x_idx));
    let y_idx = parameters.next_index();
    parameters.push(VarInfo::new("y".to_string(), typ::int(), y_idx));

    let template_info = TemplateInfo {
        parameters,
        encs: BTreeMap::new(),
    };

    let x = term::var(x_idx, typ::int());
    let y = term::var(y_idx, typ::int());
    let form = term::eq(term::add(vec![x.clone(), y.clone()]), term::int(5));

    let mut fvs = VarSet::new();
    fvs.insert(x_idx);
    fvs.insert(y_idx);

    let model = solve_by_blasting(&form, &template_info, &fvs, -1, 1)
        .expect("blasting should not error");
    assert!(model.is_none());
}

#[test]
fn test_solve_by_blasting_prioritizes_zero() {
    let mut parameters = VarInfos::new();
    let x_idx = parameters.next_index();
    parameters.push(VarInfo::new("x".to_string(), typ::int(), x_idx));

    let template_info = TemplateInfo {
        parameters,
        encs: BTreeMap::new(),
    };

    let x = term::var(x_idx, typ::int());
    let form = term::or(vec![term::eq(x.clone(), term::int(-1)), term::eq(x.clone(), term::int(0))]);

    let mut fvs = VarSet::new();
    fvs.insert(x_idx);

    let model = solve_by_blasting(&form, &template_info, &fvs, -1, 1)
        .expect("blasting should not error")
        .expect("formula should be satisfiable");

    let val = model[x_idx].to_int().unwrap().unwrap();
    assert_eq!(val, 0.into());
}

fn solve_by_blasting(
    form: &term::Term,
    template_info: &TemplateInfo,
    fvs: &VarSet,
    min: i64,
    max: i64,
) -> Res<Option<Model>> {
    if min > max {
        return Ok(None);
    }

    let vars: Vec<_> = fvs.iter().copied().collect();

    let mut model: VarMap<Val> = template_info
        .parameters
        .iter()
        .map(|info| info.typ.default_val())
        .collect();

    fn search(
        form: &term::Term,
        vars: &[VarIdx],
        depth: usize,
        min: i64,
        max: i64,
        model: &mut VarMap<Val>,
    ) -> Res<Option<Model>> {
        if depth == vars.len() {
            return match form.bool_eval(model)? {
                Some(true) => Ok(Some(Model::from(model.clone()))),
                _ => Ok(None),
            };
        }

        let var = vars[depth];
        let prev = model[var].clone();
        let zero_first = min <= 0 && max >= 0;
        if zero_first {
            model[var] = val::int(0);
            if let Some(res) = search(form, vars, depth + 1, min, max, model)? {
                return Ok(Some(res));
            }
        }
        for value in (min..=max).rev() {
            if zero_first && value == 0 {
                continue;
            }
            model[var] = val::int(value);
            if let Some(res) = search(form, vars, depth + 1, min, max, model)? {
                return Ok(Some(res));
            }
        }
        model[var] = prev;
        Ok(None)
    }

    search(form, &vars, 0, min, max, &mut model)
}

// ============================================================================
// Linearization solver for [-1, 1] coefficient templates
// ============================================================================

use std::collections::{HashMap, HashSet};

/// Expands a term to polynomial normal form by distributing multiplication over addition.
///
/// For example:
/// - `c * (d + e)` → `c*d + c*e`
/// - `(a + b) * (c + d)` → `a*c + a*d + b*c + b*d`
/// - `c * c * c` → `c` (since c³ = c for c ∈ {-1, 0, 1})
fn expand_to_polynomial(term: &term::Term, coef_vars: &VarSet) -> term::Term {
    expand_term_recursive(term, coef_vars)
}

fn expand_term_recursive(term: &term::Term, coef_vars: &VarSet) -> term::Term {
    match term.get() {
        term::RTerm::Var(_, _) | term::RTerm::Cst(_) => term.clone(),

        term::RTerm::App { op, args, .. } => {
            // First, recursively expand all arguments
            let expanded_args: Vec<term::Term> =
                args.iter().map(|a| expand_term_recursive(a, coef_vars)).collect();

            match op {
                term::Op::Mul => expand_multiplication(&expanded_args, coef_vars),
                term::Op::CMul => {
                    // CMul is (constant * term), expand the term part
                    if expanded_args.len() == 2 {
                        let const_part = &expanded_args[0];
                        let term_part = &expanded_args[1];
                        // If term_part is an addition, distribute
                        if let Some((term::Op::Add, add_args)) = term_part.app_inspect() {
                            let distributed: Vec<term::Term> = add_args
                                .iter()
                                .map(|a| term::mul(vec![const_part.clone(), a.clone()]))
                                .collect();
                            term::add(distributed)
                        } else {
                            term::mul(vec![const_part.clone(), term_part.clone()])
                        }
                    } else {
                        term::app(term::Op::CMul, expanded_args)
                    }
                }
                term::Op::Add => {
                    // Flatten nested additions
                    let mut flat_args = Vec::new();
                    for arg in expanded_args {
                        if let Some((term::Op::Add, nested)) = arg.app_inspect() {
                            flat_args.extend(nested.clone());
                        } else {
                            flat_args.push(arg);
                        }
                    }
                    term::add(flat_args)
                }
                _ => term::app(*op, expanded_args),
            }
        }

        // For other term types, just clone (datatypes, etc.)
        _ => term.clone(),
    }
}

/// Expands a multiplication, distributing over additions and simplifying cubic terms.
///
/// This uses Cartesian product expansion, which can produce exponentially many terms
/// when there are multiple sums. For example, `(a+b)*(c+d)*(e+f)*(g+h)` produces 2^4=16 terms.
///
/// This is acceptable for coefficient templates, which are typically simple linear
/// combinations like `a*x + b*y + c` rather than deeply nested sum structures.
/// If this becomes a bottleneck, consider adding a size limit or alternative expansion.
fn expand_multiplication(args: &[term::Term], coef_vars: &VarSet) -> term::Term {
    // Separate additions from other terms
    let mut additions: Vec<&Vec<term::Term>> = Vec::new();
    let mut other_terms: Vec<term::Term> = Vec::new();
    let mut coef_var_counts: HashMap<VarIdx, usize> = HashMap::new();

    for arg in args {
        if let Some((term::Op::Add, add_args)) = arg.app_inspect() {
            additions.push(add_args);
        } else if let Some(var_idx) = arg.var_idx() {
            if coef_vars.contains(&var_idx) {
                *coef_var_counts.entry(var_idx).or_insert(0) += 1;
            } else {
                other_terms.push(arg.clone());
            }
        } else {
            other_terms.push(arg.clone());
        }
    }

    // Simplify cubic terms: c³ = c for c ∈ {-1, 0, 1}
    let mut simplified_vars: Vec<term::Term> = Vec::new();
    for (var_idx, count) in coef_var_counts {
        // c^n where n >= 1: reduce to c if n is odd, c² if n is even
        let effective_count = if count % 2 == 0 { 2 } else { 1 };
        for _ in 0..effective_count {
            simplified_vars.push(term::var(var_idx, typ::int()));
        }
    }

    // Combine other_terms with simplified_vars
    other_terms.extend(simplified_vars);

    if additions.is_empty() {
        // No additions to distribute, just multiply
        if other_terms.is_empty() {
            term::int(1)
        } else if other_terms.len() == 1 {
            other_terms.pop().unwrap()
        } else {
            term::mul(other_terms)
        }
    } else {
        // Distribute over additions using Cartesian product
        let mut products = vec![other_terms];

        for add_args in additions {
            let mut new_products = Vec::new();
            for product in products {
                for add_term in add_args {
                    let mut new_product = product.clone();
                    new_product.push(add_term.clone());
                    new_products.push(new_product);
                }
            }
            products = new_products;
        }

        // Convert each product to a term
        let sum_terms: Vec<term::Term> = products
            .into_iter()
            .map(|p| {
                if p.is_empty() {
                    term::int(1)
                } else if p.len() == 1 {
                    p.into_iter().next().unwrap()
                } else {
                    // Recursively expand in case there are nested multiplications
                    expand_multiplication(&p, coef_vars)
                }
            })
            .collect();

        if sum_terms.len() == 1 {
            sum_terms.into_iter().next().unwrap()
        } else {
            term::add(sum_terms)
        }
    }
}

/// Collects all squared coefficient variables and product pairs from a term.
///
/// Returns (squared_vars, product_pairs) where:
/// - squared_vars: coefficient variables that appear as c*c
/// - product_pairs: ordered pairs (c, d) of distinct coefficient variables appearing as c*d
///
/// Note: This function is not used in production (linearize_term does on-the-fly detection
/// which is more efficient), but is retained for unit testing the product collection logic.
#[cfg(test)]
fn collect_products(
    term: &term::Term,
    coef_vars: &VarSet,
) -> (HashSet<VarIdx>, HashSet<(VarIdx, VarIdx)>) {
    let mut squared = HashSet::new();
    let mut products = HashSet::new();
    collect_products_recursive(term, coef_vars, &mut squared, &mut products);
    (squared, products)
}

#[cfg(test)]
fn collect_products_recursive(
    term: &term::Term,
    coef_vars: &VarSet,
    squared: &mut HashSet<VarIdx>,
    products: &mut HashSet<(VarIdx, VarIdx)>,
) {
    match term.get() {
        term::RTerm::Var(_, _) | term::RTerm::Cst(_) => {}

        term::RTerm::App { op, args, .. } => {
            match op {
                term::Op::Mul => {
                    // Collect coefficient variables in this multiplication
                    let mut coef_indices: Vec<VarIdx> = Vec::new();
                    for arg in args {
                        if let Some(var_idx) = arg.var_idx() {
                            if coef_vars.contains(&var_idx) {
                                coef_indices.push(var_idx);
                            }
                        }
                        // Recurse into nested terms
                        collect_products_recursive(arg, coef_vars, squared, products);
                    }

                    // Find squared terms and product pairs
                    let mut seen: HashMap<VarIdx, usize> = HashMap::new();
                    for idx in &coef_indices {
                        *seen.entry(*idx).or_insert(0) += 1;
                    }

                    for (&idx, &count) in &seen {
                        if count >= 2 {
                            squared.insert(idx);
                        }
                    }

                    // Generate product pairs for distinct variables
                    let unique_vars: Vec<VarIdx> = seen.keys().copied().collect();
                    for i in 0..unique_vars.len() {
                        for j in (i + 1)..unique_vars.len() {
                            let a = unique_vars[i];
                            let b = unique_vars[j];
                            // Use ordered pair (min, max) to avoid duplicates
                            let pair = if a < b { (a, b) } else { (b, a) };
                            products.insert(pair);
                        }
                    }
                }
                _ => {
                    // Recurse into all arguments
                    for arg in args {
                        collect_products_recursive(arg, coef_vars, squared, products);
                    }
                }
            }
        }

        term::RTerm::DTypNew { args, .. } => {
            for arg in args {
                collect_products_recursive(arg, coef_vars, squared, products);
            }
        }

        term::RTerm::DTypSlc { term: inner, .. }
        | term::RTerm::DTypTst { term: inner, .. }
        | term::RTerm::CArray { term: inner, .. } => {
            collect_products_recursive(inner, coef_vars, squared, products);
        }

        term::RTerm::Fun { args, .. } => {
            for arg in args {
                collect_products_recursive(arg, coef_vars, squared, products);
            }
        }
    }
}

/// Context for linearization: manages auxiliary variables and their constraints.
struct LinearizationContext {
    /// Maps coefficient var to its square variable (c → c2 where c2 represents c²)
    squared_vars: HashMap<VarIdx, VarIdx>,
    /// Maps (c, d) pair to product variable c_d (where c_d represents c*d)
    product_vars: HashMap<(VarIdx, VarIdx), VarIdx>,
    /// Next fresh variable index
    next_var: VarIdx,
    /// Constraint terms for the auxiliary variables
    constraints: Vec<term::Term>,
}

impl LinearizationContext {
    fn new(start_var: VarIdx) -> Self {
        LinearizationContext {
            squared_vars: HashMap::new(),
            product_vars: HashMap::new(),
            next_var: start_var,
            constraints: Vec::new(),
        }
    }

    /// Get or create a squared variable for c.
    /// Adds constraint: (c = 0 ∧ c2 = 0) ∨ c2 = 1
    fn get_or_create_squared(&mut self, c: VarIdx) -> VarIdx {
        if let Some(&c2) = self.squared_vars.get(&c) {
            return c2;
        }

        let c2 = self.next_var;
        self.next_var = VarIdx::new(self.next_var.get() + 1);
        self.squared_vars.insert(c, c2);

        // Add constraint: (c = 0 ∧ c2 = 0) ∨ c2 = 1
        let c_term = term::var(c, typ::int());
        let c2_term = term::var(c2, typ::int());

        let case1 = term::and(vec![
            term::eq(c_term.clone(), term::int(0)),
            term::eq(c2_term.clone(), term::int(0)),
        ]);
        let case2 = term::eq(c2_term.clone(), term::int(1));

        self.constraints.push(term::or(vec![case1, case2]));

        c2
    }

    /// Get or create a product variable for c*d.
    /// Adds constraint: (c = 0 ∧ c_d = 0) ∨ (c = 1 ∧ c_d = d) ∨ (c = -1 ∧ c_d = -d)
    fn get_or_create_product(&mut self, c: VarIdx, d: VarIdx) -> VarIdx {
        // Normalize to (min, max) ordering
        let key = if c < d { (c, d) } else { (d, c) };

        if let Some(&c_d) = self.product_vars.get(&key) {
            return c_d;
        }

        let c_d = self.next_var;
        self.next_var = VarIdx::new(self.next_var.get() + 1);
        self.product_vars.insert(key, c_d);

        // Use the first variable (smaller index) as the "control" variable
        let (ctrl, other) = (key.0, key.1);
        let ctrl_term = term::var(ctrl, typ::int());
        let other_term = term::var(other, typ::int());
        let c_d_term = term::var(c_d, typ::int());

        // (ctrl = 0 ∧ c_d = 0) ∨ (ctrl = 1 ∧ c_d = other) ∨ (ctrl = -1 ∧ c_d = -other)
        let case1 = term::and(vec![
            term::eq(ctrl_term.clone(), term::int(0)),
            term::eq(c_d_term.clone(), term::int(0)),
        ]);
        let case2 = term::and(vec![
            term::eq(ctrl_term.clone(), term::int(1)),
            term::eq(c_d_term.clone(), other_term.clone()),
        ]);
        let case3 = term::and(vec![
            term::eq(ctrl_term.clone(), term::int(-1)),
            term::eq(c_d_term.clone(), term::cmul(-1, other_term.clone())),
        ]);

        self.constraints.push(term::or(vec![case1, case2, case3]));

        c_d
    }

    /// Get all constraints as a conjunction.
    fn get_constraints(&self) -> term::Term {
        if self.constraints.is_empty() {
            term::bool(true)
        } else {
            term::and(self.constraints.clone())
        }
    }
}

/// Rewrites a term by substituting coefficient products with auxiliary variables.
fn linearize_term(term: &term::Term, ctx: &mut LinearizationContext, coef_vars: &VarSet) -> term::Term {
    match term.get() {
        term::RTerm::Var(_, _) | term::RTerm::Cst(_) => term.clone(),

        term::RTerm::App { op, args, .. } => {
            match op {
                term::Op::Mul => {
                    // Collect coefficient variables and other terms
                    let mut coef_indices: Vec<VarIdx> = Vec::new();
                    let mut other_terms: Vec<term::Term> = Vec::new();

                    for arg in args {
                        if let Some(var_idx) = arg.var_idx() {
                            if coef_vars.contains(&var_idx) {
                                coef_indices.push(var_idx);
                            } else {
                                other_terms.push(linearize_term(arg, ctx, coef_vars));
                            }
                        } else {
                            other_terms.push(linearize_term(arg, ctx, coef_vars));
                        }
                    }

                    // Process coefficient variables: replace products with aux vars
                    let mut result_coef_terms: Vec<term::Term> = Vec::new();

                    if !coef_indices.is_empty() {
                        // Count occurrences of each coefficient variable
                        let mut counts: HashMap<VarIdx, usize> = HashMap::new();
                        for idx in &coef_indices {
                            *counts.entry(*idx).or_insert(0) += 1;
                        }

                        // Handle squared terms (c² → c2)
                        for (&idx, &count) in &counts {
                            if count >= 2 {
                                // c² → c2 (squared variable)
                                let c2 = ctx.get_or_create_squared(idx);
                                result_coef_terms.push(term::var(c2, typ::int()));
                            }
                        }

                        // For single occurrences, add them to result_coef_terms
                        for (&idx, &count) in &counts {
                            if count == 1 {
                                result_coef_terms.push(term::var(idx, typ::int()));
                            }
                        }

                        // Recursively pair coefficient-like terms until at most one remains.
                        // After pairing, aux vars (c_d, c2) are also in {-1, 0, 1}, so they
                        // need further pairing if there are multiple.
                        while result_coef_terms.len() >= 2 {
                            let mut new_terms = Vec::new();
                            let mut i = 0;
                            while i + 1 < result_coef_terms.len() {
                                let a_idx = result_coef_terms[i].var_idx().unwrap();
                                let b_idx = result_coef_terms[i + 1].var_idx().unwrap();
                                let ab = ctx.get_or_create_product(a_idx, b_idx);
                                new_terms.push(term::var(ab, typ::int()));
                                i += 2;
                            }
                            // If odd number, keep the last one
                            if i < result_coef_terms.len() {
                                new_terms.push(result_coef_terms[i].clone());
                            }
                            result_coef_terms = new_terms;
                        }
                    }

                    // Combine all terms
                    let mut all_terms = result_coef_terms;
                    all_terms.extend(other_terms);

                    if all_terms.is_empty() {
                        term::int(1)
                    } else if all_terms.len() == 1 {
                        all_terms.pop().unwrap()
                    } else {
                        term::mul(all_terms)
                    }
                }
                _ => {
                    // Recursively process arguments
                    let new_args: Vec<term::Term> = args
                        .iter()
                        .map(|a| linearize_term(a, ctx, coef_vars))
                        .collect();
                    term::app(*op, new_args)
                }
            }
        }

        term::RTerm::DTypNew { name, args, typ, .. } => {
            let new_args: Vec<term::Term> = args
                .iter()
                .map(|a| linearize_term(a, ctx, coef_vars))
                .collect();
            term::dtyp_new(typ.clone(), name.clone(), new_args)
        }

        term::RTerm::DTypSlc { name, term: inner, typ, .. } => {
            term::dtyp_slc(typ.clone(), name.clone(), linearize_term(inner, ctx, coef_vars))
        }

        term::RTerm::DTypTst { name, term: inner, .. } => {
            term::dtyp_tst(name.clone(), linearize_term(inner, ctx, coef_vars))
        }

        term::RTerm::CArray { term: inner, typ, .. } => {
            // CArray represents a constant array. Coefficient templates typically don't
            // contain arrays, but we handle it correctly for completeness.
            let new_inner = linearize_term(inner, ctx, coef_vars);
            if new_inner == *inner {
                term.clone()
            } else {
                term::cst_array(typ.clone(), new_inner)
            }
        }

        term::RTerm::Fun { name, args, .. } => {
            let new_args: Vec<term::Term> = args
                .iter()
                .map(|a| linearize_term(a, ctx, coef_vars))
                .collect();
            term::fun(name.clone(), new_args)
        }
    }
}

/// Solves a template formula using linearization for [-1, 1] coefficients.
fn solve_by_linearization(
    form: &term::Term,
    template_info: &TemplateInfo,
    fvs: &VarSet,
    solver: &mut Solver<Parser>,
) -> Res<Option<Model>> {
    log_debug!("Using linearization solver for {} variables", fvs.len());

    // Step 1: Expand to polynomial form
    let expanded = expand_to_polynomial(form, fvs);
    log_debug!("Expanded form: {}", expanded);

    // Step 2: Find max variable index for fresh variables
    let max_var = fvs.iter().copied().max().unwrap_or(VarIdx::new(0));
    let start_var = VarIdx::new(max_var.get() + 1);

    // Step 3: Create linearization context and linearize the term
    let mut ctx = LinearizationContext::new(start_var);
    let linearized = linearize_term(&expanded, &mut ctx, fvs);
    log_debug!("Linearized form: {}", linearized);

    // Step 4: Setup solver
    solver.reset()?;
    solver.set_option(":timeout", "10000")?; // 10 second timeout

    // Declare original coefficient variables with bounds [-1, 1]
    for var_idx in fvs.iter() {
        solver.declare_const(&format!("v_{}", var_idx), "Int")?;
        writeln!(solver, "(assert (>= v_{} (- 1)))", var_idx)?;
        writeln!(solver, "(assert (<= v_{} 1))", var_idx)?;
    }

    // Declare squared variables with bounds [0, 1]
    for (&_c, &c2) in &ctx.squared_vars {
        solver.declare_const(&format!("v_{}", c2), "Int")?;
        writeln!(solver, "(assert (>= v_{} 0))", c2)?;
        writeln!(solver, "(assert (<= v_{} 1))", c2)?;
    }

    // Declare product variables (can be in range [-1, 1] since result of c*d)
    for (&(_c, _d), &c_d) in &ctx.product_vars {
        solver.declare_const(&format!("v_{}", c_d), "Int")?;
        writeln!(solver, "(assert (>= v_{} (- 1)))", c_d)?;
        writeln!(solver, "(assert (<= v_{} 1))", c_d)?;
    }

    // Assert auxiliary variable constraints
    let aux_constraints = ctx.get_constraints();
    if !ctx.constraints.is_empty() {
        writeln!(solver, "; Auxiliary variable constraints")?;
        writeln!(solver, "(assert {})", aux_constraints)?;
    }

    // Assert the linearized formula
    writeln!(solver, "; Linearized target formula")?;
    writeln!(solver, "(assert {})", linearized)?;

    // Solve
    let sat = solver.check_sat()?;
    if !sat {
        log_debug!("Linearization solver: UNSAT");
        return Ok(None);
    }

    // Extract model, filtering to only original variables
    let full_model = solver.get_model()?;
    let full_model = Parser.fix_model(full_model)?;

    // Build a model with only the original coefficient variables
    let model = Model::of_model(&template_info.parameters, full_model, true)?;
    log_debug!("Linearization solver: SAT with model {}", model);

    Ok(Some(model))
}

impl<'a> LearnCtx<'a> {
    pub fn new(
        encs: &'a mut BTreeMap<Typ, Encoder>,
        cex: &'a CEX,
        solver: &'a mut Solver<Parser>,
        profiler: &'a Profiler,
    ) -> Self {
        let models = Vec::new();

        LearnCtx {
            original_encs: encs,
            cex,
            solver,
            models,
            profiler,
        }
    }

    /// Define encoding functions
    ///
    /// Assumption: Data types are all defined.
    fn define_enc_funs(&mut self) -> Res<()> {
        let ctx = super::enc::EncodeCtx::new(&self.original_encs);
        let mut funs = Vec::new();
        for enc in self.original_encs.values() {
            enc.generate_enc_fun(&ctx, &mut funs)?;
        }

        let funs_strs = funs.into_iter().map(|(funname, ty, term)| {
            let args = vec![("v_0", ty.to_string())];
            let body = term.to_string();
            (funname, args, "Int", body)
        });
        self.solver.define_funs_rec(funs_strs)?;
        Ok(())
    }

    /// Define data types
    fn define_datatypes(&mut self) -> Res<()> {
        dtyp::write_all(&mut self.solver, "")?;
        Ok(())
    }

    fn get_model(&mut self, timeout: Option<usize>) -> Res<Option<Model>> {
        self.solver.reset()?;
        self.define_datatypes()?;
        self.define_enc_funs()?;
        self.cex
            .define_assert_with_enc(&mut self.solver, &self.original_encs)?;
        if let Some(tmo) = timeout {
            self.solver.set_option(":timeout", &format!("{}000", tmo))?;
        } else {
            self.solver.set_option(":timeout", "4294967295")?;
        }
        let b = self.solver.check_sat()?;
        if !b {
            return Ok(None);
        }
        let model = self.solver.get_model()?;
        let model = Parser.fix_model(model)?;
        let cex = Model::of_model(&self.cex.vars, model, true)?;
        Ok(Some(cex))
    }

    fn get_template_model(
        &mut self,
        form: &term::Term,
        template_info: &TemplateInfo,
    ) -> Res<Option<Model>> {
        let fvs = form.free_vars();
        if let Some((min, max)) = template_info.param_range() {
            // Use blasting for small problems
            if fvs.len() <= THRESHOLD_BLASTING && max - min + 1 <= THRESHOLD_BLASTING_MAX_RANGE {
                return solve_by_blasting(form, template_info, &fvs, min, max)
            }

            // Use linearization for [-1, 1] templates with many variables
            // Triggers when: (a) forced via config, OR (b) vars > threshold and range is [-1,1]
            if min == -1 && max == 1 && (conf.force_linearization || fvs.len() > THRESHOLD_BLASTING) {
                return solve_by_linearization(form, template_info, &fvs, &mut self.solver);
            }
        }
        self.solver.reset()?;
        self.solver.set_option(":timeout", "4294967295")?;
        template_info.define_parameters(&mut self.solver)?;
        template_info.define_constraints(&mut self.solver)?;

        writeln!(self.solver, "; Target term")?;
        writeln!(self.solver, "(assert {})", form)?;

        writeln!(self.solver)?;
        let b = self.solver.check_sat()?;
        if !b {
            return Ok(None);
        }
        let model = self.solver.get_model()?;
        let model = Parser.fix_model(model)?;
        let cex = Model::of_model(&template_info.parameters, model, true)?;
        Ok(Some(cex))
    }
    fn get_instantiation(
        &mut self,
        template_info: TemplateInfo,
    ) -> Res<Option<BTreeMap<Typ, Encoder>>> {
        // 1. Let l1, ..., lk be li in fv(cex)
        // 2. vis = [[m[li] for m in self.models] for li in l1, ..., lk]
        // 4. Declare a1, ... ak in coef(enc) as free variables
        // 5. Declare template functions for each dtype <- not needed?
        // form <- T
        // 6. for vi in vis:
        //    r <- cex
        //    for li in l1, ..., lk:
        //       r <- r.subst(li, enc.encode(vi))
        //    form <- form /\ r
        // 7. solve form and return the model for
        // return form

        // templates encoder
        let mut form = Vec::new();
        let encoder = EncodeCtx::new(&template_info.encs);
        for m in self.models.iter() {
            let mut terms =
                encoder.encode(&term::not(self.cex.term.clone()), &|_: &Typ, v: &VarIdx| {
                    let v = &m[*v];
                    let terms = encoder.encode_val(v);
                    terms
                });
            form.append(&mut terms)
        }
        // solve the form
        let form = term::and(form);
        log_debug!("cex encoded with template");
        log_debug!("{}", form);

        let r = self.get_template_model(&form, &template_info)?.map(|m| {
            log_debug!("found model: {}", m);
            let encs = template_info.instantiate(&m);
            encs
        });
        Ok(r)
    }

    fn refine_enc(
        &mut self,
        original_encs: &BTreeMap<Typ, Encoder>,
    ) -> Res<Option<BTreeMap<Typ, Encoder>>> {
        for template_info in TemplateScheduler::new(original_encs.clone()) {
            match self.get_instantiation(template_info)? {
                None => continue,
                Some(new_encs) => return Ok(Some(new_encs)),
            }
        }
        Ok(None)
    }

    pub fn work(&mut self) -> Res<()> {
        // We now only consider the linear models
        // Appendinx them to the existing encodings
        let original_enc = self.original_encs.clone();
        let mut first = true;
        loop {
            // 1. Check if the new encoding can refute the counterexample
            log_info!("checking enc refutes cex...");
            if conf.split_step {
                pause("go?", self.profiler);
            }

            let timeout = if first {
                first = false;
                None
            } else {
                Some(CONSTRAINT_CHECK_TIMEOUT)
            };
            match self.get_model(timeout) {
                // The current cex is refuted
                Ok(None) => {
                    log_info!("Yes.");
                    break;
                }
                Ok(Some(model)) => {
                    log_info!("No.");
                    log_debug!("model: {}", model);

                    #[cfg(debug_assertions)]
                    {
                        for m in self.models.iter() {
                            assert_ne!(m, &model, "model is duplicated");
                        }
                    }
                    self.models.push(model);
                }
                Err(e) if e.is_timeout() || e.is_unknown() => {
                    log_info!("Timeout or unknown");
                    break;
                }
                Err(e) => {
                    println!("err: {}", e);
                    return Err(e);
                }
            }
            // 2. If not, learn something new
            *self.original_encs = self
                .refine_enc(&original_enc)?
                .expect("No appropriate template found");

            log_debug!("new_encs: ");
            for (k, v) in self.original_encs.iter() {
                log_debug!("{}: {}", k, v);
            }
        }
        Ok(())
    }
}

/// Entrypoint for the learning algorithm
///
/// If this function returns Ok(()), some encodings are appended to `encs`
/// so that `cex` can be refuted.
pub fn work<'a>(
    encs: &'a mut BTreeMap<Typ, Encoder>,
    cex: &'a CEX,
    solver: &mut Solver<Parser>,
    profiler: &Profiler,
) -> Res<()> {
    let mut learn_ctx = LearnCtx::new(encs, cex, solver, profiler);
    learn_ctx.work()?;
    Ok(())
}

// ============================================================================
// Unit tests for linearization
// ============================================================================

#[test]
fn test_expand_simple_product() {
    // Test: c * (d + e) => c*d + c*e
    let c_idx = VarIdx::new(0);
    let d_idx = VarIdx::new(1);
    let e_idx = VarIdx::new(2);

    let mut coef_vars = VarSet::new();
    coef_vars.insert(c_idx);
    coef_vars.insert(d_idx);
    coef_vars.insert(e_idx);

    let c = term::var(c_idx, typ::int());
    let d = term::var(d_idx, typ::int());
    let e = term::var(e_idx, typ::int());

    // c * (d + e)
    let term = term::mul(vec![c.clone(), term::add(vec![d.clone(), e.clone()])]);

    let expanded = expand_to_polynomial(&term, &coef_vars);

    // Result should be an addition
    let (op, args) = expanded.app_inspect().expect("expected an App");
    assert_eq!(op, term::Op::Add);
    assert_eq!(args.len(), 2);
}

#[test]
fn test_expand_cubic_simplification() {
    // Test: c * c * c => c (since c³ = c for c ∈ {-1, 0, 1})
    let c_idx = VarIdx::new(0);

    let mut coef_vars = VarSet::new();
    coef_vars.insert(c_idx);

    let c = term::var(c_idx, typ::int());

    // c * c * c
    let term = term::mul(vec![c.clone(), c.clone(), c.clone()]);

    let expanded = expand_to_polynomial(&term, &coef_vars);

    // Result should be just c
    assert_eq!(expanded.var_idx(), Some(c_idx));
}

#[test]
fn test_expand_squared() {
    // Test: c * c => c * c (two occurrences)
    let c_idx = VarIdx::new(0);

    let mut coef_vars = VarSet::new();
    coef_vars.insert(c_idx);

    let c = term::var(c_idx, typ::int());

    // c * c
    let term = term::mul(vec![c.clone(), c.clone()]);

    let expanded = expand_to_polynomial(&term, &coef_vars);

    // Result should be a multiplication of two c's
    let (op, args) = expanded.app_inspect().expect("expected an App");
    assert_eq!(op, term::Op::Mul);
    assert_eq!(args.len(), 2);
}

#[test]
fn test_collect_products_basic() {
    // Test: c * d detected as product
    let c_idx = VarIdx::new(0);
    let d_idx = VarIdx::new(1);

    let mut coef_vars = VarSet::new();
    coef_vars.insert(c_idx);
    coef_vars.insert(d_idx);

    let c = term::var(c_idx, typ::int());
    let d = term::var(d_idx, typ::int());

    let term = term::mul(vec![c, d]);

    let (squared, products) = collect_products(&term, &coef_vars);

    assert!(squared.is_empty());
    assert_eq!(products.len(), 1);
    assert!(products.contains(&(c_idx, d_idx)));
}

#[test]
fn test_collect_products_squared() {
    // Test: c * c detected as squared
    let c_idx = VarIdx::new(0);

    let mut coef_vars = VarSet::new();
    coef_vars.insert(c_idx);

    let c = term::var(c_idx, typ::int());

    let term = term::mul(vec![c.clone(), c.clone()]);

    let (squared, products) = collect_products(&term, &coef_vars);

    assert_eq!(squared.len(), 1);
    assert!(squared.contains(&c_idx));
    assert!(products.is_empty());
}

#[test]
fn test_collect_products_triple() {
    // Test: c * c * d => squared(c) and product(c, d)
    let c_idx = VarIdx::new(0);
    let d_idx = VarIdx::new(1);

    let mut coef_vars = VarSet::new();
    coef_vars.insert(c_idx);
    coef_vars.insert(d_idx);

    let c = term::var(c_idx, typ::int());
    let d = term::var(d_idx, typ::int());

    let term = term::mul(vec![c.clone(), c.clone(), d]);

    let (squared, products) = collect_products(&term, &coef_vars);

    assert_eq!(squared.len(), 1);
    assert!(squared.contains(&c_idx));
    assert_eq!(products.len(), 1);
    assert!(products.contains(&(c_idx, d_idx)));
}

#[test]
fn test_linearization_context_squared_constraint() {
    // Test that squared constraint is generated correctly
    let c_idx = VarIdx::new(0);
    let start_var = VarIdx::new(10);

    let mut ctx = LinearizationContext::new(start_var);
    let c2 = ctx.get_or_create_squared(c_idx);

    // c2 should be the start_var
    assert_eq!(c2, start_var);

    // Should have one constraint
    assert_eq!(ctx.constraints.len(), 1);

    // Constraint should be: (c = 0 ∧ c2 = 0) ∨ c2 = 1
    // We just check it's an Or
    let (op, _) = ctx.constraints[0].app_inspect().expect("expected an App");
    assert_eq!(op, term::Op::Or);
}

#[test]
fn test_linearization_context_product_constraint() {
    // Test that product constraint is generated correctly
    let c_idx = VarIdx::new(0);
    let d_idx = VarIdx::new(1);
    let start_var = VarIdx::new(10);

    let mut ctx = LinearizationContext::new(start_var);
    let c_d = ctx.get_or_create_product(c_idx, d_idx);

    // c_d should be the start_var
    assert_eq!(c_d, start_var);

    // Should have one constraint
    assert_eq!(ctx.constraints.len(), 1);

    // Constraint should be an Or with 3 cases
    let (op, args) = ctx.constraints[0].app_inspect().expect("expected an App");
    assert_eq!(op, term::Op::Or);
    assert_eq!(args.len(), 3);
}

#[test]
fn test_linearization_context_reuse() {
    // Test that same variable pair returns same aux var
    let c_idx = VarIdx::new(0);
    let d_idx = VarIdx::new(1);
    let start_var = VarIdx::new(10);

    let mut ctx = LinearizationContext::new(start_var);

    let c2_first = ctx.get_or_create_squared(c_idx);
    let c2_second = ctx.get_or_create_squared(c_idx);

    assert_eq!(c2_first, c2_second);
    assert_eq!(ctx.constraints.len(), 1); // Only one constraint

    let cd_first = ctx.get_or_create_product(c_idx, d_idx);
    let cd_second = ctx.get_or_create_product(c_idx, d_idx);
    let cd_reversed = ctx.get_or_create_product(d_idx, c_idx);

    assert_eq!(cd_first, cd_second);
    assert_eq!(cd_first, cd_reversed); // Normalized ordering
    assert_eq!(ctx.constraints.len(), 2); // Two constraints (one squared, one product)
}

#[test]
fn test_linearize_term_basic() {
    // Test linearization of c * c => c2
    let c_idx = VarIdx::new(0);
    let start_var = VarIdx::new(10);

    let mut coef_vars = VarSet::new();
    coef_vars.insert(c_idx);

    let c = term::var(c_idx, typ::int());
    let term = term::mul(vec![c.clone(), c.clone()]);

    let mut ctx = LinearizationContext::new(start_var);
    let linearized = linearize_term(&term, &mut ctx, &coef_vars);

    // Result should be just c2 (the aux var)
    assert_eq!(linearized.var_idx(), Some(start_var));
    assert_eq!(ctx.squared_vars.len(), 1);
}

#[test]
fn test_linearize_term_product() {
    // Test linearization of c * d => c_d
    let c_idx = VarIdx::new(0);
    let d_idx = VarIdx::new(1);
    let start_var = VarIdx::new(10);

    let mut coef_vars = VarSet::new();
    coef_vars.insert(c_idx);
    coef_vars.insert(d_idx);

    let c = term::var(c_idx, typ::int());
    let d = term::var(d_idx, typ::int());
    let term = term::mul(vec![c, d]);

    let mut ctx = LinearizationContext::new(start_var);
    let linearized = linearize_term(&term, &mut ctx, &coef_vars);

    // Result should be just c_d (the aux var)
    assert_eq!(linearized.var_idx(), Some(start_var));
    assert_eq!(ctx.product_vars.len(), 1);
}

#[test]
fn test_expand_nested_product() {
    // Test: c * (d + c) => c*d + c*c
    let c_idx = VarIdx::new(0);
    let d_idx = VarIdx::new(1);

    let mut coef_vars = VarSet::new();
    coef_vars.insert(c_idx);
    coef_vars.insert(d_idx);

    let c = term::var(c_idx, typ::int());
    let d = term::var(d_idx, typ::int());

    // c * (d + c)
    let term = term::mul(vec![c.clone(), term::add(vec![d.clone(), c.clone()])]);

    let expanded = expand_to_polynomial(&term, &coef_vars);

    // Result should be an addition of two terms
    let (op, args) = expanded.app_inspect().expect("expected an App");
    assert_eq!(op, term::Op::Add);
    assert_eq!(args.len(), 2);

    // One term should contain c*d (product of two different vars)
    // The other should contain c*c (squared)
}

#[test]
fn test_expand_double_sum() {
    // Test: (a + b) * (c + d) => a*c + a*d + b*c + b*d
    let a_idx = VarIdx::new(0);
    let b_idx = VarIdx::new(1);
    let c_idx = VarIdx::new(2);
    let d_idx = VarIdx::new(3);

    let mut coef_vars = VarSet::new();
    coef_vars.insert(a_idx);
    coef_vars.insert(b_idx);
    coef_vars.insert(c_idx);
    coef_vars.insert(d_idx);

    let a = term::var(a_idx, typ::int());
    let b = term::var(b_idx, typ::int());
    let c = term::var(c_idx, typ::int());
    let d = term::var(d_idx, typ::int());

    // (a + b) * (c + d)
    let term = term::mul(vec![
        term::add(vec![a.clone(), b.clone()]),
        term::add(vec![c.clone(), d.clone()]),
    ]);

    let expanded = expand_to_polynomial(&term, &coef_vars);

    // Result should be an addition of 4 terms
    let (op, args) = expanded.app_inspect().expect("expected an App");
    assert_eq!(op, term::Op::Add);
    assert_eq!(args.len(), 4);
}

#[test]
fn test_collect_products_ignores_non_coef() {
    // Test: c * x where x is not a coef var => no product collected
    let c_idx = VarIdx::new(0);
    let x_idx = VarIdx::new(1);

    let mut coef_vars = VarSet::new();
    coef_vars.insert(c_idx); // Only c is a coef var, not x

    let c = term::var(c_idx, typ::int());
    let x = term::var(x_idx, typ::int());

    let term = term::mul(vec![c, x]);

    let (squared, products) = collect_products(&term, &coef_vars);

    // No products should be detected since x is not a coef var
    assert!(squared.is_empty());
    assert!(products.is_empty());
}

#[test]
fn test_linearize_term_mixed() {
    // Test: c * c * d => should produce c2 (for c*c) and keep d separate
    // After linearization: c2 * d (where c2 is aux var for c²)
    let c_idx = VarIdx::new(0);
    let d_idx = VarIdx::new(1);
    let start_var = VarIdx::new(10);

    let mut coef_vars = VarSet::new();
    coef_vars.insert(c_idx);
    coef_vars.insert(d_idx);

    let c = term::var(c_idx, typ::int());
    let d = term::var(d_idx, typ::int());

    // c * c * d
    let term = term::mul(vec![c.clone(), c.clone(), d.clone()]);

    let mut ctx = LinearizationContext::new(start_var);
    let linearized = linearize_term(&term, &mut ctx, &coef_vars);

    // Should have created a squared variable for c
    assert_eq!(ctx.squared_vars.len(), 1);
    assert!(ctx.squared_vars.contains_key(&c_idx));

    // Result should be a multiplication (c2 * d)
    let (op, args) = linearized.app_inspect().expect("expected an App");
    assert_eq!(op, term::Op::Mul);
    assert_eq!(args.len(), 2);
}

#[test]
fn test_expand_with_constant() {
    // Test: 2 * c * d should keep constant and expand correctly
    let c_idx = VarIdx::new(0);
    let d_idx = VarIdx::new(1);

    let mut coef_vars = VarSet::new();
    coef_vars.insert(c_idx);
    coef_vars.insert(d_idx);

    let c = term::var(c_idx, typ::int());
    let d = term::var(d_idx, typ::int());

    // 2 * c * d
    let term = term::mul(vec![term::int(2), c.clone(), d.clone()]);

    let expanded = expand_to_polynomial(&term, &coef_vars);

    // Result should be a multiplication (structure may vary due to simplification)
    let (op, args) = expanded.app_inspect().expect("expected an App");
    assert_eq!(op, term::Op::Mul);
    // Should have at least 2 factors (constant may be absorbed into CMul structure)
    assert!(args.len() >= 2);
}

#[test]
fn test_expand_mixed_constant_and_sum() {
    // Test: c * (5 + d) => 5*c + c*d
    let c_idx = VarIdx::new(0);
    let d_idx = VarIdx::new(1);

    let mut coef_vars = VarSet::new();
    coef_vars.insert(c_idx);
    coef_vars.insert(d_idx);

    let c = term::var(c_idx, typ::int());
    let d = term::var(d_idx, typ::int());

    // c * (5 + d)
    let term = term::mul(vec![c.clone(), term::add(vec![term::int(5), d.clone()])]);

    let expanded = expand_to_polynomial(&term, &coef_vars);

    // Result should be an addition of 2 terms
    let (op, args) = expanded.app_inspect().expect("expected an App");
    assert_eq!(op, term::Op::Add);
    assert_eq!(args.len(), 2);
}

#[test]
fn test_linearize_nested_product() {
    // Test full pipeline: c * (d + c) after expansion and linearization
    let c_idx = VarIdx::new(0);
    let d_idx = VarIdx::new(1);
    let start_var = VarIdx::new(10);

    let mut coef_vars = VarSet::new();
    coef_vars.insert(c_idx);
    coef_vars.insert(d_idx);

    let c = term::var(c_idx, typ::int());
    let d = term::var(d_idx, typ::int());

    // c * (d + c)
    let term = term::mul(vec![c.clone(), term::add(vec![d.clone(), c.clone()])]);

    // Step 1: Expand
    let expanded = expand_to_polynomial(&term, &coef_vars);

    // Step 2: Linearize
    let mut ctx = LinearizationContext::new(start_var);
    let linearized = linearize_term(&expanded, &mut ctx, &coef_vars);

    // After expansion: c*d + c*c
    // After linearization: c_d + c2 (where c_d is aux var for c*d, c2 for c²)
    // Should have one product var and one squared var
    assert_eq!(ctx.product_vars.len(), 1);
    assert_eq!(ctx.squared_vars.len(), 1);

    // Result should be an addition
    let (op, _) = linearized.app_inspect().expect("expected an App");
    assert_eq!(op, term::Op::Add);
}

#[test]
fn test_linearization_constraint_count() {
    // Verify correct number of constraints are generated
    let c_idx = VarIdx::new(0);
    let d_idx = VarIdx::new(1);
    let e_idx = VarIdx::new(2);
    let start_var = VarIdx::new(10);

    let mut coef_vars = VarSet::new();
    coef_vars.insert(c_idx);
    coef_vars.insert(d_idx);
    coef_vars.insert(e_idx);

    let c = term::var(c_idx, typ::int());
    let d = term::var(d_idx, typ::int());
    let e = term::var(e_idx, typ::int());

    // c * c + d * e (needs c2 and d_e)
    let term = term::add(vec![
        term::mul(vec![c.clone(), c.clone()]),
        term::mul(vec![d.clone(), e.clone()]),
    ]);

    let mut ctx = LinearizationContext::new(start_var);
    let _ = linearize_term(&term, &mut ctx, &coef_vars);

    // Should have 1 squared var (c2) and 1 product var (d_e)
    assert_eq!(ctx.squared_vars.len(), 1);
    assert_eq!(ctx.product_vars.len(), 1);

    // Should have 2 constraints (one for each aux var)
    assert_eq!(ctx.constraints.len(), 2);
}

#[test]
fn test_linearize_preserves_non_coef_vars() {
    // Test that non-coefficient variables are preserved correctly
    let c_idx = VarIdx::new(0);
    let x_idx = VarIdx::new(1); // Not a coef var
    let start_var = VarIdx::new(10);

    let mut coef_vars = VarSet::new();
    coef_vars.insert(c_idx); // Only c is a coef var

    let c = term::var(c_idx, typ::int());
    let x = term::var(x_idx, typ::int());

    // c * x (x is not a coef var, so no product aux var needed)
    let term = term::mul(vec![c.clone(), x.clone()]);

    let mut ctx = LinearizationContext::new(start_var);
    let linearized = linearize_term(&term, &mut ctx, &coef_vars);

    // No aux variables should be created
    assert!(ctx.squared_vars.is_empty());
    assert!(ctx.product_vars.is_empty());
    assert!(ctx.constraints.is_empty());

    // Result should be a multiplication of c and x (unchanged)
    let (op, args) = linearized.app_inspect().expect("expected an App");
    assert_eq!(op, term::Op::Mul);
    assert_eq!(args.len(), 2);
}

#[test]
fn test_expand_deeply_nested() {
    // Test: c * ((d + e) * f) - deeply nested structure
    let c_idx = VarIdx::new(0);
    let d_idx = VarIdx::new(1);
    let e_idx = VarIdx::new(2);
    let f_idx = VarIdx::new(3);

    let mut coef_vars = VarSet::new();
    coef_vars.insert(c_idx);
    coef_vars.insert(d_idx);
    coef_vars.insert(e_idx);
    coef_vars.insert(f_idx);

    let c = term::var(c_idx, typ::int());
    let d = term::var(d_idx, typ::int());
    let e = term::var(e_idx, typ::int());
    let f = term::var(f_idx, typ::int());

    // c * ((d + e) * f) => c*d*f + c*e*f
    let inner = term::mul(vec![term::add(vec![d.clone(), e.clone()]), f.clone()]);
    let term = term::mul(vec![c.clone(), inner]);

    let expanded = expand_to_polynomial(&term, &coef_vars);

    // Result should be an addition of 2 terms (c*d*f and c*e*f)
    let (op, args) = expanded.app_inspect().expect("expected an App");
    assert_eq!(op, term::Op::Add);
    assert_eq!(args.len(), 2);
}

#[test]
fn test_power_of_four_simplification() {
    // Test: c * c * c * c => c * c (since c⁴ = c² for c ∈ {-1, 0, 1})
    let c_idx = VarIdx::new(0);

    let mut coef_vars = VarSet::new();
    coef_vars.insert(c_idx);

    let c = term::var(c_idx, typ::int());

    // c * c * c * c
    let term = term::mul(vec![c.clone(), c.clone(), c.clone(), c.clone()]);

    let expanded = expand_to_polynomial(&term, &coef_vars);

    // Result should be c * c (two occurrences)
    let (op, args) = expanded.app_inspect().expect("expected an App");
    assert_eq!(op, term::Op::Mul);
    assert_eq!(args.len(), 2);
}

#[test]
fn test_full_linearization_pipeline() {
    // Comprehensive test: c * (d + c) + e * e
    // After expansion: c*d + c*c + e*e
    // After linearization: c_d + c2 + e2 (three aux vars: c_d for c*d, c2 for c², e2 for e²)
    let c_idx = VarIdx::new(0);
    let d_idx = VarIdx::new(1);
    let e_idx = VarIdx::new(2);
    let start_var = VarIdx::new(10);

    let mut coef_vars = VarSet::new();
    coef_vars.insert(c_idx);
    coef_vars.insert(d_idx);
    coef_vars.insert(e_idx);

    let c = term::var(c_idx, typ::int());
    let d = term::var(d_idx, typ::int());
    let e = term::var(e_idx, typ::int());

    // c * (d + c) + e * e
    let term = term::add(vec![
        term::mul(vec![c.clone(), term::add(vec![d.clone(), c.clone()])]),
        term::mul(vec![e.clone(), e.clone()]),
    ]);

    // Step 1: Expand
    let expanded = expand_to_polynomial(&term, &coef_vars);

    // Should be: c*d + c*c + e*e (three terms)
    let (op, args) = expanded.app_inspect().expect("expected an App");
    assert_eq!(op, term::Op::Add);
    assert_eq!(args.len(), 3);

    // Step 2: Linearize
    let mut ctx = LinearizationContext::new(start_var);
    let linearized = linearize_term(&expanded, &mut ctx, &coef_vars);

    // Should have: 1 product var (c*d), 2 squared vars (c², e²)
    assert_eq!(ctx.product_vars.len(), 1);
    assert_eq!(ctx.squared_vars.len(), 2);
    assert!(ctx.squared_vars.contains_key(&c_idx));
    assert!(ctx.squared_vars.contains_key(&e_idx));

    // Should have 3 constraints (one per aux var)
    assert_eq!(ctx.constraints.len(), 3);

    // Result should be an addition of three terms (all aux vars)
    let (op, _) = linearized.app_inspect().expect("expected an App");
    assert_eq!(op, term::Op::Add);
}

#[test]
fn test_linearization_constraint_structure() {
    // Verify that constraints are well-formed
    let c_idx = VarIdx::new(0);
    let d_idx = VarIdx::new(1);
    let start_var = VarIdx::new(10);

    let mut ctx = LinearizationContext::new(start_var);

    // Create both squared and product vars
    let _c2 = ctx.get_or_create_squared(c_idx);
    let _cd = ctx.get_or_create_product(c_idx, d_idx);

    // Get all constraints as a conjunction
    let constraints = ctx.get_constraints();

    // Should be a conjunction (And) of two constraints
    let (op, args) = constraints.app_inspect().expect("expected an App");
    assert_eq!(op, term::Op::And);
    assert_eq!(args.len(), 2);

    // Each constraint should be a disjunction (Or)
    for arg in args {
        let (sub_op, _) = arg.app_inspect().expect("expected an App");
        assert_eq!(sub_op, term::Op::Or);
    }
}
