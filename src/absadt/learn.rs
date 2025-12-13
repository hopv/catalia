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
                for (sel, ty) in ty.selectors_of(constr).unwrap().iter() {
                    let ty = ty.to_type(Some(prms)).unwrap();
                    let n_arg = if encs.get(&ty).is_some() {
                        n_encs
                    } else {
                        assert!(ty.is_int());
                        1
                    };
                    for i in 0..n_arg {
                        let next_index = variables.next_index();
                        let info = VarInfo::new(
                            format!("arg-{}-{}", sel, i),
                            typ::int(),
                            next_index,
                        );
                        variables.push(info.clone());
                        approx_args.push(info);
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

enum TemplateType {
    BoundLinear { min: i64, max: i64 },
    Linear,
}

impl std::fmt::Display for TemplateType {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            TemplateType::BoundLinear { min, max } => write!(f, "BoundLinear({}, {})", min, max),
            TemplateType::Linear => write!(f, "Linear"),
        }
    }
}

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
    const N_TEMPLATES: usize = 8;

    const TEMPLATE_SCHDEDULING: [TemplateSchedItem; Self::N_TEMPLATES] = [
        TemplateSchedItem {
            n_encs: 1,
            typ: TemplateType::BoundLinear { min: -1, max: 1 },
        },
        TemplateSchedItem {
            n_encs: 2,
            typ: TemplateType::BoundLinear { min: -1, max: 1 },
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
            let next_template = &Self::TEMPLATE_SCHDEDULING[self.idx];
            self.idx += 1;

            let r = match next_template.typ {
                TemplateType::BoundLinear { min, max } => {
                    TemplateInfo::new_linear_approx(&self.enc, next_template.n_encs, Some(min), Some(max))
                }
                TemplateType::Linear => {
                    TemplateInfo::new_linear_approx(&self.enc, next_template.n_encs, None, None)
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
    coef: Vec<VarMap<VarIdx>>,
    cnst: VarMap<VarIdx>,
    min: Option<i64>,
    max: Option<i64>,
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
            .flat_map(|coefs| coefs.iter())
            .chain(self.cnst.iter())
        {
            if let Some(min) = self.min {
                let t = term::le(term::int(min), term::var(*c, typ::int()));
                asserts.push(t);
            }

            if let Some(max) = self.max {
                let t = term::le(term::var(*c, typ::int()), term::int(max));
                asserts.push(t);
            }
        }

        Some(term::and(asserts))
    }
    fn instantiate(&self, model: &Model) -> Approx {
        let mut subst_map: VarHMap<Term> = VarHMap::new();
        for cnst in self.cnst.iter() {
            subst_map.insert(*cnst, term::val(model[*cnst].clone()));
        }
        for coef in self.coef.iter().flatten() {
            subst_map.insert(*coef, term::val(model[*coef].clone()));
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
    ) -> Self {
        let mut coef = Vec::with_capacity(n_encs);
        let mut cnst = VarMap::new();
        let mut terms = Vec::new();
        for term_idx in 0..n_encs {
            // prepare coefficients
            let name = format!("coef-term-{term_idx}");
            let coefs = prepare_coefs(name, variables, args.len());

            // create const
            let const_idx = variables.next_index();
            let info = VarInfo::new(format!("const-term-{term_idx}"), typ::int(), const_idx);
            variables.push(info);

            // build term
            let mut parts = vec![term::var(const_idx, typ::int())];
            for (coef, arg) in coefs.iter().zip(args.iter()) {
                let c = term::var(*coef, typ::int());
                let v = term::var(arg.idx, arg.typ.clone());
                parts.push(term::mul(vec![c, v]));
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
    let approx = LinearApprox::new(args, 1, &mut fvs, None, None);

    let x = term::val(val::int(4));
    let argss = vec![x.clone()];
    let mut t = approx.apply(&argss);

    assert_eq!(t.len(), 1);
    let t = t.remove(0);

    let coef_idx = approx.coef[0][VarIdx::from(0)];
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
    let approx = LinearApprox::new(args, 2, &mut fvs, None, None);

    let x = term::val(val::int(4));
    let argss = vec![x.clone()];
    let terms = approx.apply(&argss);
    assert_eq!(terms.len(), 2);

    let coef0 = approx.coef[0][VarIdx::from(0)];
    let coef1 = approx.coef[1][VarIdx::from(0)];
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

fn prepare_coefs<S>(
    varname: S,
    variables: &mut VarInfos,
    n: usize,
) -> VarMap<VarIdx>
where
    S: AsRef<str>,
{
    let varname = varname.as_ref();
    let mut res = VarMap::new();
    for i in 0..n {
        let idx = variables.next_index();
        let info = VarInfo::new(format!("{varname}-{i}"), typ::int(), idx);
        res.push(idx);
        variables.push(info);
    }
    res
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
            if fvs.len() <= THRESHOLD_BLASTING && max - min + 1 <= THRESHOLD_BLASTING_MAX_RANGE {
                return solve_by_blasting(form, template_info, &fvs, min, max)
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
