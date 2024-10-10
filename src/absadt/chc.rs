//! This is "another representation" for chcs
//!
//! Due to the lack of my understanding of HoIce's implementation, to implement
//! my poc on top of HoIce, I have to create another representation for chcs.
//! This representation is expected to be used by the absadt solver for
//!  - Inline clauses naively
//!  - Preserve the order of the body of predicate applciations (rhs_preds)
//!    (not sure in the current implementation, it is)
//!    * This is important for the absadt solver to extract a counterexample
//!    from a resolution proof, since the order of the execution is important
//!
//! These functionalitiy should be merged in the future with the original HoIce's instance
use crate::common::*;
use crate::info::VarInfo;
use crate::term::Term;

use super::enc::{self, Approximation, Enc};
use super::hyper_res;
use crate::common::smt::FullParser as Parser;
use hyper_res::ResolutionProof;

use std::path::PathBuf;

const CHECK_SAT_TIMEOUT: usize = 10;
const CHECK_CHC_TIMEOUT: usize = 100;

pub struct PredApp {
    pub pred: PrdIdx,
    pub args: VarTerms,
}

impl std::fmt::Display for PredApp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "P{}(", self.pred)?;
        let mut itr = self.args.iter();
        if let Some(arg) = itr.next() {
            write!(f, "{}", arg)?;
        }
        for arg in itr {
            write!(f, ", {}", arg)?;
        }
        write!(f, ")")
    }
}

pub struct AbsClause {
    pub vars: VarInfos,
    pub rhs: Option<(PrdIdx, Vec<VarIdx>)>,
    pub lhs_preds: Vec<PredApp>,
    pub lhs_term: Term,
}

impl std::fmt::Display for AbsClause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.lhs_term.is_true() {
            write!(f, "true")?;
        } else {
            write!(f, "{}", self.lhs_term)?;
        }
        for pred in self.lhs_preds.iter() {
            write!(f, "/\\ {}", pred)?;
        }
        if let Some((pred, args)) = &self.rhs {
            write!(f, " => P{}(", pred)?;
            let mut itr = args.iter();
            if let Some(arg) = itr.next() {
                write!(f, "v_{}", arg)?;
            }
            for arg in itr {
                write!(f, ", v_{}", arg)?;
            }
            write!(f, ")")?;
        } else {
            write!(f, " => false")?;
        }
        Ok(())
    }
}

const TAG_PRED: &str = "tag!";
const IDX_ARG: &str = "idx!";

/// Mostly taken from clause.rs
/// The important difference is that the order of the body is preserved
impl AbsClause {
    /// Retrieves or constructs the let-bindings for this clause.
    ///
    /// Vector is sorted by the depth of the terms in the map. For each map, all terms should have
    /// the same depth.
    pub fn bindings(&self) -> Option<term::Bindings> {
        let mut r = term::bindings::Builder::new().scan_term(&self.lhs_term);
        for pred in self.lhs_preds.iter() {
            r = r.scan_terms(pred.args.iter())
        }
        r.build(self.vars.next_index())
    }

    pub fn write<W, WriteVar, WritePrd>(
        &self,
        w: &mut W,
        write_var: WriteVar,
        write_prd: WritePrd,
        tag_pred: Option<&str>,
        // define (idx! Int) as the top-level variable for the clause if true
        define_idx: bool,
    ) -> IoRes<()>
    where
        W: Write,
        WriteVar: Fn(&mut W, &VarInfo) -> IoRes<()>,
        WritePrd: Fn(
            &mut W,
            // None: do not track the position of applications
            // Some(Left): head
            // Some(Right): body. The value represents the position
            either::Either<(), usize>,
            PrdIdx,
            &VarTerms,
            Option<&term::Bindings>,
        ) -> IoRes<()>,
    {
        writeln!(w, "({} ", keywords::cmd::assert)?;
        self.forall_write(w, write_var, write_prd, 2, tag_pred, define_idx)?;
        writeln!(w, ")")?;
        Ok(())
    }
    pub fn forall_write<W, WriteVar, WritePrd>(
        &self,
        w: &mut W,
        write_var: WriteVar,
        write_prd: WritePrd,
        indent: usize,
        tag_pred: Option<&str>,
        define_idx: bool,
    ) -> IoRes<()>
    where
        W: Write,
        WriteVar: Fn(&mut W, &VarInfo) -> IoRes<()>,
        WritePrd: Fn(
            &mut W,
            either::Either<(), usize>,
            PrdIdx,
            &VarTerms,
            Option<&term::Bindings>,
        ) -> IoRes<()>,
    {
        write!(
            w,
            "{nil: >indent$}({}\n{nil: >indent$}  (",
            keywords::forall,
            nil = "",
            indent = indent
        )?;

        let mut inactive = 0;
        for var in &self.vars {
            if var.active {
                write!(w, " (")?;
                write_var(w, var)?;
                write!(w, " {})", var.typ)?
            } else {
                inactive += 1;
            }
        }
        if inactive == self.vars.len() {
            write!(w, " (unused Bool)")?
        }

        if define_idx {
            write!(w, "({IDX_ARG} Int)")?
        }

        writeln!(w, " )")?;

        self.qf_write(w, write_var, write_prd, indent + 2, tag_pred)?;

        writeln!(w, "{nil: >indent$})", nil = "", indent = indent)?;

        Ok(())
    }

    /// Writes a clause without the quantifiers around it.
    fn qf_write<W, WriteVar, WritePrd>(
        &self,
        w: &mut W,
        write_var: WriteVar,
        write_prd: WritePrd,
        original_indent: usize,
        tag_pred: Option<&str>,
    ) -> IoRes<()>
    where
        W: Write,
        WriteVar: Fn(&mut W, &VarInfo) -> IoRes<()>,
        WritePrd: Fn(
            &mut W,
            either::Either<(), usize>,
            PrdIdx,
            &VarTerms,
            Option<&term::Bindings>,
        ) -> IoRes<()>,
    {
        let bindings = self.bindings();
        let bindings = bindings.as_ref();

        let mut indent = original_indent;

        if let Some(bindings) = bindings {
            indent += 2;
            bindings.write_opening(
                w,
                |w, var| write_var(w, &self.vars[var]),
                &" ".repeat(original_indent),
            )?
        }

        write!(
            w,
            "{nil: >indent$}(=>\n{nil: >indent$}  (and\n{nil: >indent$}   ",
            nil = "",
            indent = indent
        )?;

        if self.lhs_term.is_true() {
            write!(w, " true")?
        } else {
            self.lhs_term
                .write_with(w, |w, var| write_var(w, &self.vars[var]), bindings)?
        }

        write!(w, "\n{nil: >indent$}   ", nil = "", indent = indent)?;

        if self.lhs_preds.is_empty() && tag_pred.is_none() {
            write!(w, " true")?
        } else {
            if let Some(tag_pred) = tag_pred {
                write!(w, " {}", tag_pred)?;
            }
            for (idx, app) in self.lhs_preds.iter().enumerate() {
                write!(w, " ")?;
                write_prd(w, either::Right(idx), app.pred, &app.args, bindings)?
            }
        }

        write!(
            w,
            "\n{nil: >indent$}  )\n{nil: >indent$}  ",
            nil = "",
            indent = indent
        )?;

        if let Some((pred, ref args)) = self.rhs {
            // for simplicity...
            let mut new_args = VarMap::new();
            // case where tag-encoding is enabled
            for a in args.iter() {
                new_args.push(term::var(*a, typ::bool()));
            }
            let args = new_args.into();
            write_prd(w, either::Left(()), pred, &args, bindings)?
        } else {
            write!(w, "false")?
        }
        writeln!(w, "\n{nil: >indent$})", nil = "", indent = indent)?;

        if let Some(bindings) = bindings {
            bindings.write_closing(w, &" ".repeat(original_indent))?
        }

        Ok(())
    }
}

pub struct AbsInstance<'a> {
    pub clauses: Vec<AbsClause>,
    pub original: &'a Instance,
    pub preds: Preds,
    log_dir: PathBuf,
}

impl AbsInstance<'_> {
    fn gen_logdir(instance: &Instance) -> Res<PathBuf> {
        let mut log_dir = crate::common::conf.out_dir(instance);
        log_dir.push("absadt");
        mk_dir(&log_dir)?;
        Ok(log_dir)
    }
    pub fn clone_with_clauses(&self, clauses: Vec<AbsClause>, preds: Preds) -> Self {
        Self {
            clauses,
            preds,
            original: self.original,
            log_dir: self.log_dir.clone(),
        }
    }
}

fn gen_lhs_preds(clause: &Clause) -> Vec<PredApp> {
    let mut lhs_preds = Vec::new();
    for (pred, argss) in clause.lhs_preds().iter() {
        for arg in argss.iter() {
            lhs_preds.push(PredApp {
                pred: *pred,
                args: arg.clone(),
            });
        }
    }
    lhs_preds
}

fn handle_query(clause: &Clause) -> AbsClause {
    let vars = clause.vars().clone();
    let lhs_preds = gen_lhs_preds(clause);
    let lhs_term = term::and(clause.lhs_terms().iter().cloned().collect());
    let head = None;
    AbsClause {
        vars,
        rhs: head,
        lhs_preds,
        lhs_term,
    }
}

fn handle_definite(
    original: &Instance,
    clause: &Clause,
    head: PrdIdx,
    rhs_args: &VarTerms,
) -> AbsClause {
    let mut vars = clause.vars().clone();
    let mut lhs_terms = Vec::new();
    let mut args = Vec::new();
    let sig = original.preds()[head].sig();
    debug_assert_eq!(rhs_args.len(), sig.len());
    let mut already_used = HashSet::new();
    for (arg, ty) in rhs_args.iter().zip(sig.iter()) {
        // ... => P(x + 1, ...) is transformed to ... /\ y = x + 1 => P(y, ...)

        match arg.get() {
            // If the argument is a variable that has not appeared so far,
            // then we just reuse it.
            RTerm::Var(_, v) if !already_used.contains(v) => {
                already_used.insert(v);
                args.push(*v);
            }
            _ => {
                let new_var = vars.next_index();
                let info =
                    crate::info::VarInfo::new(format!("arg_{}", new_var), ty.clone(), new_var);
                vars.push(info);
                lhs_terms.push(term::eq(arg.clone(), term::var(new_var, ty.clone())));
                args.push(new_var);
            }
        }
    }

    for t in clause.lhs_terms().iter() {
        lhs_terms.push(t.clone());
    }
    let lhs_term = term::and(lhs_terms);
    let lhs_preds = gen_lhs_preds(clause);

    let head = Some((head, args));

    AbsClause {
        vars,
        rhs: head,
        lhs_preds,
        lhs_term,
    }
}

impl<'a> AbsInstance<'a> {
    pub fn new(original: &'a Instance) -> Res<Self> {
        let mut clauses = Vec::new();
        let mut queries = Vec::new();
        for clause in original.clauses().iter() {
            match clause.rhs() {
                Some((prd, args)) => {
                    clauses.push(handle_definite(original, clause, prd, args));
                }
                None => {
                    queries.push(handle_query(clause));
                }
            }
        }
        for query in queries {
            clauses.push(query);
        }

        let log_dir = Self::gen_logdir(original)?;
        let preds = original.preds().clone();
        Ok(Self {
            clauses,
            preds,
            original,
            log_dir,
        })
    }

    pub fn instance_log_files<S: AsRef<str>>(&self, name: S) -> Res<::std::fs::File> {
        use std::fs::OpenOptions;
        let mut path = self.log_dir.clone();
        path.push(name.as_ref());
        path.set_extension("smt2");
        let file = OpenOptions::new()
            .write(true)
            .truncate(true)
            .create(true)
            .open(&path)
            .chain_err(|| {
                format!(
                    "while creating instance dump file {}",
                    path.to_string_lossy()
                )
            })?;
        Ok(file)
    }

    fn dump_dtype_if_needed<File>(&self, w: &mut File) -> Res<()>
    where
        File: Write,
    {
        fn check(t: &Term) -> bool {
            match t.get() {
                RTerm::Var(typ, _) => typ.is_dtyp(),
                RTerm::Cst(v) => v.typ().is_dtyp(),
                RTerm::CArray { typ, term, .. }
                | RTerm::DTypSlc { typ, term, .. }
                | RTerm::DTypTst { typ, term, .. } => typ.is_dtyp() || check(term),
                RTerm::App { typ, args, .. }
                | RTerm::DTypNew { typ, args, .. }
                | RTerm::Fun { typ, args, .. } => {
                    typ.is_dtyp() || args.iter().any(|arg| check(arg))
                }
            }
        }
        let mut flag = false;
        for clause in &self.clauses {
            if check(&clause.lhs_term) {
                flag = true;
                break;
            }
            for pred in &clause.lhs_preds {
                for arg in pred.args.iter() {
                    if check(arg) {
                        flag = true;
                        break;
                    }
                }
            }
        }
        if flag {
            writeln!(w, "; Datatypes")?;
            dtyp::write_all(w, "")?;
            dtyp::write_constructor_map(w, "; ")?;
            writeln!(w)?;
        }
        Ok(())
    }

    pub fn dump_as_smt2_with_fun<File, Blah, F>(
        &self,
        w: &mut File,
        blah: Blah,
        gen_additional: F,
        encode_tag: bool,
    ) -> Res<()>
    where
        File: Write,
        Blah: AsRef<str>,
        F: Fn(&mut File) -> Res<()>,
    {
        let blah = blah.as_ref();

        for line in blah.lines() {
            writeln!(w, "; {}", line)?
        }
        writeln!(w)?;
        writeln!(w, "(set-logic HORN)")?;
        writeln!(w)?;
        gen_additional(w)?;
        writeln!(w)?;

        self.dump_dtype_if_needed(w)?;

        writeln!(w, "; Functions")?;
        fun::write_all(w, "", true)?;

        writeln!(w)?;

        // what are side clauses?
        // writeln!(w, "; Side-clauses")?;
        // for side_clause in &self.original.get{
        //     side_clause.write(
        //         w,
        //         |w, var_info| write!(w, "{}", var_info.name),
        //         |_, _, _, _| panic!("illegal side-clause: found predicate application(s)"),
        //         true,
        //     )?;
        //     writeln!(w)?;
        // }

        // writeln!(w)?;
        // writeln!(w)?;

        for pred in self.preds.iter() {
            if !pred.is_defined() {
                write!(w, "({}\n  {}\n  (", keywords::cmd::dec_fun, pred.name)?;
                // All predicates take another argument for handling callee
                // positions
                if encode_tag {
                    write!(w, "Int")?;
                }
                for typ in &pred.sig {
                    write!(w, " {}", typ)?
                }
                writeln!(w, " ) Bool\n)")?
            }
        }

        // Append tag predicate for tracking the use of clauses in refutation proofs
        if encode_tag {
            for (clsidx, _) in self.clauses.iter().enumerate() {
                write!(
                    w,
                    "({}\n  {TAG_PRED}{clsidx}\n  () Bool\n)",
                    keywords::cmd::dec_fun
                )?;
                writeln!(w)?;
                write!(w, "({} {TAG_PRED}{clsidx})", keywords::cmd::assert)?;
                writeln!(w, "\n")?;
            }
        }

        for (idx, clause) in self.clauses.iter().enumerate() {
            writeln!(w, "\n; Clause #{}", idx)?;
            let tag_pred = format!("{TAG_PRED}{idx}");

            clause.write(
                w,
                |w, var_info| write!(w, "{}", var_info.name),
                |w, fst, p, args, bindings| {
                    if !args.is_empty() {
                        write!(w, "(")?
                    }
                    w.write_all(self.preds[p].name.as_bytes())?;
                    if encode_tag {
                        match fst {
                            either::Left(()) => write!(w, " {IDX_ARG}")?,
                            either::Right(n) => write!(w, " {n}")?,
                        }
                    }
                    for arg in args.iter() {
                        write!(w, " ")?;
                        arg.write_with(w, |w, var| write!(w, "{}", clause.vars[var]), bindings)?
                    }
                    if !args.is_empty() {
                        write!(w, ")")
                    } else {
                        Ok(())
                    }
                },
                if encode_tag { Some(&tag_pred) } else { None },
                encode_tag,
            )?;
            writeln!(w)?;
            writeln!(w)?
        }

        writeln!(w, "\n(check-sat)")?;

        Ok(())
    }
    pub fn dump_as_smt2<File, Blah>(&self, w: &mut File, blah: Blah, encode_tag: bool) -> Res<()>
    where
        File: Write,
        Blah: AsRef<str>,
    {
        self.dump_as_smt2_with_fun(w, blah, |_| Ok(()), encode_tag)
    }
    pub fn dump_as_smt2_with_option<File, Blah, Options>(
        &self,
        w: &mut File,
        blah: Blah,
        options: Options,
        encode_tag: bool,
    ) -> Res<()>
    where
        File: Write,
        Blah: AsRef<str>,
        Options: AsRef<str>,
    {
        self.dump_as_smt2_with_fun(
            w,
            blah,
            |w| {
                let option = options.as_ref();
                if option != "" {
                    writeln!(w, "{}", option)?;
                }
                Ok(())
            },
            encode_tag,
        )
    }
}

/*** Pre/Post-process for tracking clauses in the resolution proof ***/

/// Data structure for a node in the call tree
pub struct Node {
    /// Name of the predicate
    pub head: String,
    /// Arguments of the predicate application for refutation
    pub args: Vec<hyper_res::V>,
    /// Children of this node in the call-tree
    pub children: Vec<usize>,
    /// Index of the clause in the original CHC
    pub clsidx: usize,
}
impl Node {
    /// Transform hyper_res::Node to Node
    ///
    /// We retrieve the clause index from the encoded-tag predicate.
    /// `cls_map` is a map from node index of the refutation proof to the clause index in the CHC instance.
    fn tr_from_hyper_res(n: &hyper_res::Node, cls_map: &HashMap<usize, usize>) -> Option<Self> {
        let mut children = n.children.clone();
        let idx = n.children.iter().enumerate().find_map(|(i, x)| {
            if cls_map.contains_key(x) {
                Some(i)
            } else {
                None
            }
        })?;
        let cls_id = children.remove(idx);
        let clsidx = *cls_map.get(&cls_id)?;

        let args = n.arguments.clone();
        let node = Self {
            head: n.head.clone(),
            children,
            clsidx,
            args,
        };
        Some(node)
    }
}

pub struct CallTree {
    pub roots: Vec<usize>,
    pub nodes: HashMap<usize, Node>,
}
impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}_{}(", self.head, self.clsidx)?;
        let mut itr = self.args.iter();
        if let Some(arg) = itr.next() {
            write!(f, "{}", arg)?;
        }
        for arg in itr {
            write!(f, ", {}", arg)?;
        }
        write!(f, ")")?;
        //write!(f, ") := ")?;
        //for c in self.children.iter() {
        //    write!(f, "{}, ", c)?;
        //}
        Ok(())
    }
}

impl fmt::Display for CallTree {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, root) in self.roots.iter().enumerate() {
            write!(f, "Tree #{}\n", i)?;
            let mut q = vec![(*root, 0)];
            while let Some((cur, indent)) = q.pop() {
                let n = self.nodes.get(&cur).unwrap();
                for _ in 0..indent {
                    write!(f, "  ")?;
                }
                writeln!(f, "{}: {}", cur, n)?;
                for c in n.children.iter().rev() {
                    q.push((*c, indent + 1));
                }
            }
        }

        Ok(())
    }
}

/// Transform a resolution proof to a call tree
///
/// 1. Find the tag nodes in the refutation tree
/// 2. Create a map from node id of tag nodes to clause index
/// 3. Transform each node
pub fn decode_tag(res: ResolutionProof) -> Res<CallTree> {
    log_debug!("decode_tag");
    log_debug!("{res}");
    // map from node (whose head is tag!X) id to its clause index
    let mut map = HashMap::new();
    for n in res.nodes.iter() {
        if n.head.starts_with("tag!") {
            let clsidx = n.head["tag!".len()..]
                .parse::<usize>()
                .map_err(|_| "invalid tag")?;
            let r = map.insert(n.id, clsidx);
            assert!(r.is_none())
        }
    }

    let mut roots = Vec::new();
    let mut nodes = HashMap::new();
    for n in res.nodes.iter() {
        if n.head.starts_with("tag!") {
            continue;
        }
        let id = n.id;
        match Node::tr_from_hyper_res(n, &map) {
            Some(node) => {
                let r = nodes.insert(id, node);
                assert!(r.is_none())
            }
            None => {
                if roots.len() > 0 || !n.head.starts_with("query!") {
                    // case where there are multiple entries
                    bail!("hyper resolution is ill-structured")
                }
                roots = n.children.iter().copied().collect()
            }
        }
    }
    if roots.len() == 0 {
        roots = res.get_roots().map(|node| node.id).collect();
        assert_eq!(roots.len(), 1);
    }
    assert!(roots.len() > 0);
    Ok(CallTree { roots, nodes })
}

impl super::chc_solver::Instance for AbsInstance<'_> {
    fn dump_as_smt2<File, Option>(&self, w: &mut File, options: Option) -> Res<()>
    where
        File: Write,
        Option: AsRef<str>,
    {
        self.dump_as_smt2_with_option(w, "", options, true)
    }
}

pub struct CEX {
    pub vars: VarInfos,
    pub term: term::Term,
}

impl fmt::Display for CEX {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "forall")?;
        for x in self.vars.iter() {
            write!(f, " v_{}: {},", x.idx, x.typ)?;
        }
        write!(f, ". {}", self.term)
    }
}

impl CEX {
    fn define_consts(&self, solver: &mut Solver<Parser>) -> Res<()> {
        for var in self.vars.iter() {
            let mut varset = VarSet::new();
            varset.insert(var.idx);
            // only declare the variables used in self.term
            if self.term.mentions_one_of(&varset) {
                solver.declare_const(&format!("v_{}", var.idx), &var.typ.to_string())?;
            }
        }
        Ok(())
    }
    pub fn define_assert_with_enc<Approx: Approximation>(
        &self,
        solver: &mut Solver<Parser>,
        encs: &BTreeMap<Typ, Enc<Approx>>,
    ) -> Res<()> {
        self.define_consts(solver)?;

        let enc_ctx = enc::EncodeCtx::new(encs);
        let f = |typ: &Typ, var| match encs.get(&typ) {
            Some(enc) => enc.encode_var_with_rdf(var),
            None => vec![term::var(*var, typ.clone())],
        };
        let terms = enc_ctx.encode(&self.term, &f);

        let t = term::and(terms);

        writeln!(solver, "(assert {})", t)?;
        writeln!(solver)?;

        Ok(())
    }

    pub fn define_assert(&self, solver: &mut Solver<Parser>) -> Res<()> {
        dtyp::write_all(solver, "")?;
        self.define_consts(solver)?;
        writeln!(solver, "(assert {})", self.term)?;
        Ok(())
    }

    /// returns true when it is satisfiable
    pub fn check_sat_opt(&self, solver: &mut Solver<Parser>) -> Res<Option<bool>> {
        solver.reset()?;
        solver.set_option(":timeout", &format!("{}000", CHECK_SAT_TIMEOUT))?;
        self.define_assert(solver)?;
        match solver.check_sat() {
            Ok(true) => Ok(Some(true)),
            Ok(false) => Ok(Some(false)),
            Err(e) => {
                let e: Error = e.into();
                if e.is_timeout() {
                    Ok(None)
                } else {
                    Err(e)
                }
            }
        }
    }
}

impl<'a> AbsInstance<'a> {
    /// Obtain a finite expansion of the original CHC instance along with the resolution proof (call-tree).
    pub fn get_cex(&self, tree: &CallTree) -> CEX {
        fn walk(
            instance: &AbsInstance,
            tree: &CallTree,
            cur: &Node,
            cur_args: VarMap<term::Term>,
            vars: &mut VarInfos,
        ) -> term::Term {
            let clause = &instance.clauses[cur.clsidx];
            let mut args_remap = HashMap::new();
            assert_eq!(clause.lhs_preds.len(), cur.children.len());

            // Introduce fresh variables and rename variables
            let mut rename_map = VarHMap::new();
            for var in clause.vars.iter() {
                let new_idx = vars.next_index();
                let mut new_info = var.clone();
                let old_idx = var.idx;
                new_info.idx = new_idx;
                vars.push(new_info);

                // a bit redundant
                args_remap.insert(old_idx, new_idx);
                rename_map.insert(old_idx, term::var(new_idx, var.typ.clone()));
            }

            let new_lhs_term = clause.lhs_term.subst_total(&rename_map).unwrap().0;
            let mut terms = vec![new_lhs_term];

            for child_idx in cur.children.iter() {
                let next_node = tree.nodes.get(child_idx).unwrap();

                let predidx = next_node.args[0].as_i64().unwrap() as usize;
                let app = &clause.lhs_preds[predidx];

                let args = app
                    .args
                    .iter()
                    .map(|arg| arg.subst_total(&rename_map).unwrap().0)
                    .collect();

                let res = walk(instance, tree, next_node, args, vars);

                terms.push(res);
            }
            let res = term::and(terms);

            match clause.rhs.as_ref() {
                Some(pred) => {
                    let args = &pred.1;

                    // sanity check
                    #[cfg(debug_assertions)]
                    {
                        let cur_pred = pred.0;
                        let node_pred = instance.preds.iter().find(|x| x.name == cur.head).unwrap();
                        assert_eq!(cur_pred, node_pred.idx);
                        assert_eq!(node_pred.sig.len(), cur_args.len());
                    }

                    assert_eq!(cur_args.len(), args.len());
                    let subst_map: VarHMap<_> = args
                        .iter()
                        .map(|x| args_remap.get(x).unwrap().clone())
                        .zip(cur_args.iter().cloned())
                        .collect();

                    res.subst(&subst_map).0
                }
                None => res,
            }
        }

        let mut vars = VarMap::new();
        let mut cexs = Vec::new();
        for root in tree.roots.iter() {
            let node = tree.nodes.get(root).unwrap();
            let term = walk(self, &tree, &node, VarMap::new(), &mut vars);
            cexs.push(term);
        }
        let term = term::or(cexs);
        CEX { vars, term }
    }

    /// Check satisfiability of the query
    /// Returns () when it' sat, and a counterexample when it's unsat
    pub fn check_sat(&self) -> Res<either::Either<(), CallTree>> {
        // since eld seems better, we first try eld with timeout
        let b = super::chc_solver::run_eldarica(self, Some(CHECK_CHC_TIMEOUT))
            .map_err(|e| println!("{}", e))
            .unwrap_or(false);
        if b {
            return Ok(either::Left(()));
        }
        let res = super::chc_solver::run_spacer(self)?;
        match res {
            either::Left(_) => Ok(either::Left(())),
            either::Right(proof) => {
                let tree = decode_tag(proof)?;
                Ok(either::Right(tree))
            }
        }
    }
}

#[test]
fn test_check_sat() {
    // generate a new instance
    // P(0)
    // P(x + 1) => P(x)
    // P(x) => x <= 0

    let mut instance = Instance::new();

    let mut vars = VarInfos::new();
    let x = vars.next_index();
    let info = VarInfo::new("x", typ::int(), x);
    vars.push(info);

    let mut sig = VarMap::new();
    sig.push(typ::int());

    let p = instance.push_pred("P", sig);

    let minus2 = term::cst(val::int(-4));
    let zerot = term::cst(val::int(0));
    let xt = term::var(x, typ::int());
    let x1t = term::add(vec![xt.clone(), term::cst(val::int(1))]);
    let x2t = term::add(vec![xt.clone(), term::cst(val::int(2))]);

    // P(0)
    let mut a1 = VarMap::new();
    a1.push(zerot.clone());
    instance
        .push_new_clause(vars.clone(), vec![], Some((p, a1.into())), "P(0)")
        .unwrap();

    // P(x + 1) => P(x)
    let mut a2 = VarMap::new();
    a2.push(x1t.clone());
    let t1 = term::TTerm::P {
        pred: p,
        args: a2.into(),
    };
    let t2 = t1.clone();

    let t3 = term::TTerm::T(term::le(term::int_var(x), term::int(0)));

    let mut a3 = VarMap::new();
    a3.push(xt.clone());
    instance
        .push_new_clause(
            vars.clone(),
            vec![t3, t1.into()],
            Some((p, a3.clone().into())),
            "P(x+1) => P(x)",
        )
        .unwrap();

    // P(x + 2) => P(x)
    let mut a2 = VarMap::new();
    a2.push(x2t.clone());
    let t1 = term::TTerm::P {
        pred: p,
        args: a2.into(),
    };

    let mut a3 = VarMap::new();
    a3.push(xt.clone());
    let c = instance
        .push_new_clause(
            vars.clone(),
            vec![t1.into(), t2.into()],
            Some((p, a3.clone().into())),
            "P(x+2) => P(x)",
        )
        .unwrap()
        .unwrap();
    let preds = instance[c].lhs_preds();
    for (_, argss) in preds.iter() {
        println!("argss: {:?}", argss);
        for args in argss.iter() {
            println!("args: {:?}", args);
            for arg in args.iter() {
                println!("{:?}", arg);
            }
        }
    }

    // P(x) => x <= -2
    let mut a2 = VarMap::new();
    a2.push(xt.clone());
    let t3 = term::TTerm::T(term::lt(xt.clone(), minus2.clone()));
    let t4 = term::TTerm::P {
        pred: p,
        args: a3.into(),
    };
    instance
        .push_new_clause(vars.clone(), vec![t3, t4], None, "P(x) => x <= 0")
        .unwrap();

    let my_instance = AbsInstance::new(&instance).unwrap();
    let mut file: std::fs::File = my_instance.instance_log_files("hoge").unwrap();
    my_instance.dump_as_smt2(&mut file, "no_def", true).unwrap();

    my_instance.check_sat().unwrap();
}
