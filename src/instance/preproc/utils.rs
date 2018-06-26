//! Helper types and functions for preprocessing.

use common::* ;
use var_to::terms::VarTermsSet ;


/// Result of extracting the terms for a predicate application in a clause.
#[derive(Clone, PartialEq, Eq)]
#[allow(dead_code)]
pub enum ExtractRes<T = Vec<TTerm>> {
  /// The clause was found to be trivially true.
  Trivial,
  /// Terms could not be extracted.
  ///
  /// Returned when the variables appearing in the application and the other
  /// variables `others` of the clause are related, or if there is a predicate
  /// application mentioning variables from `others`.
  Failed,
  /// Success, predicate is equivalent to true.
  SuccessTrue,
  /// Success, predicate is equivalent to false.
  SuccessFalse,
  /// Success, predicate is equivalent to some top terms.
  Success(T),
}
impl<T: PartialEq + Eq> ExtractRes<T> {
  /// True if failed.
  pub fn is_failed(& self) -> bool{ * self == ExtractRes::Failed }
}







/// Term extraction context.
pub struct ExtractionCxt {
  /// Map from **clause** variables to **predicate** variables.
  map: VarHMap<Term>,
  /// Quantified variables.
  qvars: VarHMap<Typ>,
  /// Index of the next fresh variable.
  fresh: VarIdx,
}
impl Default for ExtractionCxt {
  fn default() -> Self { Self::new() }
}
impl ExtractionCxt {
  /// Index of the next fresh variable.
  pub fn next_fresh(& mut self) -> VarIdx {
    let fresh = self.fresh ;
    self.fresh.inc() ;
    fresh
  }

  /// Constructor.
  pub fn new() -> Self {
    ExtractionCxt {
      map: VarHMap::with_capacity(11),
      qvars: VarHMap::with_capacity(11),
      fresh: 0.into(),
    }
  }

  /// Creates quantified variables if needed.
  ///
  /// Returns `true` if the process failed.
  pub fn add_qvars(
    & mut self, quantifiers: bool, var_info: & VarInfos,
    app_vars: & mut VarSet, vars: VarSet,
  ) -> bool {
    for var in vars {
      let is_new = app_vars.insert(var) ;

      if is_new {
        if ! quantifiers {
          return true
        }
        let fresh = self.next_fresh() ;
        let _prev = self.qvars.insert(
          fresh, var_info[var].typ.clone()
        ) ;
        debug_assert_eq! { None, _prev }

        log! {
          @6 "adding fresh {} for {}", fresh.default_str(), var_info[var]
        }
        let _prev = self.map.insert(
          var, term::var( fresh, var_info[var].typ.clone() )
        ) ;
        debug_assert_eq! { None, _prev }
      }
    }
    false
  }

  /// Applies a map to some predicate applications, generating quantifiers if
  /// necessary and `quantifiers` is true.
  ///
  /// Returns `None` on failure. Failure happens when some quantifiers are
  /// needed but `quantifiers` is false.
  fn args_of_pred_app(
    & mut self,
    quantifiers: bool, var_info: & VarInfos,
    args: & VarTerms, app_vars: & mut VarSet,
  ) -> Res< TExtractRes<VarTerms> > {
    log! { @6 "args_of_pred_app ({})", quantifiers }
    let mut nu_args = VarMap::with_capacity( args.len() ) ;
    for arg in args.iter() {
      let abort = self.add_qvars(
        quantifiers, var_info, app_vars, term::vars(arg)
      ) ;
      if abort {
        return Ok( TExtractRes::Failed )
      }

      if let Some((nu_arg, _)) = arg.subst_total(& self.map) {
        nu_args.push(nu_arg)
      } else {
        bail!("unreachable, substitution was not total")
      }
    }
    Ok( TExtractRes::Success( nu_args.into() ) )
  }



  /// Applies a map to some predicate applications, generating quantifiers if
  /// necessary and `quantifiers` is true.
  ///
  /// The `pred` argument is a special predicate that will be skipped when
  /// handling `src`, but it's arguments will be returned.
  fn terms_of_pred_apps<'a>(
    & mut self,
    quantifiers: bool, var_info: & VarInfos,
    src: & 'a PredApps, tgt: & mut TTermSet,
    pred: PrdIdx, app_vars: & mut VarSet,
  ) -> Res< TExtractRes< Option<& 'a VarTermsSet > > > {
    log! { @6 "terms_of_pred_apps" }
    let mut res = None ;
    for (prd, argss) in src {

      let prd = * prd ;
      if prd == pred {
        res = Some(argss) ;
        continue
      }

      for args in argss {
        match self.args_of_pred_app(
          quantifiers, var_info, args, app_vars
        ) ? {
          TExtractRes::Success(nu_args) => {
            tgt.insert_pred_app(prd, nu_args) ;
            ()
          },
          TExtractRes::Failed => {
            log! { @6 "failed to extract argument {}", args }
            return Ok(TExtractRes::Failed)
          },
        }
      }
    }
    Ok( TExtractRes::Success(res) )
  }


  /// Applies a map to some terms, generating quantifiers if necessary and
  /// `quantifiers` is true.
  ///
  /// Argument `even_if_disjoint` forces to add terms even if its variables
  /// are disjoint from `app_vars`.
  ///
  /// Returns `true` if one of the `src` terms is false (think `is_trivial`).
  fn terms_of_terms<'a, TermIter, Terms, F>(
    & mut self,
    quantifiers: bool, var_info: & VarInfos,
    src: Terms, tgt: & mut TermSet,
    app_vars: & mut VarSet, even_if_disjoint: bool, f: F
  ) -> Res< TExtractRes<bool> >
  where
  TermIter: Iterator<Item = & 'a Term> + ExactSizeIterator,
  Terms: IntoIterator<IntoIter = TermIter, Item = & 'a Term>,
  F: Fn(Term) -> Term {
    log! { @4 "terms_of_terms" }

    // Finds terms which variables are related to the ones from the predicate
    // applications.
    let src = src.into_iter() ;

    // The terms we're currently looking at.
    let mut lhs_terms_vec: Vec<_> = Vec::with_capacity( src.len() ) ;
    for term in src {
      match term.bool() {
        Some(true) => (),
        Some(false) => return Ok( TExtractRes::Success(true) ),
        _ => lhs_terms_vec.push(term),
      }
    }
    // Terms which variables are disjoint from `app_vars` **for now**. This
    // might change as we generate quantified variables.
    let mut postponed: Vec<_> = Vec::with_capacity( lhs_terms_vec.len() ) ;


    // A fixed point is reached when we go through the terms in `lhs_terms_vec`
    // and don't generate quantified variables.
    loop {
      let mut fixed_point = true ;

      for term in lhs_terms_vec.drain(0..) {
        log! { @6 "{}", term.to_string_info(var_info) ? }
        let vars = term::vars(term) ;

        if app_vars.len() == var_info.len()
        || vars.is_subset(& app_vars) {
          let term = if let Some((term, _)) = term.subst_total(& self.map) {
            term
          } else {
            bail!("[unreachable] failure during total substitution (1)")
          } ;
          log! { @6 "      sub {}", term }
          tgt.insert( f(term) ) ;

        } else if ! even_if_disjoint && vars.is_disjoint(& app_vars) {
          log! { @6 "      disjoint" }
          postponed.push(term)

        } else {
          // The term mentions variables from `app_vars` and other variables.
          // We generate quantified variables to account for them and
          // invalidate `fixed_point` since terms that were previously disjoint
          // might now intersect.
          fixed_point = false ;
          let abort = self.add_qvars(
            quantifiers, var_info, app_vars, vars
          ) ;
          if abort {
            return Ok( TExtractRes::Failed )
          }

          let term = if let Some((term, _)) = term.subst_total(& self.map) {
            term
          } else {
            bail!("[unreachable] failure during total substitution (2)")
          } ;
          tgt.insert( f(term) ) ;
        }

      }

      if fixed_point || postponed.is_empty() {
        break
      } else {
        // Iterating over posponed terms next.
        ::std::mem::swap(
          & mut lhs_terms_vec, & mut postponed
        )
      }

    }    

    Ok( TExtractRes::Success(false) )
  }



  /// Given a predicate application, returns the constraints on the input and a
  /// map from the variables used in the arguments to the variables of the
  /// predicate. Also returns the set of variables appearing in the
  /// application.
  ///
  /// # Assumptions
  ///
  /// - `self.map.is_empty()`
  ///
  /// # TODO
  ///
  /// - more doc with examples
  pub fn terms_of_app(
    & mut self,
    quantifiers: bool, var_info: & VarInfos,
    instance: & Instance, pred: PrdIdx, args: & VarTerms,
  ) -> Res<
    Option<(TermSet, VarSet)>
  > {
    debug_assert! { self.map.is_empty() }

    let mut app_vars = VarSet::with_capacity( instance[pred].sig.len() ) ;
    let mut terms = TermSet::with_capacity( 7 ) ;

    // Will store the arguments that are not a variable or a constant.
    let mut postponed = Vec::with_capacity( args.len() ) ;

    for (index, arg) in args.index_iter() {
      if let Some(var) = arg.var_idx() {
        let _ = app_vars.insert(var) ;
        if let Some(pre) = self.map.insert(
          var, term::var( index, arg.typ() )
        ) {
          terms.insert(
            term::eq( term::var(index, arg.typ()), pre )
          ) ;
        }
      } else {
        match arg.as_val().to_term() {
          Some(trm) => {
            debug_assert_eq! { trm.typ(), arg.typ() }
            let var = term::var(index, trm.typ()) ;
            terms.insert(
              term::eq(var, trm)
            ) ;
          },
          None => {
            postponed.push( (index, arg) )
          },
        }
      }
    }

    for (var, arg) in postponed {
      if let Some( (term, _) ) = arg.subst_total(& self.map) {
        terms.insert(
          term::eq(term::var(var, arg.typ()), term)
        ) ;
      } else if let Some((v, inverted)) = arg.invert_var(var, arg.typ()) {
        let _prev = self.map.insert(v, inverted) ;
        debug_assert_eq!( _prev, None ) ;
        let is_new = app_vars.insert(v) ;
        debug_assert!( is_new )
      } else if let TExtractRes::Failed = self.terms_of_terms(
        quantifiers, var_info, Some(arg), & mut terms,
        & mut app_vars, true, |term| term::eq(
          term::var(var, term.typ()), term
        )
      ) ? {
        return Ok(None)
      }
    }

    Ok( Some( (terms, app_vars) ) )
  }




  /// Retrieves the internal quantified variables.
  pub fn get_qvars(& mut self) -> VarHMap<Typ> {
    self.qvars.shrink_to_fit() ;
    ::std::mem::replace(& mut self.qvars, VarHMap::with_capacity(11))
  }



  /// Returns the weakest predicate `p` such that `(p args) /\ lhs_terms /\
  /// {lhs_preds \ (p args)} => rhs`.
  ///
  /// Quantified variables are understood as universally quantified.
  ///
  /// The result is `(pred_app, pred_apps, terms)` which semantics is `pred_app
  /// \/ (not /\ tterms) \/ (not /\ pred_apps)`.
  pub fn terms_of_lhs_app(
    & mut self,
    quantifiers: bool, instance: & Instance, var_info: & VarInfos,
    lhs_terms: & TermSet, lhs_preds: & PredApps,
    rhs: Option<(PrdIdx, & VarTerms)>,
    pred: PrdIdx, args: & VarTerms,
  ) -> Res<
    ExtractRes<(Quantfed, Option<PredApp>, TTermSet)>
  > {
    log!{ @4
      "terms_of_lhs_app on {} {} ({})", instance[pred], args, quantifiers
    }

    // Index of the first quantified variable: fresh for `pred`'s variables.
    self.fresh = instance.original_sig_of(pred).next_index() ;
    self.map.clear() ;

    log!{ @5 "extracting application's terms" }

    let (
      terms, mut app_vars
    ) = if let Some(res) = self.terms_of_app(
      quantifiers, var_info, instance, pred, args
    ) ? {
      res
    } else {
      log! { @5 "failed to extract terms of application" }
      return Ok(ExtractRes::Failed)
    } ;

    if_log! { @5
      log! { @5 "terms:" }
      for term in & terms {
        log!{ @5 "- {}", term }
      }
      log! { @5 "map:" }
      for (var, term) in & self.map {
        log! { @5 "- v_{} -> {}", var, term }
      }
      log! { @5
        "working on lhs predicate applications ({})", lhs_preds.len()
      }
    }

    let mut tterms = TTermSet::of_terms(terms, lhs_preds.len()) ;

    // Predicate applications need to be in the resulting term. Depending on
    // the definition they end up having, the constraint might be trivial.
    match self.terms_of_pred_apps(
      quantifiers, var_info, lhs_preds, & mut tterms, pred, & mut app_vars
    ) ? {
      TExtractRes::Success( Some(pred_argss) ) => match pred_argss.len() {
        1 => (),
        len => bail!(
          "illegal call to `terms_of_lhs_app`, \
          predicate {} is applied {} time(s), expected 1",
          instance[pred], len
        ),
      },
      TExtractRes::Success(None) => (),
      TExtractRes::Failed => {
        log!{ @5 "qualifiers required for lhs pred apps, failing" }
        return Ok( ExtractRes::Failed )
      },
    }

    let pred_app = if let Some((pred, args)) = rhs {
      log! { @5
        "working on rhs predicate application"
      }
      if let TExtractRes::Success(nu_args) = self.args_of_pred_app(
        quantifiers, var_info, args, & mut app_vars,
      ) ? {
        Some((pred, nu_args))
      } else {
        log! { @5 "qualifiers required for rhs pred app, failing" }
        return Ok( ExtractRes::Failed )
      }
    } else {
      log! { @5 "no rhs predicate application" }
      None
    } ;

    log! { @5
      "working on lhs terms ({})", lhs_terms.len()
    }

    if let TExtractRes::Success(trivial) = self.terms_of_terms(
      quantifiers, var_info, lhs_terms, tterms.terms_mut(),
      & mut app_vars, false, identity
    ) ? {
      if trivial { return Ok( ExtractRes::Trivial ) }
    } else {
      log!{ @5 "qualifiers required for lhs terms, failing" }
      return Ok( ExtractRes::Failed )
    }

    debug_assert! { quantifiers || self.qvars.is_empty() }

    if pred_app.is_none() && tterms.is_empty() {
      Ok( ExtractRes::SuccessFalse )
    } else {
      let qvars = self.get_qvars() ;
      Ok(
        ExtractRes::Success( (qvars, pred_app, tterms) )
      )
    }
  }


  /// Returns the weakest predicate `p` such that `lhs_terms /\ lhs_preds => (p
  /// args)`.
  ///
  /// Quantified variables are understood as existentially quantified.
  ///
  /// The result is `(pred_apps, terms)` which semantics is `pred_app /\
  /// tterms`.
  pub fn terms_of_rhs_app(
    & mut self,
    quantifiers: bool, instance: & Instance, var_info: & VarInfos,
    lhs_terms: & TermSet, lhs_preds: & PredApps,
    pred: PrdIdx, args: & VarTerms,
  ) -> Res< ExtractRes<(Quantfed, TTermSet)> > {
    log! { @4
      "terms of rhs app on {} {} ({})", instance[pred], args, quantifiers
    }

    // Index of the first quantified variable: fresh for `pred`'s variables.
    self.fresh = instance.original_sig_of(pred).next_index() ;
    self.map.clear() ;

    log!{ @5 "extracting application's terms" }

    let (
      terms, mut app_vars
    ) = if let Some(res) = self.terms_of_app(
      quantifiers, var_info, instance, pred, args
    ) ? {
      res
    } else {
      log! { @5 "could not extract terms of app" }
      return Ok(ExtractRes::Failed)
    } ;

    if_log! { @5
      log! { @5 "terms:" }
      for term in & terms {
        log! { @5 "- {}", term }
      }
      log! { @5 "map:" }
      for (var, term) in & self.map {
        log! { @5 "- v_{} -> {}", var, term }
      }
    }

    log! { @5
      "working on lhs predicate applications ({})", lhs_preds.len()
    }

    let mut tterms = TTermSet::of_terms(terms, lhs_preds.len()) ;

    // Predicate applications need to be in the resulting term. Depending on
    // the definition they end up having, the constraint might be trivial.
    match self.terms_of_pred_apps(
      quantifiers, var_info, lhs_preds, & mut tterms, pred, & mut app_vars
    ) ? {
      TExtractRes::Success( Some(pred_argss) ) => if ! pred_argss.is_empty() {
        bail!(
          "illegal call to `terms_of_rhs_app`, \
          predicate {} appears in the lhs",
          instance[pred]
        )
      },
      TExtractRes::Success(None) => (),
      TExtractRes::Failed => {
        log! { @5
          "could not extract terms of predicate app ({})", instance[pred]
        }
        return Ok( ExtractRes::Failed )
      },
    }

    log! { @5
      "working on lhs terms ({})", lhs_terms.len()
    }

    if let TExtractRes::Success(trivial) = self.terms_of_terms(
      quantifiers, var_info, lhs_terms, tterms.terms_mut(),
      & mut app_vars, false, identity
    ) ? {
      if trivial { return Ok( ExtractRes::Trivial ) }
    } else {
      log_debug! { "  could not extract terms of terms" }
      return Ok( ExtractRes::Failed )
    }

    debug_assert! { quantifiers || self.qvars.is_empty() }

    if tterms.is_empty() {
      Ok(ExtractRes::SuccessTrue)
    } else {
      let qvars = self.get_qvars() ;
      Ok(
        ExtractRes::Success( (qvars, tterms) )
      )
    }
  }
}




/// Results of term extraction.
pub enum TExtractRes<T> {
  /// Success.
  Success(T),
  /// Failure: need qualifiers.
  Failed,
}
