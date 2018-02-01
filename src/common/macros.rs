//! Macros.


/// Wraps stuff in a block, usually to please borrow-checking.
macro_rules! scoped {
  ($($tokens:tt)*) => ({
    $($tokens)*
  })
}

/// Chains some errors and bails.
macro_rules! err_chain {
  ($head:expr $(=> $tail:expr)*) => ({
    let mut err: Error = $head.into() ;
    $(
      err = err.chain_err(|| $tail) ;
    )*
    bail!(err)
  })
}


/// In verbose mode, same as `println` but with a "; " prefix.
macro_rules! info {
  ( $( $str:expr $(, $args:expr)* $(,)* );* ) => (
    if ::common::conf.verb.verbose() {
      $(
        for line in format!($str $(, $args)*).lines() {
          println!("; {}", line)
        }
      )*
      ()
    }
  ) ;
}
/// In debug mode, same as `println` but with a "; " prefix.
macro_rules! debug {
  ( $( $str:expr $(, $args:expr)* $(,)* );* ) => (
    if ::common::conf.verb.debug() {
      $(
        for line in format!($str $(, $args)*).lines() {
          println!("; {}", line)
        }
      )*
      ()
    }
  ) ;
}
/// Formats a warning.
macro_rules! warn {
  ( $( $str:expr $(, $args:expr)* $(,)* );* ) => ({
    println!(
      "; {}", conf.sad("|===| Warning:")
    ) ;
    $(
      print!("; {} ", conf.sad("|")) ;
      println!( $str $(, $args)* ) ;
    )*
    println!("{}", conf.sad("; |===|"))
  }) ;
}



/// `Int` printer.
macro_rules! int_to_smt {
  ($writer:expr, $i:expr) => (
    if $i.is_negative() {
      write!($writer, "(- {})", - $i)
    } else {
      write!($writer, "{}", $i)
    }
  )
}
/// `Rat` printer.
macro_rules! rat_to_smt {
  ($writer:expr, $r:expr) => ({
    let (num, den) = ( $r.numer(), $r.denom() ) ;
    debug_assert!( ! den.is_negative() ) ;
    if ! num.is_negative() {
      write!($writer, "(/ {} {})", num, den)
    } else {
      write!($writer, "(- (/ {} {}))", - num, den)
    }
  })
}


/// Does something if not in bench mode.
#[macro_export]
#[cfg(not (feature = "bench") )]
macro_rules! if_not_bench {
  ( then { $($then:tt)* } else { $($else:tt)* } ) => (
    $($then)*
  ) ;
  ($($blah:tt)*) => ($($blah)*) ;
}
#[cfg(feature = "bench")]
macro_rules! if_not_bench {
  ( then { $($then:tt)* } else { $($else:tt)* } ) => (
    $($else)*
  ) ;
  ($($blah:tt)*) => (()) ;
}


/// Guards something by an `if conf.verbose()`. Inactive in bench mode.
#[macro_export]
#[cfg(not(feature = "bench"))]
macro_rules! if_verb {
  ($($blah:tt)*) => (
    if conf.verbose() {
      $($blah)*
    }
  ) ;
}
#[cfg(feature = "bench")]
macro_rules! if_verb {
  ($($blah:tt)*) => (()) ;
}


/// Logs at info level using `info!`. Inactive in bench mode.
#[cfg(feature = "bench")]
macro_rules! log_info {
  ($($tt:tt)*) => (()) ;
}
#[cfg(not(feature = "bench"))]
macro_rules! log_info {
  ($($tt:tt)*) => ( info!{$($tt)*} ) ;
}


/// Logs at debug level using `debug!`. Inactive in bench mode.
#[cfg( feature = "bench" )]
macro_rules! log_debug {
  ($($tt:tt)*) => (()) ;
}
#[cfg( not(feature = "bench") )]
macro_rules! log_debug {
  ($($tt:tt)*) => ( debug!{$($tt)*} ) ;
}


/// Does something if in debug mode.
#[macro_export]
#[cfg( not(feature = "bench") )]
macro_rules! if_debug {
  ( then { $($then:tt)* } else { $($else:tt)* } ) => (
    $($then)*
  ) ;
  ($($blah:tt)*) => (
    if conf.debug() {
      $($blah)*
    }
  ) ;
}
#[cfg(feature = "bench")]
#[allow(unused_macros)]
macro_rules! if_debug {
  ( then { $($then:tt)* } else { $($else:tt)* } ) => (
    $($else)*
  ) ;
  ($($blah:tt)*) => (()) ;
}


/// Profiling macro.
///
/// If passed `self`, assumes `self` has a `_profiler` field.
#[macro_export]
#[cfg( not(feature = "bench") )]
macro_rules! profile {
  ( | $stuff:ident $(. $prof:ident)* |
    wrap $b:block $( $scope:expr ),+ $(,)*
  ) => ({
    profile! { | $stuff $(. $prof)* | tick $($scope),+ }
    let res = $b ;
    profile! { | $stuff $(. $prof)* | mark $($scope),+ }
    res
  }) ;
  ( | $stuff:ident $(. $prof:ident)* | $stat:expr => add $e:expr ) => (
    $stuff$(.$prof)*.stat_do( $stat, |val| val + $e )
  ) ;
  ( | $stuff:ident $(. $prof:ident)* |
    $meth:ident $( $scope:expr ),+ $(,)*
  ) => (
    $stuff$(.$prof)*.$meth(
      vec![ $($scope),+ ]
    )
  ) ;
  ( $slf:ident wrap $b:block $( $scope:expr ),+ $(,)* ) => ({
    let prof = & $slf._profiler ;
    profile! { |prof| wrap $b $($scope),+ }
  }) ;
  ( $slf:ident $stat:expr => add $e:expr ) => ({
    let prof = & $slf._profiler ;
    profile!{ |prof| $stat => add $e }
  }) ;
  ( $slf:ident $meth:ident $( $scope:expr ),+ $(,)* ) => ({
    let prof = & $slf._profiler ;
    profile!{ |prof| $meth $($scope),+ }
  }) ;
}
#[cfg(feature = "bench")]
macro_rules! profile {
  ( | $stuff:ident $(. $prof:ident)* |
    wrap $b:block $( $scope:expr ),+ $(,)*
  ) => ($b) ;
  ( $slf:ident
    wrap $b:block $( $scope:expr ),+ $(,)*
  ) => ($b) ;
  ( $($stuff:tt)* ) => ( () ) ;
}


/// Messaging macro, compiled to nothing in `release`.
#[macro_export]
#[cfg( feature = "bench" )]
macro_rules! msg {
  ( $($tt:tt)* ) => (()) ;
}
#[cfg( not(feature = "bench") )]
macro_rules! msg {
  ( debug $slf:expr => $($tt:tt)* ) => (
    if conf.debug() {
      msg!( $slf => $($tt)* )
    } else { true }
  ) ;
  ( $core:expr => $e:expr ) => (
    if conf.verbose() {
      $core.msg($e)
    } else { true }
  ) ;
  ( $slf:expr => $($tt:tt)* ) => (
    if conf.verbose() {
      msg!{ $slf => format!( $($tt)* ) }
    } else { true }
  ) ;
}


/// Yields the value if the type (int or bool) matches, otherwise
/// `return`s `Ok(Val::N)`.
///
/// ```rust
/// use hoice::term::Val ;
/// use hoice::errors ;
///
/// fn int(val: Val) -> Res<Val> {
///   Ok( try_val!{ int val } )
/// }
/// fn bool(val: Val) -> Res<Val> {
///   Ok( try_val!{ bool val } )
/// }
///
/// let none = Val::N ;
///
/// let val: Val = 7.into() ;
/// assert_eq!{ int( val.clone() ), val }
/// assert_eq!{ bool( val.clone() ), none }
///
/// let val: Val = false.into() ;
/// assert_eq!{ int( val.clone() ), none }
/// assert_eq!{ bool( val.clone() ), val }
///
/// assert_eq!{ int( none.clone() ), none }
/// assert_eq!{ bool( none.clone() ), none }
/// ```
macro_rules! try_val {
  (int $e:expr) => (
    if let Some(i) = $e.to_int()? { i } else {
      return Ok( Val::N )
    }
  ) ;
  (bool $e:expr) => (
    if let Some(b) = $e.to_bool()? { b } else {
      return Ok( Val::N )
    }
  ) ;
}


/// Dumps an instance if the `PreprocConf` flag says so.
macro_rules! preproc_dump {
  ($instance:expr => $file:expr, $blah:expr) => (
    if let Some(mut file) = conf.preproc.log_file($file) ? {
      $instance.dump_as_smt2(& mut file, $blah)
    } else { Ok(()) }
  ) ;
}



/// Test macros
#[cfg(test)]
#[macro_use]
mod test {

  /// Turns a sequence of values into a `Cex` (`VarMap<Val>`).
  #[macro_export]
  macro_rules! model {
    ( $($values:expr),* ) => (
      $crate::common::VarMap::of(
        vec![ $( $values.into() ),* ]
      )
    ) ;
  }

  /// Checks that the result of an evaluation yields the correct value.
  ///
  /// Prints information before the check.
  #[macro_export]
  macro_rules! assert_eval {
    ( int $model:expr => $expr:expr, $value:expr ) => ({
      let res = $expr.eval(& $model).unwrap().to_int().unwrap().unwrap() ;
      println!(
        "{} evaluated with {} is {}, expecting {}", $expr, $model, res, $value
      ) ;
      assert_eq!( res, $value.into() )
    }) ;
    ( bool $model:expr => $expr:expr ) => ({
      let res = $expr.eval(& $model).unwrap().to_bool().unwrap().unwrap() ;
      println!(
        "{} evaluated with {} is {}, expecting true", $expr, $model, res
      ) ;
      assert!( res )
    }) ;
    ( bool not $model:expr => $expr:expr ) => ({
      let res = $expr.eval(& $model).unwrap().to_bool().unwrap().unwrap() ;
      println!(
        "{} evaluated with {} is {}, expecting false", $expr, $model, res
      ) ;
      assert!( ! res )
    }) ;
  }
}