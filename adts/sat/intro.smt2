(set-logic HORN)

(declare-datatypes ((nat 0)) (
  (
    z
    (s (tail nat))
  )
 )
)

(declare-fun plus (nat nat nat) Bool)
(declare-fun lt (nat nat) Bool)

(assert (forall ((m nat))
  (=> true (plus m z m))
))

(assert (forall ((m nat) (n nat) (r nat))
  (=> (plus m n r) (plus m (s n) (s r)))
))

(assert (forall ((n nat))
  (=> true (lt z (s n)))
))

(assert (forall ((m nat) (n nat))
  (=> (lt m n) (lt (s m) (s n)))
))

(assert (forall ((m nat) (n nat) (r nat))
  (=> (and (plus m n r) (lt r m)) false)
))

(check-sat)


