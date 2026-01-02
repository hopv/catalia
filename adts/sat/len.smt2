
(set-logic HORN)

(declare-datatypes ((Lst 1)) (
    (par (T) (
      nil (cons (head T) (tail (Lst T))))
    )
) )


(declare-fun check ((Lst Int) (Lst Int)) Bool)


(assert (forall ((l (Lst Int)) (r (Lst Int))(l2 (Lst Int)) (r2 (Lst Int)) (x Int) (y Int))
    (=> (and (= l (cons x l2)) (= r (cons y r2)) (check l2 r2))
      (check l r))))
(assert (forall ((dummy Int)) (check nil nil)))

(assert (forall ((l (Lst Int)))
  (=> (check l (cons 1 l)) false)))

(check-sat)
