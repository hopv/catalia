(set-logic HORN)

(declare-datatypes ((LstCex 1)) (
    (par (T) (
      nilCex (consCex (headCex T) (tailCex (LstCex T))))
    )
) )


(declare-fun create_list (Int (LstCex Int)) Bool)
(declare-fun len ((LstCex Int) Int) Bool)


(assert (forall ((n Int) (l (LstCex Int)))
    (=> (<= n 0) (create_list n nilCex))))

(assert (forall ((n Int) (l (LstCex Int)) (m Int) (k (LstCex Int)))
    (=> (and (> n 0) (create_list (- n 1) k) (= l (consCex 1 k)))
        (create_list n l)
    )
  )
)

(assert (forall ((v Int)(l2 (LstCex Int)) (l (LstCex Int)) (r Int))
    (=>  true
        (len nilCex 0)
    )
))

(assert (forall ((l2 (LstCex Int)) (v Int) (l (LstCex Int)) (r Int))
    (=> (and

        (= l (consCex v l2))
        (len l2 r))
        (len l (+ r 1))
    )
))

(assert (forall ((n Int) (l (LstCex Int)) (r Int))
    (=> (and (> n 0) (len l r) (create_list n l) )
      (= r n))
  )
)

(check-sat)
(get-model)
