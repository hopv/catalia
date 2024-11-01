(set-logic HORN)

(declare-datatypes ((Lst 1)) (
    (par (T) (
      nil (cons (head T) (tail (Lst T))))
    )
) )


(declare-fun create_list (Int (Lst Int)) Bool)
(declare-fun len ((Lst Int) Int) Bool)


(assert (forall ((n Int) (l (Lst Int)))
    (=> (<= n 0) (create_list n nil))))

(assert (forall ((n Int) (l (Lst Int)) (m Int) (k (Lst Int)))
    (=> (and (> n 0) (create_list (- n 1) k) (= l (cons 1 k)))
        (create_list n l)
    )
  )
)

(assert (forall ((v Int)(l2 (Lst Int)) (l (Lst Int)) (r Int))
    (=>  true
        (len nil 0)
    )
))

(assert (forall ((l2 (Lst Int)) (v Int) (l (Lst Int)) (r Int))
    (=> (and 
        
        (= l (cons v l2))
        (len l2 r))
        (len l (+ r 1))
    )
))

(assert (forall ((n Int) (l (Lst Int)) (r Int))
    (=> (and (> n 0) (len l r) (create_list n l) )
      (= r n))
  )
)

(check-sat)
(get-model)
