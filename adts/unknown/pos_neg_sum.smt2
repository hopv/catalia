; Example by Takashi Nakayama
(set-logic HORN)

(declare-datatypes ((Lst 1)) (
    (par (T) (
      nil (cons (head T) (tail (Lst T))))
    )
) )


(declare-fun sum_even_odd ((Lst Int) Int Int) Bool)
(declare-fun sum_odd_even ((Lst Int) Int Int) Bool)
(declare-fun gen ((Lst Int) Int) Bool)

(assert (forall ((dummy Int)) (=> true (sum_even_odd nil 0 0))))

(assert (forall ((x Int) (m Int) (n Int) (l (Lst Int))) 
  (=> 
  (sum_odd_even l m n)
  (sum_even_odd (cons x l) (+ x m ) n)
  )
))

(assert (forall ((x Int) (m Int) (n Int) (l (Lst Int))) 
  (=> 
  (sum_even_odd l m n)
  (sum_odd_even (cons x l) m (+ x n))
  )
))

; gen(nil, 0)
(assert (forall ((dummy Int)) (=> true (gen nil 0))))

; gen (cons x (cons y l), n) <= x >= 0, y <= 0, gen (l, (n -1))
(assert (forall ((n Int) (y Int) (x Int) (l (Lst Int)))
  (=> 
    (and (gen l (- n 1)) (>= x 0) (<= y 0))
    (gen (cons x (cons y l)) n)
  )
)) 

(assert (forall ((x Int) (m Int) (n Int) (l (Lst Int))) 
  (=> 
  (and 
    (sum_even_odd l m n)
    (gen l x)
    (>= x 0)
  )
  (and 
    (>= m 0)
    (<= n 0)
  )
  )
))
(check-sat)
