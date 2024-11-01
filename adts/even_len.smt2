(set-logic HORN)
(declare-datatypes ((tree 0)) (
   (
      (node (left tree) (right tree)) 
      (leaf))
   )
)

(declare-fun leftlen (tree tree) Bool)

(assert (forall ((x tree) (y tree) ) (=>
  (and (= x leaf) (= y leaf))
  (leftlen x y))))

(assert (forall ((x tree) (x2 tree) (z tree) (x_ tree) (x2_ tree) (z_ tree) ) (=>
  (and 
    (= x (node x2 z))
    (= x_ (node x2_ z_))
    (leftlen x2 x2_)
  )
  (leftlen x x_))
))

(assert (forall ((x tree) ) 
  (=> (leftlen x (node x leaf)) false)
))

(check-sat)
(get-model)
