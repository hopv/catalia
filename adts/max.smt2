(set-logic HORN)

(declare-datatypes ((LstInt 0)) (((cons (headlistOfInt Int) (taillistOfInt LstInt)) (nil))))

(declare-fun leq (LstInt Int) Bool)
(declare-fun nleq (LstInt Int) Bool)

(assert (forall ((y Int))
	(=> true (leq nil y))))

(assert (forall ((x Int) (y Int) (l LstInt))
	(=> (and (<= x y) (leq l y)) (leq (cons x l) y))))

(assert (forall ((x Int) (y Int) (l LstInt))
	(=> (> x y) (nleq (cons x l) y))))

(assert (forall ((x Int) (y Int) (l LstInt))
	(=> (nleq l y) (nleq (cons x l) y))))

(assert (forall ((x Int) (l LstInt))
	(=> (and (nleq l x) (leq l x)) false)))

(check-sat)
(exit)
