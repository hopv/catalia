;; Test file for CVC5 with ADTs (Algebraic Data Types)
;; This tests ADT + LIA queries

(set-logic HORN)

;; Define a simple list datatype
(declare-datatypes ((IntList 0))
  (((nil)
    (cons (head Int) (tail IntList)))))

;; Declare a function that computes list length
(declare-fun len (IntList) Int)

;; Base case: length of nil is 0
(assert (= (len nil) 0))

;; Recursive case: length of cons is 1 + length of tail
(assert (forall ((h Int) (t IntList))
  (= (len (cons h t)) (+ 1 (len t)))))

;; Declare an invariant predicate
(declare-fun inv (IntList) Bool)

;; Initial: empty list
(assert (inv nil))

;; Transition: can add elements
(assert (forall ((lst IntList) (x Int))
  (=> (inv lst) (inv (cons x lst)))))

;; Safety: length is always non-negative
(assert (forall ((lst IntList))
  (=> (inv lst) (>= (len lst) 0))))

(check-sat)
