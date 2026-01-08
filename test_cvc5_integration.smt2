;; Test file for CVC5 integration with Catalia
;; This file tests basic NIA (Non-linear Integer Arithmetic) queries

(set-logic HORN)

(declare-fun inv (Int Int) Bool)

;; Initial state: x = 0, y = 0
(assert (inv 0 0))

;; Transition: x' = x + 1, y' = y + x
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int))
  (=> (and (inv x y) (= x1 (+ x 1)) (= y1 (+ y x)))
      (inv x1 y1))))

;; Safety property: y >= 0 (should be safe)
(assert (forall ((x Int) (y Int))
  (=> (inv x y) (>= y 0))))

(check-sat)
