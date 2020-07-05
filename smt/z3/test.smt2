; this file is a collection of small examples
; each example is wrapped in a push/pop pair that creates a new scope

(push)
(declare-const a String)
(assert (= a "foo"))
(check-sat)
(get-model)
(pop)

(push)
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (= (not(and a b)) (or (not a)(not b))))
(check-sat)
(get-model)
(pop)

(push)
(declare-const x Int)
(declare-const y Int)
(simplify (* (+ x y 1 2) (+ y x x x x)))
(pop)

(push)
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)
(define-fun conjecture () Bool
    (=> (and (=> p q) (=> q r))
        (=> p r)))
(assert (not conjecture))
(check-sat)
(pop)


; This example uses a/b variables, since the example is in a new scope this is
; fine. If it were not a new scope, then the redefinition would trigger an error.

(push)
(declare-const a Bool)
(declare-const b Bool)
(define-fun demorgan () Bool
    (= (and a b) (not (or (not a) (not b)))))
; we proove the negative is unsatisfiable
(assert (not demorgan))
(check-sat)
(pop)


(push)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Real)
(declare-const e Real)
(assert (> a (+ b 2)))
(assert (= a (+ (* 2 c) 10)))
(assert (<= (+ c b) 1000))
(assert (>= d e))
(maximize b)
(check-sat)
(get-model)
(get-objectives)
(pop)

(push)
(declare-const a (Array Int Int))
(declare-const i Int)
(assert (= (select a 9) 42))
(assert (= (select a 2) 8))
(assert (< (select a i) 10))
(check-sat)
(get-model)
(pop)

(reset)
(set-option :produce-proofs true)
(declare-const a Int)
(declare-fun f (Int Bool) Int)
(assert (> a 10))
(assert (< (f a true) 100))
(check-sat)
(get-model)
(get-proof)

(define-sort Set (T) (Array T Bool))
(define-sort IList () (List Int))
(define-sort List-Set (T) (Array (List T) Bool))
(define-sort I () Int)

(declare-const s1 (Set I))
(declare-const s2 (List-Set Int))
(declare-const a I)
(declare-const l IList)

(assert (= (select s1 a) true))
(assert (= (select s2 l) false))
(check-sat)
(get-model)

(declare-datatypes (T1 T2) ((Pair (mk-pair (first T1) (second T2)))))
(declare-const p1 (Pair Int Int))
(declare-const p2 (Pair Int Int))
(assert (= p1 p2))
(assert (> (second p1) 20))
(check-sat)
(get-model)
(assert (not (= (first p1) (first p2))))
(check-sat)

(declare-datatypes () ((S A B C)))
(declare-const x S)
(declare-const y S)
(declare-const z S)
(declare-const u S)
; satisfied, since x y z may correspond to A B C
(assert (distinct x y z))
(check-sat)
; unsat, since there are too many variables, they can't be distinct
(assert (distinct x y z u))
(check-sat)

(set-option :timeout 2000)
(declare-datatypes () ((Nat zero (succ (pred Nat)))))
(declare-fun p (Nat) Bool)
(assert (p zero))
(assert (forall ((x Nat)) (implies (p (pred x)) (p x))))
(assert (not (forall ((x Nat)) (p x))))
(check-sat)
(get-info :all-statistics)

;;;; from bjorner
;;;; assert properties of a subtyping function
(declare-sort Type)
(declare-fun subtype (Type Type) Bool)
(declare-fun array-of (Type) Type)
; all things are a subtype of themselves
(assert (forall ((x Type)) (subtype x x)))
; transitive property
(assert (forall ((x Type) (y Type) (z Type))
          (=> (and (subtype x y) (subtype y z))
              (subtype x z))))
; mutual subtype relations imply type identity
(assert (forall ((x Type) (y Type))
          (=> (and (subtype x y) (subtype y x))
              (= x y))))
;
(assert (forall ((x Type) (y Type) (z Type))
          (=> (and (subtype x y) (subtype x z))
              (or (subtype y z) (subtype z y)))))
;
(assert (forall ((x Type) (y Type))
          (=> (subtype x y)
              (subtype (array-of x) (array-of y)))))
; exists a minimum type
(declare-const root-type Type)
(assert (forall ((x Type)) (subtype x root-type)))
(check-sat)
(get-model)
