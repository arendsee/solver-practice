(declare-datatype
  Type (
     ; TODO: add polymorphic type
     (t_var (var String))             ; type terms
     (t_fun (funI Type) (funO Type))  ; functions
     (t_arr (arr1 Type) (arr2 Type))  ; parameterized types
  )
)

;;; program
; id :: forall a . a -> a
; foo x = id [1,2,x]

;  (1)
;   /\_____________
;  /       \        \
; (2) foo   (3) x    (4)
;                     /\_____
;                    /       \
;                   (5) id    (6) [
;                                 /\__________
;                                /    \       \
;                               (7) 1  (8) 2   (9) x

; descend into the tree, declaring nodes with an increasing index
; -- t1 doesn't have any meaningful type 
(declare-const t2 Type)
(declare-const t3 Type)
(declare-const t4 Type)

; Abs rule
(assert (= t2 (t_fun t3 t4)))

(declare-const t5 Type)
(declare-const t6 Type)

; App rule
(assert (= t4 (funO t5)))
; FIXME: inferred manually from id type signature -- need to generalize
(assert (= t5 (t_fun t6 t6)))

(declare-const t7 Type)
(declare-const t8 Type)
(declare-const t9 Type)

; Definition of a homogenous list
(declare-const t6a Type)
(assert (= t6 (t_arr (t_var "List") t6a)))
; FIXME: should use subtyping relation, not equality
(assert (= t6a t7 t8 t9))

; Primitive type inference
(assert (= t7 (t_var "Num")))
(assert (= t8 (t_var "Num")))

; Unification of bound variables
(assert (= t3 t9))
(check-sat)
(get-model)
