(declare-datatype
  Type (
     (t_var (var String))             ; type terms
     (t_fun (funI Type) (funO Type))  ; functions
     (t_arr (arr1 Type) (arr2 Type))  ; parameterized types
  )
)

;;; In Haskell, this would be:
; data Type = Var String | Fun Type Type | Arr Type Type
;;; The difference is that every parameter in every data constructor must
;;; be named in z3

;;; program
; map :: forall a b . (a -> b) -> [a] -> [b]
; odd :: Int -> Bool
; foo xs = map odd xs

;   (1)
;   /\_____________
;  /       \       \
; (2) foo  (3) xs  (4)
;                  / \
;                 /   \
;                (5)  (6) xs
;               /  \___
;              /       \
;             (7) map  (8) odd

(declare-const t2 Type)
(declare-const t3 Type)
(declare-const t4 Type)

; Abs
(assert (= t2 (t_fun t3 t4)))

; ---- @4 ----
(declare-const t5 Type)
(declare-const t6 Type)

; App
(assert (= t5 (t_fun t6 t4)))

; ---- @6 ----
; Var
(assert (= t3 t6))

; ---- @5 ----
(declare-const t7 Type)
(declare-const t8 Type)
; App
(assert (= t7 (t_fun t8 t5)))



; ---- 'map' type signature ----
(declare-const t9 Type)
(declare-const t10 Type)
(assert (and (= t8 (t_fun t9 t10))
             (= t6 (t_arr (t_var "List") t9))
             (= t4 (t_arr (t_var "List") t10))))

; ---- 'odd' type signature ----
(assert (= t8 (t_fun (t_var "Int") (t_var "Bool"))))

(check-sat)
(get-model)
