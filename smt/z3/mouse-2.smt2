;;; in rbase
; map :: forall a b . (a -> b) -> [a] -> [b]
; map r :: forall a b . (a -> b) -> [a] -> [b]
; map :: forall a b c . (a -> b -> c) -> [a] -> [b] -> [c]
; map r :: forall a b c . (a -> b) -> [a] -> [b] -> [c]
; sqrt :: Num -> Num
; sqrt r :: numeric -> numeric

;;; in pybase
; map :: forall a b . (a -> b) -> [a] -> [b]
; map py :: forall a b . (a -> b) -> [a] -> [b]
; map :: forall a b c . (a -> b -> c) -> [a] -> [b] -> [c]
; map py :: forall a b c . (a -> b) -> [a] -> [b] -> [c]
; sqrt :: Num -> Num
; sqrt py :: float -> float

;;; in this script
; import rbase (map, sqrt)
; import pybase (map, sqrt)
;
; foo xs = map sqrt xs

;;;;; procedure ;;;;;;;;
; Step 1 - assign unique names to everything
; map = map1 | map2 | map3 | map4
;  where
;   map1   :: forall a b . (a -> b) -> [a] -> [b]
;        r :: forall a b . (a -> b) -> [a] -> [b]
;   map2   :: forall a b c . (a -> b) -> [a] -> [b] -> [c]
;        r :: forall a b c . (a -> b) -> [a] -> [b] -> [c]
;   etc
; sqrt = sqrt1 | sqrt2
(declare-const map1 Bool)
(declare-const map2 Bool)
(declare-const map3 Bool)
(declare-const map4 Bool)
(declare-const sqrt1 Bool)
(declare-const sqrt2 Bool)

; Our goal now is to 1) select one map and one sqrt implementation and 2) to
; resolve the polymorphic terms in the map function. For the second goal, we
; define variables for all the polymorphic variables. For now, they are typed
; as strings, but eventually they will need to be nested arrays (capable of
; representing parameterized types and records).
; general types
(declare-const map_a_gen String)
(declare-const map_b_gen String)
(declare-const map_c_gen String)
; concrete types
(declare-const map_a_con String)
(declare-const map_b_con String)
(declare-const map_c_con String)

; Step 2 - make the functions mutually exclusive
; Each unique function is linked to one implementation
; We want to find a unique solution (and eventually, an optimal one)
; So we add a mutual exclusion statement
(assert (or (and map1 (not map2) (not map3) (not map4))
            (and map2 (not map1) (not map3) (not map4))
            (and map3 (not map1) (not map2) (not map4))
            (and map4 (not map1) (not map2) (not map3))))
(assert (or (and sqrt1 (not sqrt2))
            (and sqrt2 (not sqrt1))))

; Step 3 - check map against each of its inputs
(assert (or (and map1 sqrt1 (= map_a_gen "Num") (= map_a_con "numeric"))
            (and map2 sqrt1 (= map_a_gen "Num") (= map_a_con "numeric"))
            (and map3 sqrt1 (= map_a_gen "Num") (= map_a_con "numeric"))
            (and map4 sqrt1 (= map_a_gen "Num") (= map_a_con "numeric"))
            (and map1 sqrt2 (= map_a_gen "Num") (= map_a_con "float")  )
            (and map2 sqrt2 (= map_a_gen "Num") (= map_a_con "float")  )
            (and map3 sqrt2 (= map_a_gen "Num") (= map_a_con "float")  )
            (and map4 sqrt2 (= map_a_gen "Num") (= map_a_con "float")  )))
(assert (or (and map1 sqrt1 (= map_b_gen "Num") (= map_b_con "numeric"))
            (and map2 sqrt1 (= map_b_gen "Num") (= map_b_con "numeric"))
            (and map3 sqrt1 (= map_b_gen "Num") (= map_b_con "numeric"))
            (and map4 sqrt1 (= map_b_gen "Num") (= map_b_con "numeric"))
            (and map1 sqrt2 (= map_b_gen "Num") (= map_b_con "float"))
            (and map2 sqrt2 (= map_b_gen "Num") (= map_b_con "float"))
            (and map3 sqrt2 (= map_b_gen "Num") (= map_b_con "float"))
            (and map4 sqrt2 (= map_b_gen "Num") (= map_b_con "float"))))

(check-sat)
(get-model)

; This works for this particular case. But can it be generalized?
; Remaining cases to handle: 
;  * parameterized types
;  * records
;  * imported functions that are morloc compositions (differing topologies)
;  * performance optimization
