; f1 :: Num -> Num -> Num
; f1 py :: float -> float -> float
;
; f2 :: Int -> Int -> Int
; f2 py :: int -> int -> int
;
; f3 :: Num -> Num -> Num
; f3 cpp :: double -> double -> double
;
; g1 :: Num -> Num -> Num
; g1 cpp :: double -> double -> double
;
; g2 :: Int -> Int -> Int
; g2 cpp :: int -> int -> int
;
; f = f1 | f2 | f3    -- these correspond to the functions
; g = g1 | g2         -- imported from different modules
;
; foo x y = f x (g 42 y)
;
; * Turn the program into a tree
; * Number the nodes
; * Use the unique node numbering to uniquely identify the functions
; * Each function is associated with a name, the name is used to look up all
;   possible implementations and their types

(declare-const f1 Bool)
(declare-const f2 Bool)
(declare-const f3 Bool)

(declare-const g1 Bool)
(declare-const g2 Bool)

(declare-const x String)
(declare-const y String)

(assert (or (and f1 (= x "Num"))
            (and f2 (= x "Int"))
            (and f3 (= x "Num"))))

(assert (or (and g1 (= y "Num"))
            (and g2 (= y "Int"))))

(assert (or (and f1 (not f2) (not f3))
            (and f2 (not f1) (not f3))
            (and f3 (not f1) (not f2))))

(assert (or (and g1 (not g2))
            (and g2 (not g1))))

(assert (or (and f1 g1 (= "Num" "Num"))
            (and f1 g2 (= "Num" "Int"))
            (and f2 g1 (= "Int" "Num"))
            (and f2 g2 (= "Int" "Int"))
            (and f3 g1 (= "Num" "Num"))
            (and f3 g2 (= "Num" "Int"))))

(check-sat)
(get-model)
