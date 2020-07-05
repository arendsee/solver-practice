;;; rbase
; head :: List a -> a
; head r :: list a -> a
; upper :: String -> String
; upper r :: character -> character

;;; morloc script
; import rbase (head, upper)
; foo xs = upper (head xs)


;;;;;;;;;;; procedure ;;;;;;;;;;;;;
; Step 0 - define types
; general types
(declare-datatypes (T) (GenString (GenList T) (GenFun T T)))
; concrete types
(declare-datatypes (T) (ConRcharacter (ConRlist T) (ConFun T T)))

; Step 1 - declare functions
; Maybe unnecessary since there is only one implementation of each function.
(declare-const head1 Bool)
(declare-const upper1 Bool)

; Step 2 - declare generic variables
(declare-const head1_a Type)

; xxx
