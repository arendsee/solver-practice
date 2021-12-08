; a morloc program with refinements:

; --- morloc
; roll :: x:Int -> y:Int where
;   x > 0
;   y > 0
;   y <= x
;
; max :: x:Int -> y:Int -> z:Int where
;   (x > y && z == x) || (y >= x && z == y)
;
; rollAdvantage = max (roll 20) (roll 20)
;
; -- this should fail, or at least raise a warning, since values outside the domain may be provided by `roll 20`
; bad :: x:Int where x > 10
; bad = roll 20
;
; -- this should definitely fail, since there is not even any overlap between the domain of `veryBad` and `roll 20`
; veryBad :: x:Int where x > 20
; veryBad = roll 20
; ---

; Our goal is to find all constraints these types impose and then determine
; whether they are satisfiable and consistent. Eventually, of course, the morloc
; compiler will need to generate these constraints for us, we can adapt the
; algorithm from (Rondon 2008) on liquid types.

; Each of the type signatures needs to be checked for satisfiability, starting with roll
;
;    exists (x :: Int) and (y :: Int) such that x > 0, y > 0 and y <= x
;
; This is obviously satisfiable, as witnessed by the values x=1 and y=1.
; Existence of one value that meets the constraints is all that is needed to
; prove satisfiability.
;
; Next for max:
;
;    exists (x :: Int) and (y :: Int)  and (z :: Int) such that (x > y && z == x) || (y >= x && z == y)
;
; This is also satisfiable, witnessed by the values x=1, y=1, and z=1

; For rollAdvantage, the constraints are not given: it is the job of the
; compiler to infer them. The use of the `roll` and `max` functions introduce
; constraints on the value of `rollAdvantage`. First we assign labels to every
; expression in the function:

; x0:(max x1:(roll x2:20) x3:(roll x4:20))

; Then we can map over all the constraints from the type signatures:
;   x4 = 20
;   x4 > 0   -- from the `x > 0` constraint in roll
;   x3 > 0
;   x3 <= x4
;   x2 = 20
;   x2 > 0
;   x1 > 0
;   x1 <= x2
;   (x1 > x3 && x0 == x1) || (x3 >= x1 && x0 == x3)   -- constraint on max

; Given this set of constraints, is there at least one solution that satisfies
; the system? Are their any cases where a function may receive an input that is
; outside the set domain?
