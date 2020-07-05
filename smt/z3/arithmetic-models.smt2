; Spend exactly 100 dollars and buy exactly 100 animals.
; • Dogs cost 15 dollars,
; • cats cost 1 dollar,
; • and rats cost 25 cents each.

(declare-const ndogs Int)
(declare-const ncats Int)
(declare-const nrats Int)
(assert (= (+ (* ndogs 1500) (* ncats 100) (* nrats 25)) 10000))
(assert (= (+ ndogs ncats nrats) 100))
(assert (> ndogs 0))
(assert (> ncats 0))
(assert (> nrats 0))

(check-sat)
(get-model)
