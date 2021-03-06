(declare-datatypes (T1 T2) (
      (Pair (pair (pairFirst T1) (pairSecond T1)))
    )
  )
(declare-datatypes (T1 T2 T3) (
      (Triple (triple (tripleFirst T1) (tripleSecond T2) (tripleThird T3)))
    )
  )
(declare-datatypes () ((Point (point (point_x Int) (point_y Int) (point_z Int)))))

(declare-const t1 (Triple Int Int Bool))
(declare-const t2 (Triple Int Int Bool))
(declare-const t3 (Triple Int Int Bool))
(assert (= t1 t2))
(assert (> (tripleFirst t1) 20))
(assert (> (tripleFirst t3) (tripleFirst t1)))
(assert (not (tripleThird t1)))
(declare-const p1 (Pair Int Bool))
(assert (= (pairFirst p1) (tripleSecond t3)))
(declare-const pnt Point)
(assert (= (point_x pnt) (tripleFirst t1)))
(assert (= (point_y pnt) (+ (tripleSecond t1) 10)))
(assert (= (point_z pnt) (+ (pairFirst p1) 1)))

(check-sat)
(get-model)
