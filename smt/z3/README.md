# z3 solver

The `*.smt2` files can all be run with a bare z3 call, for example:

```
$ z3 mouse-1.smt2
sat
(
  (define-fun f2 () Bool
    false)
  (define-fun g2 () Bool
    false)
  (define-fun f1 () Bool
    false)
  (define-fun g1 () Bool
    true)
  (define-fun f3 () Bool
    true)
  (define-fun x () String
    "Num")
  (define-fun y () String
    "Num")
)
```

The `sat` term means that the system in mouse-1.smt2 was satisfiable. 
