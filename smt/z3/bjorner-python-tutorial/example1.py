#!/usr/bin/env python3

from z3 import *

if __name__ == '__main__':
  """
  You must (wear a tie or a shirt) and
           (not wear a tie or wear a shirt) and
           (not wear a tie or not wear a shirt)
  """
  Tie, Shirt = Bools('Tie Shirt')
  s = Solver()
  s.add(
    Or(Tie, Shirt),
    Or(Not(Tie), Shirt),
    Or(Not(Tie), Not(Shirt))
  )
  print(s.check())
  print(s.model())
