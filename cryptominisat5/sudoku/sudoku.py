from pycryptosat import Solver
import sys

def exactly_one(xs, s):
  # for all pairs of values, one must be false
  for i in range(len(xs)):
    for j in (range(i+1, len(xs))):
      s.add_clause([-xs[i], -xs[j]])
  # but one value must be true
  s.add_clause(xs)

# values from 1 to 9^3 for a 9X9 game
# row : [1,2,...,9]
# col : [1,2,...,9]
# val : [1,2,...,9]
def make_id(row, col, val):
  return (9 * (col-1) + 81 * (row-1) + val)

# straight rules (same for all games)
def col_rules(s):
  for col in range(1,10):
    for val in range(1,10):
      xs = [make_id(row,col,val) for row in range(1,10)]
      exactly_one(xs, s)

# rules defining constraints on rows (same for all games)
def row_rules(s):
  for row in range(1,10):
    for val in range(1,10):
      xs = [make_id(row,col,val) for col in range(1,10)]
      exactly_one(xs, s)

# rules defining constraints on boxes (same for all games)
def box_rules(s):
  for box_row in range(3):
    for box_col in range(3):
      for val in range(1,10):
        xs = [make_id(box_row*3+i,box_col*3+j,val) for i in range(1,4) for j in range(1,4)]
        exactly_one(xs, s)

# set the given values for the game
def constant_rules(game, s):
  for (pos,val) in enumerate(game):
    if (val != 0):
      i = make_id(pos // 9 + 1, pos % 9 + 1, val)
      s.add_clause([i])

# require each cell has a unique solution
def int_rules(s):
  for row in range(1,10):
    for col in range(1,10):
      xs = [make_id(row, col, val) for val in range(1,10)]
      exactly_one(xs, s)

def build_solver(game):
  s = Solver()
  constant_rules(game, s)
  row_rules(s)
  col_rules(s)
  box_rules(s)
  int_rules(s)
  return s

def pretty_print(sat, solution):
  if not sat:
    print("No solution")
    sys.exit(1)
  vals = [i for (i,val) in enumerate(solution) if val ]

  i=0
  for row in range(9):
    for grp in range(3):
      for cel in range(3):
        print(vals[i] - row * 81 - (grp*3 + cel) * 9, end="")
        i += 1
      print(" ", end="")
    print("")

if __name__ == '__main__':

  game1 = [
      5,3,0, 0,7,0, 0,0,0,
      6,0,0, 1,9,5, 0,0,0,
      0,9,8, 0,0,0, 0,6,0,

      8,0,0, 0,6,0, 0,0,3,
      4,0,0, 8,0,3, 0,0,1,
      7,0,0, 0,2,0, 0,0,6,

      0,6,0, 0,0,0, 2,8,0,
      0,0,0, 4,1,9, 0,0,5,
      0,0,0, 0,8,0, 0,7,9,
    ]

  s = build_solver(game1)
  sat, solution = s.solve()
  pretty_print(sat, solution)
