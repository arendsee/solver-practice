from pycryptosat import Solver
import sys

def exactly_one(xs, s):
  # for all pairs of values, one must be false
  for i in range(len(xs)):
    for j in (range(i+1, len(xs))):
      s.add_clause([-xs[i], -xs[j]])
  # but one value must be true
  s.add_clause(xs)

def dnf_to_cnf(xss, s):
  """
  Convert from a disjunctive normal form, where ANDed sets are ORed together,
  to a conjunctive normal form, where ORed sets are ANDed together.

  This is done by ANDing together all sets containing exactly one
  representative from wach AND group.
  """

  def _dnf_to_cnf(xss):
    if len(xss) == 0:
      return [[]]
    elif len(xss) == 1:
      return [xss[0]]
    else:
      return [[x] + xs for x in xss[0] for xs in _dnf_to_cnf(xss[1:])]

  for xs in _dnf_to_cnf(xss):
    s.add_clause(xs)

def key_index(p, l, k, n_levels, n_pins):
  """
  p,l,k are all assumed to be 0-based
  """
  return (1 + l + p * n_levels + k * n_levels * n_pins)

def lck_index(p, l, k, n_levels, n_pins, n_keys):
  """
  p,l,k are all assumed to be 0-based
  """
  return (n_levels * n_pins * n_keys + key_index(p,l,k,n_levels,n_pins))

def keys_have_exactly_one_cut(n_keys, n_pins, n_levels, s):
  for i in range(n_keys):
    for p in range(n_pins):
      xs = [key_index(p,l,i,n_levels,n_pins) for l in range(n_levels)]
      exactly_one(xs, s)

def locks_have_at_least_one_shear(n_keys, n_locks, n_pins, n_levels, s):
  for i in range(n_locks):
    for p in range(n_pins):
      xs = [lck_index(p,l,i,n_levels,n_pins,n_keys) for l in range(n_levels)]
      s.add_clause(xs)

#   G  M1 M2 K1 K2 K3 K4 K5 K6 K7 K8
#   1  1  0  1  0  0  0  0  0  0  0   L1
#   1  1  0  0  1  0  0  0  0  0  0   L2
#   1  1  0  0  0  1  0  0  0  0  0   L3
#   1  1  0  0  0  0  1  0  0  0  0   L4
#   1  0  1  0  0  0  0  1  0  0  0   L5
#   1  0  1  0  0  0  0  0  1  0  0   L6
#   1  0  1  0  0  0  0  0  0  1  0   L7
#   1  0  1  0  0  0  0  0  0  0  1   L8
#   1  1  1  1  1  1  1  1  1  1  1   GL
def keys_must_open_charted_locks(keyset, n_levels, n_pins, s):
  n_keys = len(keyset)
  for lck_idx in range(len(keyset)): 
    for key_idx in range(len(keyset[lck_idx])):
      if keyset[lck_idx][key_idx]:
        xs = []
        for pin in range(n_pins):
          dnf_to_cnf(
            [ [ key_index(key_idx, pin, lvl, n_levels, n_pins)
              , lck_index(lck_idx, pin, lvl, n_levels, n_pins, n_keys)
              ]
              for lvl in range(n_levels)
            ],
            s
          )

def keys_must_not_open_uncharted_locks(keyset, n_levels, n_pins, s):
  n_keys = len(keyset)
  for lck_idx in range(len(keyset)): 
    for key_idx in range(len(keyset[lck_idx])):
      if not keyset[lck_idx][key_idx]:
        for pin in range(n_pins):
          for lvl in range(n_levels):
            s.add_clause([ -1 * key_index(key_idx, pin, lvl, n_levels, n_pins)
                         , -1 * lck_index(lck_idx, pin, lvl, n_levels, n_pins, n_keys)])

def keys_must_not_match_gencon(gencon, s):
  pass

def build_solver(keyset, gencon, n_pins, n_levels):
  s = Solver()

  n_keys = len(keyset[0])
  n_locks = len(keyset)

  keys_have_exactly_one_cut(n_keys, n_pins, n_levels, s)
  locks_have_at_least_one_shear(n_keys, n_locks, n_pins, n_levels, s)
  keys_must_open_charted_locks(keyset, n_levels, n_pins, s)
  keys_must_not_open_uncharted_locks(keyset, n_levels, n_pins, s)
  keys_must_not_match_gencon(gencon, s)

  return s

def unindex(i, n_levels, n_pins):
  ind = i // (n_levels * n_pins) + 1
  pin = (i % (n_pins * n_levels)) // n_levels + 1
  lvl = i % n_levels + 1
  return(ind,pin,lvl)

if __name__ == '__main__':

  keyset = [
#      G  M1 M2 K1 K2 K3 K4 K5 K6 K7 K8
      [1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0], # L1
      [1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0], # L2
      [1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0], # L3
      [1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0], # L4
      [1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0], # L5
      [1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0], # L6
      [1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0], # L7
      [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], # L8
      [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], # GL
    ]

  # Can't have 0 twice in a row (too structurally weak)
  gencon = [
      [0, 0, None, None],
      [None, 0, 0, None],
      [None, None, 0, 0],
    ]

  # number of pins
  n_pins = 4

  # number of levels
  n_levels = 3

  n_keys = len(keyset[0])
  n_locks = len(keyset)

  s = build_solver(keyset, gencon, n_pins, n_levels)
  sat, solution = s.solve()

  if not sat:
    print("No solution", file=sys.stderr)
    sys.exit(1)

  key_lvls=[]
  for (i, v) in enumerate(solution[1:(n_pins*n_levels*n_keys+1)]):
    if v:
      (key,pin,lvl) = unindex(i, n_levels, n_pins)
      key_lvls.append(lvl)
      if pin == n_pins:
        print(f"key {str(key)}: ({','.join([str(l) for l in key_lvls])})")
        key_lvls=[]

  locks = [[[] for j in range(n_pins)] for i in range(n_locks)]
  for (i, v) in enumerate(solution[(n_pins*n_levels*n_keys+1):]):
    if v:
      (lck,pin,lvl) = unindex(i, n_levels, n_pins)
      locks[lck-1][pin-1].append(lvl)
  for (i,lock) in enumerate(locks):
    pins = ["/".join([str(lvl) for lvl in lvls]) for lvls in lock]
    print(f"lock {i+1}: ({','.join(pins)})")
