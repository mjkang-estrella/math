# Cyclic sequence S = e_0..e_{b-1}, w_1..w_R, e_t, ..., e_{b-1}, e_0, ..., e_{b-1}  (length n = 2b + R - t)
# Check directly that every b cyclically consecutive vectors are independent over Q, with interval columns
# (consecutive-ones => totally unimodular => nonzero minors are +-1 => independent over every field).
import sys, json, os
from fractions import Fraction
def rank(vs, b):
    M = [[Fraction(x) for x in v] for v in vs]; rk = 0; cols = b
    for c in range(cols):
        p = next((i for i in range(rk, len(M)) if M[i][c] != 0), None)
        if p is None: continue
        M[rk], M[p] = M[p], M[rk]
        for i in range(len(M)):
            if i != rk and M[i][c] != 0:
                f = M[i][c] / M[rk][c]; M[i] = [a - f*bb for a, bb in zip(M[i], M[rk])]
        rk += 1
    return rk
def seq(b, R, t, ivs):
    e = lambda i: [1 if k == i else 0 for k in range(b)]
    S = [e(i) for i in range(b)] + [[1 if lo <= k <= hi else 0 for k in range(b)] for (lo, hi) in ivs] + [e(i) for i in range(t, b)] + [e(i) for i in range(b)]
    return S
def valid(S, b):
    n = len(S)
    return all(rank([S[(s + j) % n] for j in range(b)], b) == b for s in range(n))
if __name__ == "__main__":
  B0, B1 = int(sys.argv[1]), int(sys.argv[2])
  for b in range(B0, B1+1):
      ivs_all = [(lo, hi) for lo in range(b) for hi in range(lo, b)]
      for rho in range(1, b):
          found = None
          for R in range(rho, b + rho):
              t = R - rho
              if t > b - 1: break
              # DFS over interval columns with incremental window checks (entering windows)
              def rec(cols):
                  nonlocal_found = None
                  return None
              stack = [[]]
              # simple DFS with pruning on entering windows e_{b-p}..e_{b-1}, w_1..w_p (p = len(cols))
              def dfs(cols):
                  global found
                  if found: return
                  p = len(cols)
                  if 0 < p <= b:
                      vs = [[1 if k == i else 0 for k in range(b)] for i in range(b - (b - p) if False else p, b)]
                      vs = [[1 if k == i else 0 for k in range(b)] for i in range(p, b)] + [[1 if lo <= k <= hi else 0 for k in range(b)] for (lo, hi) in cols[:min(p, b)]]
                      if p <= b and rank(vs[-b:], b) < min(b, len(vs[-b:])): return
                  if p == R:
                      S = seq(b, R, t, cols)
                      if valid(S, b): found = {'R': R, 't': t, 'intervals': list(cols), 'n': len(S)}
                      return
                  for iv in ivs_all:
                      dfs(cols + [iv])
                      if found: return
              dfs([])
              if found: break
          print(json.dumps({'b': b, 'rho': rho, 'n': 2*b + rho, 'found': found}), flush=True)
  