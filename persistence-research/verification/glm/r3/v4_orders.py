#!/usr/bin/env python3
"""v4_orders.py -- certify the order formulas far beyond any L the proof can reach:
  ord_{3^k}(10)  = 3^(k-2)      for 2 <= k <= 60
  ord_{7^k}(10)  = 6*7^(k-1)    for 1 <= k <= 30
  ord_{5^k}(3)   = 4*5^(k-1)    for 1 <= k <= 30
Test: d | a^d - 1 mod p^k AND a^(d/p) not ≡ 1 mod p^k  (two-sided order certificate).
"""
ok = True
def chk(c, m):
    global ok
    if not c: ok = False; print("FAIL:", m)

for k in range(2, 61):
    mod = 3**k; d = 3**(k-2)
    chk(pow(10, d, mod) == 1, f"ord3 k={k} upper")
    if k >= 3:
        chk(pow(10, d // 3, mod) != 1, f"ord3 k={k} lower")
for k in range(1, 31):
    mod = 7**k; d = 6 * 7**(k-1)
    chk(pow(10, d, mod) == 1, f"ord7 k={k} upper")
    if k >= 2:
        chk(pow(10, d // 7, mod) != 1, f"ord7 k={k} lower")
    else:
        chk(all(pow(10, j, 7) != 1 for j in range(1, 6)), "ord7 k=1")
for k in range(1, 31):
    mod = 5**k; d = 4 * 5**(k-1)
    chk(pow(3, d, mod) == 1, f"ord5 k={k} upper")
    if k >= 2:
        chk(pow(3, d // 5, mod) != 1, f"ord5 k={k} lower")
    else:
        chk(all(pow(3, j, 5) != 1 for j in range(1, 4)), "ord5 k=1")
print("ALL ORDER FORMULAS CERTIFIED k<=60 (3), k<=30 (5,7)" if ok else "FAILURES FOUND")
