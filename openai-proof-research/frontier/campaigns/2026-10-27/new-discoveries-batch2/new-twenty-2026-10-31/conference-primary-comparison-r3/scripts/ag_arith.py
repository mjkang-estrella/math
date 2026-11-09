import json
p, k = 19, 19
sq = {a * a % p for a in range(1, p)}
prop13 = [a for a in range(1, p) if (a * a + k) % p == 0]
prop14 = [(a, b) for a in range(1, p) for b in range(1, p) if (a * a + b * b + k) % p == 0]
r = {"p": p, "k": k, "nonzero_squares": sorted(sq), "minus1_is_square": (p - 1) in sq,
     "prop1_3_alpha_solutions": prop13, "prop1_4_alpha_beta_solutions": prop14}
json.dump(r, open('work/ag_arith.json', 'w'), indent=1); print(r)
