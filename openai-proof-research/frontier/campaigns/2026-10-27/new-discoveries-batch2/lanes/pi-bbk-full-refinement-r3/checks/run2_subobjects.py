"""Run 2: (a) exact counterexample to 'all sub-objects positive';
(b) h-superadditivity test for B={1,3,5};
(c) divisor-matching existence per (M,m)."""
import sys
from itertools import combinations
sys.path.insert(0, '.')
from gkn_core import series_mul, series_inv, q_pochhammer_odd

def coeff(poly):  # helper
    return poly

# (a) T = {1,7} with B = {1,3,5}: (1-q)(1-q^7)/((1-q)(1-q^3)(1-q^5)) = (1-q^7)/((1-q^3)(1-q^5))
den = q_pochhammer_odd(3, 2)          # (1-q^3)(1-q^5)
inv = series_inv(den, 30)
ser = series_mul([1,0,0,0,0,0,0,-1], inv)  # (1-q^7)/((1-q^3)(1-q^5))
print("(a) [q^m] (1-q^7)/((1-q^3)(1-q^5)), m<=20:", ser[:21])
print("    coefficient at q^7:", ser[7], " (negative => sub-object positivity FALSE at (k,n)=(4,2))")

# cross-check it is a legit sub-object of G_{4,2} = (1-q^7)(1-q^9)/((1-q)(1-q^3)(1-q^5))
g42 = series_mul(q_pochhammer_odd(7,2), series_inv(q_pochhammer_odd(1,3), 400))
print("    G_{4,2} min coeff up to 400:", min(g42), "(conjecture itself fine here)")

# (b) h = denumerant of B={1,3,5}; test h(a+u+2) >= h(u+2)+h(u) for all a>u>=0 (a odd), u<=200
hB = series_inv(q_pochhammer_odd(1,3), 2500)  # 1/((1-q)(1-q^3)(1-q^5))
def h(x): return hB[x] if x >= 0 else 0
fails = []
for u in range(0, 400):
    for a in range(u+1, u+80, 2):
        if a % 2 == 1 and h(a+u+2) < h(u+2) + h(u):
            fails.append((a,u,h(a+u+2),h(u+2),h(u)))
print("(b) h(a+u+2) >= h(u+2)+h(u) failures (u<=400):", fails[:5], "count", len(fails))

# also the tail-regime inequality for k=4: Delta_a h(m) >= Delta_a h(m-a-2) for m >= 2a+2
fails2 = []
for a in range(3, 60, 2):
    for m in range(2*a+2, 2*a+2+900):
        if h(m) - h(m-a) < h(m-a-2) - h(m-2*a-2):
            fails2.append((a,m))
print("(b2) Delta-inequality failures (a<=59):", fails2[:5], "count", len(fails2))

# (c) divisor matching: reduced form A = odds in [2M+1, 2M+2m-3] (m-1 els), B = odds [1,2m-1] (m els).
# matching: inject A -> B with phi(a)|a; one b0 free. Hall check by brute force (small).
def matching_exists(M, m):
    A = list(range(2*M+1, 2*M+2*m-2, 2))
    B = list(range(1, 2*m, 2))
    n = len(A)
    # bipartite matching, exact
    assign = {}
    def try_k(i, used):
        if i == n: return True
        for j,b in enumerate(B):
            if j in used: continue
            if a_div(b, A[i]):
                used.add(j)
                if try_k(i+1, used): used.discard(j); return True
                used.discard(j)
        return False
    def a_div(b, a): return a % b == 0
    return try_k(0, set())

bad_hall = []
for m in range(2, 13):
    for M in range(m, 4*m+2):
        ok = matching_exists(M, m)
        if not ok: bad_hall.append((M,m))
print("(c) (M,m) with NO divisor matching (M<4m+2):", bad_hall[:30], "count", len(bad_hall))
