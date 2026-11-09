"""Reviewer extra diagnostics: blocker nonideality via 1/4 vertex; core-only satisfiable (Pap Thm 3.4.7 consistency);
drop-one-blocker-member satisfiability (author's 'whole blocker needed' diagnostic)."""
import itertools, json, sys
from fractions import Fraction
E = [frozenset(s) for s in [{1,7,10},{2,3,8},{2,3,4},{0,3,4},{0,1,4},{0,5,6},{5,6,7},{1,6,7},{2,8,9},{8,9,10},{5,9,10}]]
V = range(11)
tr = [frozenset(T) for k in range(12) for T in itertools.combinations(V, k) if all(e & set(T) for e in E)]
s = set(tr); B = [T for T in tr if not any(T - {v} in s for v in T)]
B4 = [T for T in B if len(T) == 4]
def rank(A):
    A = [[Fraction(x) for x in r] for r in A]; r = 0
    for c in range(len(A[0])):
        p = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if p is None: continue
        A[r], A[p] = A[p], A[r]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c] / A[r][c]; A[i] = [a - f*b for a, b in zip(A[i], A[r])]
        r += 1
    return r
out = {}
out["B4_incidence_rank"] = rank([[1 if v in T else 0 for v in V] for T in B4])
y = Fraction(1, 4)
out["quarter_vector_feasible_for_P(b(C))"] = all(len(T) * y >= 1 for T in B)
out["quarter_tight_count"] = sum(len(T) * y == 1 for T in B)
# blocker of blocker = C (sanity of blocker computation)
tr2 = [frozenset(T) for k in range(12) for T in itertools.combinations(V, k) if all(b & set(T) for b in B)]
s2 = set(tr2); BB = [T for T in tr2 if not any(T - {v} in s2 for v in T)]
out["b(b(C)) == C"] = set(BB) == set(E)
Es = [sorted(e) for e in E]
def sat(blist):
    single = [[(i, next(iter(set(Es[i]) & T))) for i in range(11) if len(set(Es[i]) & T) == 1] for T in blist]
    for ch in itertools.product(range(3), repeat=11):
        p = [Es[i][ch[i]] for i in range(11)]
        if all(not ({v for i, v in single[j] if p[i] == v} >= T) for j, T in enumerate(blist)):
            return True
    return False
out["core_only_(C, B4)_satisfiable"] = sat(B4)
out["full_satisfiable"] = sat(B)
out["drop_one_satisfiable_count"] = sum(sat(B[:j] + B[j+1:]) for j in range(len(B)))
out["blocker_members"] = len(B)
json.dump(out, sys.stdout, indent=1); print()
