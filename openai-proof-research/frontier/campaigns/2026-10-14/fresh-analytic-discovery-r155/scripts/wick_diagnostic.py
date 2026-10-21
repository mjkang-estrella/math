"""Exact finite Wick-pairing coefficient check, not a mathematical gate."""
from itertools import permutations

def contractions(a,b):
    return sum(all(a[i]==b[p[i]] for i in range(len(a))) for p in permutations(range(len(b))))

# R_i=:g_i sum_a g_a^2:, three free scalar colors.
coeff={}
for i in range(3):
    for j in range(3):
        coeff[f'{i+1},{j+1}']=sum(contractions([i,a,a],[j,b,b]) for a in range(3) for b in range(3))
# One cubic external insertion R_1 and three g_1 leaves.
star=sum(contractions([0,a,a],[0,0,0]) for a in range(3))
assert coeff=={f'{i+1},{j+1}':10 if i==j else 0 for i in range(3) for j in range(3)}
assert star==6
print({'cubic_cubic_coefficients':coeff,'one_cubic_three_linear_star':star,
       'meaning':'finite combinatorial diagnostic only; no proof/correctness/contribution/acceptance grade'})
