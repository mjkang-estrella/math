# Diagnostics only (not credited): 355892 literal Delta=2 failures; 355617 sign of source formula.
import itertools, json, resource
from math import comb, factorial
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
def semistrong(M, edges):
    V={v for e in M for v in e}; ind=[e for e in edges if e[0] in V and e[1] in V]
    deg={v:sum(v in e for e in ind) for v in V}
    return all(len(set(e))==2 for e in M) and len(V)==2*len(M) and all(deg[e[0]]==1 or deg[e[1]]==1 for e in M)
def chi_ss(n_vertices, edges):
    m=len(edges)
    for k in range(1,m+1):
        for col in itertools.product(range(k),repeat=m):
            if col[0]!=0: continue
            if all(semistrong([edges[i] for i in range(m) if col[i]==c],edges) for c in range(k)): return k
cyc={n:chi_ss(n,[(i,(i+1)%n) for i in range(n)]) for n in range(3,11)}
lah=lambda n:sum((-1)**(n-k-1)*comb(n-1,k-1)*factorial(n)//factorial(k) for k in range(1,n+1))
print(json.dumps({'355892_cycle_semistrong_index(Delta=2,bound Delta^2-1=3)':cyc,
 '355617_source_formula_chi(X(K_n))':{n:lah(n) for n in range(1,9)},
 '355617_note':'empty digraph on n vertices has reduced Euler characteristic -1 (only the empty face); a one-edge digraph has 0'}))
