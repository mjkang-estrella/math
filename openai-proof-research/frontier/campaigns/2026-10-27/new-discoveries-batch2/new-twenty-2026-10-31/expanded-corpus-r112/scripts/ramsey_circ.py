"""Circulant restriction of the cyclic/ordered Ramsey SAT encoding: colour of {u,v} depends only on the cyclic distance
min(|u-v|, n-|u-v|) in 1..floor(n/2); variable y_d TRUE = colour 2. For cyclic mode, embeddings are rotations of sorted
k-subsets; by rotation invariance only subsets containing vertex 0 are needed.
usage: ramsey_circ.py H1 H2 n out.cnf"""
import sys,itertools
sys.path.insert(0,__import__('os').path.dirname(__file__))
from ramsey_sat import graph
def main():
    h1,h2,n,out=sys.argv[1:5];n=int(n)
    a,E1=graph(h1);b,E2=graph(h2)
    d=lambda u,v: min(abs(u-v),n-abs(u-v))
    cl=set()
    for k,E,sgn in [(a,E1,1),(b,E2,-1)]:
        for rest in itertools.combinations(range(1,n),k-1):
            c=(0,)+rest
            for t in range(k):
                r=c[t:]+c[:t]
                cl.add(tuple(sorted({sgn*d(r[u],r[v]) for u,v in E})))
    m=n//2
    with open(out,'w') as f:
        f.write(f'p cnf {m} {len(cl)}\n')
        for c in cl: f.write(' '.join(map(str,c))+' 0\n')
    print('circ',h1,h2,n,'vars',m,'clauses',len(cl))
main()
