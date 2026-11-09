import itertools
from collections import Counter
from importlib.util import spec_from_file_location, module_from_spec
def stats(perm,cols,c):
    n=len(perm)
    inv=sum(1 for i in range(n) for j in range(i+1,n) if perm[i]>perm[j])
    col=sum(cols); key=[((c-t) if t else c, v) for v,t in zip(perm,cols)]
    maj=sum(i+1 for i in range(n-1) if key[i]>key[i+1]); return c*inv+col, c*maj+col
for c,n in [(1,3),(1,4),(2,2),(2,3),(3,2),(2,4),(3,3),(4,2),(4,3),(1,5),(2,5)]:
    D=Counter()
    for p in itertools.permutations(range(1,n+1)):
        for cols in itertools.product(range(c),repeat=n):
            if any(p[i]==i+1 and cols[i]==0 for i in range(n)): continue
            D[stats(p,cols,c)]+=1
    asym=sorted((k,D[k],D[(k[1],k[0])]) for k in D if D[k]!=D[(k[1],k[0])])
    print(c,n,'|D|',sum(D.values()),'asym',len(asym),asym[:3],flush=True)
