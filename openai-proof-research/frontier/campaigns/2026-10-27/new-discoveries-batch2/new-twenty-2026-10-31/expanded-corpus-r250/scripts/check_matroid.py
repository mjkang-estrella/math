import itertools,json
cols=[9,6,4,11,6,14,5,1,12];r=4;n=len(cols)
def independent(ix):
 return all(__import__('functools').reduce(int.__xor__,[cols[ix[j]] for j in range(4) if m>>j&1],0)!=0 for m in range(1,16))
bases=[set(c) for c in itertools.combinations(range(n),r) if independent(c)]
for x in [1,6]:
 E=set(range(n))-{x};decomp=[sorted(b) for b in bases if b<=E and E-b in bases];print(x,decomp)
