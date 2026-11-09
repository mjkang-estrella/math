# Swap whole binary-pattern classes of TC-dominant set (m=5) and compute spectral radius.
import itertools,numpy as np,json
m=5; al='ACGT'; comp={'A':'T','T':'A','C':'G','G':'C'}
rc=lambda w:''.join(comp[c] for c in reversed(w))
words=[''.join(t) for t in itertools.product(al,repeat=m)]
idx={w:i for i,w in enumerate(words)}
bits=lambda w:''.join('1' if c in 'TC' else '0' for c in w)
def rho(S):
    S=sorted(S); ix={w:i for i,w in enumerate(S)}; A=np.zeros((len(S),len(S)))
    for w in S:
        for c in al:
            y=w[1:]+c
            if y in ix: A[ix[w],ix[y]]=1
    return max(abs(np.linalg.eigvals(A)))
TC=[w for w in words if bits(w).count('1')>=3]
pats=sorted({bits(w) for w in TC if bits(w).count('1')==3})
res=[]
for k in range(0,4):
  for sub in itertools.combinations(pats,k):
    S=[rc(w) if bits(w) in sub else w for w in TC]
    res.append((rho(S),sub))
res.sort(reverse=True)
for r in res[:10]: print(r)
print('TC',rho(TC))
