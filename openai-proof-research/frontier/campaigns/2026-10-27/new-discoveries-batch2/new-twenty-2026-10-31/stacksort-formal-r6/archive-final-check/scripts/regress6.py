import itertools, math, json, pathlib
lane=pathlib.Path(__file__).resolve().parent.parent
base=lane.parent
expected={int(k):int(v) for k,v in json.loads((base/'expanded-corpus-r133/outputs/stack_pairs_P_1_82.json').read_text()).items()}
review=json.loads((base/'stacksort-review-r1/outputs/reviewer_P_1_82_and_certificates.json').read_text())['P']
assert all(expected[int(k)]==int(v) for k,v in review.items())
def counts(weights=(1,2,1),wrong_fixed=False):
 X={(0,0,0):1}; I={}
 get=lambda T,m,r,s:T.get((m,r,s),0)
 for m in range(1,21):
  for r in range(1,min(m,21-m)+1):
   for s in range(1,min(m,21-m)+1):
    deletion=sum(weights[t]*weights[u]*get(X,m-1,r-1+t,s-1+u) for t in range(3) for u in range(3))
    fixed=free=0
    for b in range(1,m):
     conv=sum(get(X,m-b,r-a,s-c)*get(I,b,a,c) for a in range(1,r) for c in range(1,s))
     fixed+=math.comb(m if wrong_fixed else m-1,b if wrong_fixed else b-1)*conv
     free+=math.comb(m,b)*conv
    assert deletion>=fixed
    I[m,r,s]=deletion-fixed; X[m,r,s]=deletion-fixed+free
 return {m:X[m,1,1] for m in range(1,21)}
P=counts(); assert all(P[n]==expected[n] for n in P)
assert counts((1,1,1))[2]!=expected[2]
try:
 wrong=counts(wrong_fixed=True)
except AssertionError:
 pass
else:
 assert wrong!=P
def sort(w):
 if not w:return ()
 m=max(w); k=w.index(m)
 return sort(w[:k])+sort(w[k+1:])+(m,)
for n in range(1,8):
 fibres={}
 for w in itertools.permutations(range(n)):
  v=sort(w); fibres[v]=fibres.get(v,0)+1
 assert sum(v*v for v in fibres.values())==expected[n]
print('PASS: all 20 clipped recurrence seeds match both immutable tables; literal max-split collision counts n=1..7; wrong unary and fixed-shuffle controls rejected')
