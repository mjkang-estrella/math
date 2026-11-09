"""Exact finite-state diagnostics, not a test of the universal conjecture."""
import itertools,json,pathlib
L=pathlib.Path(__file__).resolve().parent
def step(q,state,c):
 if state is None:return None
 suffix,age,seen=state
 suffix=(suffix+c)[-len(q):]
 if suffix==q:return (suffix,0,True)
 age+=1
 if age>=len(q):return None
 return (suffix,age,seen)
def cover(u,v,q):
 # Exact safety run on u v^omega; cycle at a period boundary is a certificate.
 state=('',0,False)
 for c in u:
  state=step(q,state,c)
  if state is None:return False
 visited=set()
 while state not in visited:
  visited.add(state)
  for c in v:
   state=step(q,state,c)
   if state is None:return False
 return True
def words(n):return [''.join(t) for k in range(1,n+1) for t in itertools.product('ab',repeat=k)]
assert cover('aba','ba','aba')
assert not cover('a','b','ab')
assert cover('ab','ab','ab')
assert not cover('aba','bb','aba')
out=[]
for a,b in itertools.product(words(3),repeat=2):
 # ab^omega is never quasiperiodic: every prefix contains its unique a.
 witness=None
 prefix=(a+b*12)
 for m in range(1,13):
  q=prefix[:m]
  if cover(a,b,q):witness=q;break
 if witness:out.append(dict(a=a,b=b,q=witness))
result={'morphisms_tested':14**2,'certified_abomega_witnesses':len(out),'witnesses':out,
 'limits':'Only q length<=12, only input ab^omega, binary image lengths<=3. No absence or universal-conjecture conclusion.'}
(L/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='witnesses'}))
