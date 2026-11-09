import pathlib,json,itertools,hashlib,sys
from attractor_checks import masks,close,theta,valid,solve
L=pathlib.Path(__file__).resolve().parent
data=json.loads((L/'attractor-results.json').read_text())
bad=sorted([r for r in data['rows'] if r['complete'] and r['positions'] is None],key=lambda r:(len(r['word']),r['word']))
print('bad lengths',[(len(r['word']),r['nodes']) for r in bad])
r=bad[0];w=r['word'];cs=masks(w);print('FIRST',r)
complexity=[len({w[i:i+k] for i in range(len(w)-k+1)}) for k in range(1,len(w)+1)]
print('complexity obstruction',[(k,c) for k,c in enumerate(complexity,1) if c>4*k])
# Independent flat enumeration: every size-four subset misses a distinct factor.
# Integer masks are occurrence unions; no solver arithmetic.
factors={}
for k in range(1,len(w)+1):
 for i in range(len(w)-k+1):
  f=w[i:i+k];factors.setdefault(f,set()).update(range(i,i+k))
small=sorted(factors,key=lambda f:len(factors[f]))
essential=[]
for f in small:
 s=factors[f]
 if not any(factors[g]<=s for g in essential):essential.append(f)
print('essential',len(essential),[(f,sorted(factors[f])) for f in essential])
tested=0
for c in itertools.combinations(range(len(w)),4):
 assert any(not set(c)&factors[f] for f in essential);tested+=1
five=solve(cs,5,budget=1000000);assert five['positions'] is not None and valid(w,five['positions'])
x=''
for a,e in r['directive']:x=close(x+a,e)
assert x==w and w==theta(w,r['directive'][-1][1])
out=dict(word=w,length=len(w),directive=r['directive'],four_subsets_exhausted=tested,attractor5=five['positions'],essential_constraints=[dict(factor=f,positions=sorted(factors[f])) for f in essential],complexity=complexity,claim='minimum attractor size exactly 5; prior status not cleared')
(L/'attractor-certificate.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k not in ['essential_constraints','complexity']},indent=2))
