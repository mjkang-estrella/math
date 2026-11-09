from pathlib import Path
import json,hashlib,itertools,time,resource,os
L=Path(__file__).resolve().parent; A=L.parent/'expanded-corpus-r250'
def frozen(name):
 d=json.loads((L/'frozen-inputs.json').read_text()); bad=[p for p,h in d.items() if not Path(p).is_file() or hashlib.sha256(Path(p).read_bytes()).hexdigest()!=h]; (L/(name+'.json')).write_text(json.dumps({'time':time.time(),'files':len(d),'mismatches':bad},indent=2)); assert not bad,bad
frozen('frozen-before')
cols=[9,6,4,11,6,14,5,1,12]; E=frozenset(range(9)); perms=list(itertools.permutations(range(4)))
# Leibniz determinant modulo two; no elimination, vector XOR, or author code.
def base(s):
 s=sorted(s)
 return len(s)==4 and sum(all((cols[s[j]]//(2**p[j]))%2 for j in range(4)) for p in perms)%2==1
B=[frozenset(s) for s in itertools.combinations(E,4) if base(s)]; BS=set(B)
ex=0
for b in B:
 for c in B:
  for x in b-c:
   assert any((b-{x})|{y} in BS for y in c-b);ex+=1
D={x:[b for b in B if x not in b and E-{x}-b in BS] for x in (1,6)}
assert len(B)==76 and len(D[1])==32 and len(D[6])==24 and not set(D[1])&set(D[6])
assert frozenset([0,2,3,5]) in D[1] and frozenset([0,1,2,7]) in D[6]
# Exhaustive independence by containment in bases, matroid connectedness via circuit chains.
I=lambda s:any(s<=b for b in B)
circuits=[frozenset(s) for n in range(1,6) for s in itertools.combinations(E,n) if not I(frozenset(s)) and all(I(frozenset(s)-{e}) for e in s)]
components=[{e} for e in E]
for c in circuits:
 hit=[s for s in components if s&c]; components=[s for s in components if not s&c]+[set().union(*hit)]
r={'method':'Leibniz determinant parity, 24 permutation products per four-subset','bases':[sorted(b) for b in B], 'exchange_obligations':ex,'deletion_extendible':{str(x):[sorted(b) for b in D[x]] for x in D},'partition_counts':{str(x):len(D[x])//2 for x in D},'intersection':[], 'circuits':[sorted(c) for c in circuits], 'components':[sorted(c) for c in components],'parallel_pairs':[sorted(c) for c in circuits if len(c)==2],'rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
(L/'independent-math.json').write_text(json.dumps(r,indent=2));print({k:v for k,v in r.items() if k not in ['bases','deletion_extendible','circuits']})
# Read and bind every specifically required artifact, including all Lean bodies.
paths=[A/p for p in ['SUMMARY.md','CANDIDATE.md','results.json','raw/332371.jsonl','matroid-certificate.json','REPRODUCE.md','replay-result.json','lean-source-manifest.json','ARTIFACTS.json']]+list((A/'lean').glob('*.lean'))+list((A/'sources').glob('*.receipt.json'))
(L/'read-inputs.json').write_text(json.dumps({str(p):{'bytes':len(p.read_bytes()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in paths},indent=2))
(L/'lean-reading.txt').write_text('\n\n'.join(str(p)+'\n'+p.read_text() for p in (A/'lean').glob('*.lean')))
(L/'target-record.json').write_text(json.dumps(json.loads((A/'results.json').read_text())['332371'],indent=2))
frozen('frozen-after-math')
