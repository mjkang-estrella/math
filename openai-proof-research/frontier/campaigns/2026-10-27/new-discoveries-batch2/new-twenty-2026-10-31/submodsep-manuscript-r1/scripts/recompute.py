from pathlib import Path
from itertools import combinations,permutations
from collections import Counter
from fractions import Fraction
from math import comb,lcm,factorial
import json,hashlib
L=Path(__file__).resolve().parents[1];E=L/'evidence/expanded-corpus-r198'
coords=[(i,) for i in range(5)]+list(combinations(range(5),2)); ix={s:i for i,s in enumerate(coords)}
q=lambda x:sum(1<<i for i,s in enumerate(coords) if all(x>>v&1 for v in s))
G={q(x) for x in range(32)}
cycle=json.loads((L/'evidence/submodsep-review-r1/known-criterion-cycle.json').read_text()); cycleout=[]
for i,row in enumerate(cycle):
 a,b,c=row['a'],row['b'],row['c_good']; meet=a&c;join=a|c
 assert meet==row['meet'] and join==row['join'] and b in [meet,join]
 other=join if b==meet else meet
 assert c in G and all(x not in G for x in [a,b,other])
 assert b==cycle[(i+1)%len(cycle)]['a']
 cycleout.append(dict(row,other=other,c_input=next(x for x in range(32) if q(x)==c),good_status={'a':False,'b':False,'c':True,'other':False}))
rows=json.loads((E/'outputs/submod-dual-compressed.json').read_text())['support']
bal=Counter();perms=list(permutations(range(5)));nsub=0
for p in perms:
 index=[ix[tuple(sorted(p[v] for v in c))] for c in coords]
 def image(m):return sum(1<<index[i] for i in range(15) if m>>i&1)
 assert {image(m) for m in G}==G
 for row in rows:
  w=row['weight'];assert type(w)==int and w>0
  if row['kind']=='submodular':
   (u,cu),(v,cv),(a,ca),(b,cb)=row['terms'];assert [cu,cv,ca,cb]==[1,1,-1,-1]
   assert u==a&b and v==a|b
   assert image(u)==image(a)&image(b) and image(v)==image(a)|image(b)
   for m,c in row['terms']:bal[image(m)]+=w*c
   nsub+=1
  else:
   m=row['point'];good=row['kind']=='good';assert (image(m) in G)==good
   bal[image(m)]+=w*(1 if good else -1)
assert not any(bal.values())
small=[]
for d,r in [(2,2),(3,2),(3,3),(4,2)]:
 cs=[s for k in range(1,r+1) for s in combinations(range(d),k)];n=len(cs)
 vals=[Fraction(str(v)).limit_denominator(10**6) for v in json.loads((E/f'outputs/submod-values-{d}-{r}.json').read_text())]
 assert len(vals)==1<<n
 good={sum(1<<i for i,s in enumerate(cs) if all(x>>v&1 for v in s)) for x in range(1<<d)}
 assert all(v<=-1 if m in good else v>=0 for m,v in enumerate(vals))
 count=0
 for i,j in combinations(range(n),2):
  for m in range(1<<n):
   if (m>>i&1) or (m>>j&1):continue
   assert vals[m]+vals[m|(1<<i)|(1<<j)]<=vals[m|(1<<i)]+vals[m|(1<<j)]
   count+=1
 assert count==comb(n,2)*2**(n-2)
 C=max(Fraction(0),-min(vals));den=lcm(*(v.denominator for v in vals),C.denominator)
 # Full-cube integer witness, both constant slices.
 full=[int(den*(v+C*(1-z))) for z in [0,1] for v in vals]
 assert all(full[m]>=0 for m in range(1<<n))
 (L/f'receipts/witness-{d}-{r}.json').write_text(json.dumps({'d':d,'r':r,'constant_coordinate_most_significant':True,'values':full,'scale':den,'shift':str(C)},indent=2)+'\n')
 small.append({'d':d,'r':r,'nonconstant_coordinates':n,'full_dimension':n+1,'face_points':len(vals),'elementary_inequalities':count,'constant0_shift':str(C),'integer_scale':den})
raw=E/'raw/341850.jsonl';obj=json.loads(raw.read_text());res=json.loads((E/'results.json').read_text())['341850']
rawhash=hashlib.sha256(raw.read_bytes()).hexdigest()
# Raw provenance may bind the line without terminal newline: report both explicitly.
rawlinehash=hashlib.sha256(raw.read_bytes().rstrip(b'\r\n')).hexdigest()
report={'pass':True,'coordinates':coords,'full_dimension':1+sum(comb(5,k) for k in [1,2]),'good_masks':sorted(G),'cycle':cycleout,'cycle_bound':-len(cycle),'support':rows,'permutations':len(perms),'expanded_submodular_rows':nsub,'touched_masks':len(bal),'balance_zero':True,'bound':-len(perms)*sum(r['weight'] for r in rows if r['kind']=='good'),'small_cases':small,'raw_file_sha256':rawhash,'raw_line_without_newline_sha256':rawlinehash,'recorded_raw_sha256':res['provenance']['raw_sha256']}
assert report['bound']==-840 and len(perms)==factorial(5)
(L/'receipts/recomputation.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ['support','good_masks','cycle','coordinates']},indent=2))
