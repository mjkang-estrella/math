from run import *
from fractions import Fraction as F
import re
aliases=['crossing number','Perles','Borwein','Kontsevich','rhombus','strong Macdonald','wide partition','0-1 conjecture','rational definite summation','Brown.Colbourn','Neggers','slit plane']
results=[];inv=[]
for p in sorted((B/'lanes').glob('*/*.md')):
 if p.parent==L or p.name not in ['SCOUTING.md','SUMMARY.md','STATUS.md','discovery.md']:continue
 if p.stat().st_size>150000:continue
 h=sha(p);t=p.read_text(errors='replace');hits=[a for a in aliases if re.search(a,t,re.I)]
 inv.append({'path':str(p),'sha256':h,'hits':hits});assert sha(p)==h
dump('semantic-dedup.json',inv)
for n in range(1,51):
 # van Hoeij Eq(2), including a genuinely superlinear pole.
 def b(k):return k+n*n+1
 s=sum((1/F(b(k))+1/F(b(k+n+1))-1/F(b(2*k))-1/F(b(2*k+1)) for k in range(n+1)),F(0))
 assert s==0
 # Reflection preserves multiplicity, with the required sign.
 for d in range(1,5):
  x=sum((1/F(b(k))**d for k in range(n+1)),F(0))
  y=(-1)**d*sum((1/F(k-n-n*n-1)**d for k in range(n+1)),F(0))
  assert x==y
 results.append(n)
dump('exact-checks.json',{'integer_n_checked':results,'reflection_multiplicities':[1,2,3,4],'arithmetic':'fractions.Fraction exact','scope':'replay of known source affine block identities; no conjecture proof or search clearance','counterexamples':0})
repo=B.parents[3]
adm=json.loads((L/'administrative-bindings.json').read_text())
for p in [repo/'AGENTS.md',repo/'sources/upstream.json',repo/'sources/CONTENTS.md',B/'lanes/root-shuffle-disposition-r2/STATUS.md']:
 if p.exists():
  q=L/'administrative'/('ancestor-'+p.name if p.name=='AGENTS.md' else p.name)
  a=sha(p);shutil.copyfile(p,q);assert a==sha(q)==sha(p);adm.append({'original':str(p),'copy':str(q),'sha256':a})
dump('administrative-bindings.json',adm)
print('semantic report files',len(inv),'hits',sum(bool(x['hits']) for x in inv),'exact checks PASS')
