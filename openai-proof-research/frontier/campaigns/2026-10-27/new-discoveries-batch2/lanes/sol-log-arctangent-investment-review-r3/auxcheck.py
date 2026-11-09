import os,resource,json,hashlib
from pathlib import Path
from fractions import Fraction as F
for x in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[x]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(35,35))
o=Path(__file__).resolve().parent;b=o.parent.parent
# Exact Q(sqrt(17)); keys are rational frequency coordinates (r,s).
z=(F(0),F(0)); one=(F(1),F(0))
def q(a=0,c=0):return F(a),F(c)
def add(a,b):return a[0]+b[0],a[1]+b[1]
def mul(a,b):return a[0]*b[0]+17*a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def scale(a,c):return mul(a,q(c))
def plus(*ps):
 r={}
 for p in ps:
  for k,v in p.items():r[k]=add(r.get(k,z),v)
 return {k:v for k,v in r.items() if v!=z}
def times(p,r):
 out={}
 for k,v in p.items():
  for l,w in r.items():
   m=add(k,l);out[m]=add(out.get(m,z),mul(v,w))
 return {k:v for k,v in out.items() if v!=z}
def scal(p,a):return {k:mul(v,a) for k,v in p.items() if mul(v,a)!=z}
def hyp(k,odd=False):return {k:q(F(1,2)),scale(k,-1):q(F(-1 if odd else 1,2))}
c=lambda k:hyp(k);s=lambda k:hyp(k,True)
d=q(0,1);alpha=q(F(5,2),F(1,2));beta=q(F(5,2),F(-1,2))
A=scal(plus(c(q(4)),scal(times(c(q(1)),c(d)),q(-1)),scal(times(s(q(1)),s(d)),q(0,F(5,17)))),q(F(1,2)))
a=q(F(-1,4),F(5,68))
Ac=plus(scal(plus(c(q(1,1)),scal(c(q(-1,1)),q(-1))),a),scal(plus(c(q(4)),scal(c(q(-1,1)),q(-1))),q(F(1,2))))
As=plus(scal(times(s(d),s(q(1))),q(F(-1,2),F(5,34))),times(s(q(F(3,2),F(1,2))),s(beta)))
assert A==Ac==As
B=scal(times(s(q(1)),plus(c(q(5)),scal(c(d),q(-1)))),q(F(1,2)))
assert B==times(times(s(q(1)),s(alpha)),s(beta))
assert mul(alpha,beta)==q(2)
limA=add(mul(q(F(-1,2),F(5,34)),d),mul(q(F(3,2),F(1,2)),beta))
assert limA==q(2)
assert F(4)**2<17<F(5)**2
assert F(3,2)**2*2>4
assert sum(F(2)**i/F(__import__('math').factorial(i)) for i in range(5))==7
# Target-specific complete cached registry path screen; no proof-body absence inferred.
paths=[b/'lanes/sol-cascade-rate-preliminary-review-r1/sources/omega-D5.json',b/'lanes/sol-cascade-rate-preliminary-review-r1/sources/omega-Problems.json',b/'lanes/sol-fresh-analysis-discovery-r7/sources/openai-preprints-tree.json',b/'lanes/sol-fresh-analysis-discovery-r7/sources/count-registry.json',b/'lanes/sol-fresh-analysis-discovery-r7/sources/current-CONTENTS.md']
terms=['2405.13618','aadm240618001m','arctan','mihok','raiss','raïss','stolars','stabiliz','logarithm']
res=[];before=json.loads((o/'hash-before.json').read_text())
for p in paths:
 raw=p.read_bytes();h=hashlib.sha256(raw).hexdigest();before.setdefault(str(p.relative_to(b)),h)
 if p.suffix=='.json':
  data=json.loads(raw)
  if isinstance(data,dict) and 'tree' in data:
   assert data.get('truncated') is False
   lines=[x['path'] for x in data['tree']]
  else:lines=raw.decode().splitlines()
 else:lines=raw.decode().splitlines()
 hits={t:[x for x in lines if t in x.lower()] for t in terms}
 res.append({'file':str(p.relative_to(b)),'sha256':h,'entries_or_lines':len(lines),'hits':hits})
(o/'hash-before.json').write_text(json.dumps(before,indent=2)+'\n')
(o/'aux-results.json').write_text(json.dumps({'A_identities':True,'B_identity':True,'A_over_t2_limit':2,'B_over_t3_limit':2,'registry_screen':res},indent=2)+'\n')
print('PASS exact auxiliary identities/limits and registry screen; analytic inequalities are proved in review.md')
