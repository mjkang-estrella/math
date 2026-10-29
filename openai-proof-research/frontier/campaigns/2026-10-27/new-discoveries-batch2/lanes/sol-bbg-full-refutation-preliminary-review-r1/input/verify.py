import os,resource,signal
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,30));signal.alarm(40)
from pathlib import Path
from fractions import Fraction as F
from math import isqrt
import json,datetime
L=Path(__file__).parent;c=json.loads((L/'checks.json').read_text());D=10**30
assert json.loads((L/'prefix-replay.json').read_text())==json.loads((L/'prefix-original.json').read_text())
assert c['status']=='PASS';assert [r['k'] for r in c['tail_rows']]==list(range(30,1600))
assert F(c['tail_upper'])==sum((F(r['upper_scaled'],D) for r in c['tail_rows']),F(2400,2**40))
base=json.loads((L/'prefix-replay.json').read_text());pr=F(base['partial_sums'][-1]['upper_scaled'],base['scale'])
P=c['pi_scale'];pl=c['pi_lower_scaled'];pu=c['pi_upper_scaled'];al=F(P,2*pu);au=F(P,2*pl)
x=al;p0,p1=0,1;q0,q1=1,0;grids={}
while True:
 z=x.numerator//x.denominator;p=z*p1+p0;q=z*q1+q0
 if q>1:grids[q]=(p,max(abs(al-F(p,q)),abs(au-F(p,q))))
 if q>2**810:break
 p0,p1=p1,p;q0,q1=q1,q;x=1/(x-z)
for row in c['tail_rows']:
 X=2**row['k'];q=row['q'];m=row['block'];p,eps=grids[q];delta=F(1,q)-(m-1)*eps
 assert 2<=m<=q and delta>0
 b=F((X+m-1)//m,X)*(1+F(11,10)/(delta*isqrt(X)))
 assert F(row['upper_scaled'],D)>=b
for row in c['finite_rows']:
 X=2**row['k'];q=row['grid_q'];Z=row['Z'];p,eps=grids[q]
 r=F(isqrt((24*D*D+X-1)//X)+1,D);err=Z*eps
 rad=(r+err)*q;left=(F(q,4)-rad).__floor__()-1;right=(F(q,4)+rad).__ceil__()+1
 assert 0<left<=right<q and right-left<q
 assert 2*F(pu,P)*(r+2*err+F(3,q))<F(1,2)
 assert row['A']==max(10001,X) and Z==2*X and q>=Z
 assert row['enumerated']==right-left+1
 inv=pow(p,-1,q);hits=sum(row['A']<=(j*inv)%q<Z for j in range(left,right+1));assert hits==row['hits']
 pr+=F(row['upper_scaled'],D)+F(row['omitted_upper'])
assert pr==F(c['finite_upper']);assert pr+F(c['tail_upper'])==F(c['total_upper'])
assert F(c['total_upper'])<F(2163292,1000000)<F(21635,10000)<F(json.loads((L/'constant.json').read_text())['Ei_lower'])
assert 60**40<2*59**40
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','scope':'exact replay of finite10000 prefix; all recorded tail witnesses, finite-window coverage/padding and residue counts; rational separator aggregation. Analytic lemmas remain ordinary proof, not kernel-checked.','tail_upper_less_than':'0.000134','finite_upper_less_than':'2.163159','full_upper_less_than':'2.163292','AS':512*1024**2,'CPU':30,'wall_alarm':40,'BLAS_threads':1}
(L/'verification.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
