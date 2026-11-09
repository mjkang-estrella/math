#!/usr/bin/env python3
import os,resource,json
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(60,60))
for v in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[v]='1'
from sympy.polys.rings import ring
from sympy import ZZ
from pathlib import Path
R,*d=ring('d0,d1,d2,d3,d4,d5',ZZ)
a=[[R.one if i==j else R.zero for j in range(6)] for i in range(3)]
for _ in range(6):a=[[sum((a[i][t] for t in range(max(0,j-1),min(6,j+2))),R.zero)*d[j] for j in range(6)] for i in range(3)]
a=[x[:3] for x in a]
f=a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])-a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])+a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0])
neg=sorted((list(e),int(c)) for e,c in f.items() if c<0)
p=Path(__file__).parent;ref=json.loads((p/'compound-checks.json').read_text());expected=sorted((x['exponents'],x['coefficient']) for x in ref['negative_multivariate_terms']);assert neg==expected
# Check every coefficient after d_h=q^h against independently computed q determinant.
g={}
for e,v in f.items():
 j=sum(i*e[i] for i in range(6));g[j]=g.get(j,0)+int(v)
assert sorted(g.items())==[tuple(x) for x in ref['geometric_specialization']]
(p/'independent-checks.json').write_text(json.dumps({'status':'PASS','terms':len(f),'negative_terms':neg,'direct_3_by_3_matches_compound':True,'coefficient_d0_6_d1_3_d2_5_d3_2_d4_2':int(f.get((6,3,5,2,2,0),0))},indent=2));print('PASS',len(f),len(neg))
