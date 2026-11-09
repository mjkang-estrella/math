#!/usr/bin/env python3
import resource,os,json
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(30,30))
for v in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[v]='1'
from sympy import ZZ
from sympy.polys.rings import ring
from pathlib import Path
R,q=ring('q',ZZ);M=[R.one]
for m in range(10):M.append(M[m]+sum((q**(r+1)*M[r]*M[m-1-r] for r in range(m)),R.zero))
a=[[M[5+i+j] for j in range(3)] for i in range(3)]
f=a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])-a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])+a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]);sq=f*f
out={'delta_3_shift5':str(f),'square':str(sq),'negative_square_coefficients':sorted((e[0],int(c)) for e,c in sq.items() if c<0)}
Path(__file__).with_name('toda-obstruction.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))

a=[[M[6+i+j] for j in range(3)] for i in range(3)]
f6=a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])-a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])+a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0])
g=json.loads(Path(__file__).with_name('compound-checks.json').read_text())['geometric_specialization']
expected=sum((int(c)*q**(int(e)+5) for e,c in g),R.zero)
assert f6==expected
out['direct_source_shift6_matches_compound']=True
Path(__file__).with_name('toda-obstruction.json').write_text(json.dumps(out,indent=2))
