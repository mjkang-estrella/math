# Standalone exact validation. No numerical solver or check.py import.
import os
for k in ['OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','OMP_NUM_THREADS']:os.environ[k]='1'
import resource,signal,json,hashlib
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(20,20));signal.alarm(25)
b=Path(__file__).resolve().parent
B=[6,9,10,16,18,20,24,25];A=[x+30 for x in B];S=[9,16,18,20,24,25]
e={d:sum(x%d==0 for x in A)-sum(x%d==0 for x in B) for d in range(1,56)}
assert min(e.values())>=0
D=sum(A)-sum(B)
c=[1]+[0]*D
for v in A:
 for j in range(D,v-1,-1):c[j]-=c[j-v]
for v in B:
 for j in range(v,D+1):c[j]+=c[j-v]
# Verify full exact denominator*quotient=numerator, including every degree.
def mulfactor(a,v):
 out=a+[0]*v
 for j,x in enumerate(a):out[j+v]-=x
 return out
num=[1];rebuild=c[:]
for v in A:num=mulfactor(num,v)
for v in B:rebuild=mulfactor(rebuild,v)
assert num==rebuild
reach=[True]+[False]*55
for j in range(1,56):reach[j]=any(j>=s and reach[j-s] for s in S)
inside=[x for x in A if reach[x]];outside=[x for x in A if not reach[x]]
assert len(inside)<len(S)
# Every nonrepresentable integer is validated by independent bounded combination enumeration.
from itertools import product
exact={sum(v*t for v,t in zip(S,cs)) for cs in product(*(range(56//s+1) for s in S)) if sum(v*t for v,t in zip(S,cs))<=55}
assert [i for i,v in enumerate(reach) if v]==sorted(exact)
assert min(c)>=0 and c==c[::-1]
out={'status':'PASS','m':30,'n':26,'B':B,'A':A,'semigroup_generators':S,'A_in_semigroup':inside,'A_outside_semigroup':outside,'lhs':len(inside),'rhs':len(S),'cyclotomic_exponents_nonzero':{k:v for k,v in e.items() if v},'polynomial_degree':D,'polynomial_minimum':min(c),'polynomial_maximum':max(c),'polynomial_coefficients':c,'scope':'Failure of HSOP criterion only, NOT a source counterexample','identity':'full exact denominator times quotient equals numerator'}
(b/'exact-obstruction.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k!='polynomial_coefficients'},indent=2))
