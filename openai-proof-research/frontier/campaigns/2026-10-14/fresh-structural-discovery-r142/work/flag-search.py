from itertools import combinations
import json
from pathlib import Path
R=Path(__file__).resolve().parents[1]
def downsets(n):
 out=[]
 for m in range(1<<(1<<n)):
  A={s for s in range(1<<n) if m>>s&1}
  if all((s^(1<<i)) in A for s in A for i in range(n) if s>>i&1):out.append(A)
 return out
def lexcomp(A,n):
 C=set()
 for d in range(n+1):
  row=sorted((s for s in range(1<<n) if s.bit_count()==d),key=lambda s:tuple((s>>i)&1 for i in range(n)))
  C.update(row[:sum(s.bit_count()==d for s in A)])
 return C
def b0(D,n):return [sum(s.bit_count()==d and not any((s^(1<<i)) in D for i in range(n) if s>>i&1) for s in D) for d in range(n+1)]
def names(A,n):return ['1' if not s else ''.join('x'+str(i+1) for i in range(n) if s>>i&1) for s in sorted(A)]
for n in [2,3,4]:
 sets=downsets(n); found=[];pairs=0
 for A in sets:
  for B in sets:
   if not B<=A:continue
   pairs+=1;D=A-B;L=lexcomp(A,n)-lexcomp(B,n);a=b0(D,n);b=b0(L,n)
   if any(x>y for x,y in zip(a,b)):
    found.append(dict(A=names(A,n),B=names(B,n),D=names(D,n),L=names(L,n),b0=a,lex_b0=b))
 print(n,len(sets),pairs,'failures',len(found));print(json.dumps(found[:2],indent=2))
 (R/f'packet/private/flags-n{n}.json').write_text(json.dumps(dict(n=n,sets=len(sets),pairs=pairs,failures=found),indent=2))
