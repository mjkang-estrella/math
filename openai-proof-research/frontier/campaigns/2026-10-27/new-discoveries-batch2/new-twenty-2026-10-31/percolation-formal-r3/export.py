from pathlib import Path
import json
r=Path(__file__).resolve().parent
pts=[(1,i//5,i%5) for i in range(25)]+[(0,1,i) for i in range(5)]+[(0,0,1)]
inc=[[sum(x*y for x,y in zip(p,l))%5==0 for l in pts] for p in pts]
on=[[p for p in range(31) if inc[p][l]] for l in range(31)]
th=[[l for l in range(31) if inc[p][l]] for p in range(31)]
# Lean bits: false :: xs then true :: xs, with xs in previous enumeration.
def bits(n):
 b=[[]]
 for _ in range(n):b=[ [v]+xs for xs in b for v in (False,True)]
 return b
cnf=[]
def gate(s,t):
 for b in bits(len(s)):
  if not t(b):cnf.append([-v if x else v for v,x in zip(s,b)])
for off,out in [(0,62),(31,93)]:
 for l in range(31):gate([out+l+1]+[off+p+1 for p in on[l]],lambda b:b[0]==(sum(b[1:])>=5))
for p in range(31):gate([32+p,1+p]+[63+l for l in th[p]],lambda b:b[0]==any(b[1:]))
for p in range(31):gate([32+p]+[94+l for l in th[p]],any)
for v in range(31):
 for l in range(31):gate([125+31*v+p for p in on[l]],lambda b:sum(b)!=5)
cnf.append([-32-p for p in range(31)])
for v in range(31):cnf.append([-1-v,-125-31*v-v])
for v in range(31):
 for p in range(31):
  if p!=v:cnf.append([-1-v,-1-p,125+31*v+p])
for name,cs in [('input',cnf),('normalized',cnf+[[1],[26],[31]])]:
 with (r/(name+'.cnf')).open('w') as f:
  f.write(f'p cnf 1085 {len(cs)}\n');f.writelines(' '.join(map(str,c))+' 0\n' for c in cs)
(r/'clauses.json').write_text(json.dumps(cnf))
print({'variables':1085,'clauses':len(cnf)})
