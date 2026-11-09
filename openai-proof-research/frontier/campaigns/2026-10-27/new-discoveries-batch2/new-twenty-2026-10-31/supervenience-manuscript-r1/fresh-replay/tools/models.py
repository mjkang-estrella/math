from pathlib import Path
import itertools,json
D=Path(__file__).resolve().parents[1]
def bad(n,a,b):
 return sum(1<<(u*n+v) for u in range(n) for v in range(n) if ((a>>u)&1)==((a>>v)&1) and ((b>>u)&1)!=((b>>v)&1))
counts={};negative={}
for n in range(4):
 total=0;mask=(1<<n)-1
 for a,c,b in itertools.product(range(1<<n),repeat=3):
  cells=[a&c,a&(mask^c),(mask^a)&c,(mask^a)&(mask^c)]
  guardbad=[bad(n,x,x&b) for x in cells]
  target=bad(n,a,b)&bad(n,c,b)
  for e in range(1<<(n*n)):
   unary=lambda x,y:not(e&bad(n,x,y))
   assert unary(a,a&b)==all(not((e>>(u*n+v))&1) or not((a>>u)&1 and (a>>v)&1) or ((b>>u)&1)==((b>>v)&1) for u in range(n) for v in range(n))
   lhs=not(e&target);rhs=not any(e&t for t in guardbad)
   assert lhs==rhs;total+=1
   if lhs!=all(unary(x,b) for x in cells):negative.setdefault('ungated_cells',dict(n=n,a=a,c=c,b=b,e=e))
   for k in range(4):
    if lhs!= (not any(e&t for i,t in enumerate(guardbad) if i!=k)):negative.setdefault('omit_cell_'+str(k),dict(n=n,a=a,c=c,b=b,e=e))
 counts[n]=total
# Nested formula semantics independently evaluated on all two-world ternary frames.
def atom(k):return ('a',k)
def dep(a,c,b):return ('d',a,c,b)
def conj(a,b):return ('c',a,b)
def neg(a):return ('n',a)
def tr(f):
 if f[0]=='a':return f
 if f[0]=='n':return neg(tr(f[1]))
 if f[0]=='c':return conj(tr(f[1]),tr(f[2]))
 a,c,b=map(tr,f[1:]);cs=[conj(a,c),conj(a,neg(c)),conj(neg(a),c),conj(neg(a),neg(c))]
 gs=[('u',x,conj(x,b)) for x in cs]
 return conj(conj(gs[0],gs[1]),conj(gs[2],gs[3]))
def ev(f,w,e,vs):
 t=f[0]
 if t=='a':return bool(vs[f[1]]&(1<<w))
 if t=='n':return not ev(f[1],w,e,vs)
 if t=='c':return ev(f[1],w,e,vs) and ev(f[2],w,e,vs)
 args=f[1:-1];b=f[-1]
 return all(not(e&(1<<(w*4+u*2+v))) or not all(ev(a,u,e,vs)==ev(a,v,e,vs) for a in args) or ev(b,u,e,vs)==ev(b,v,e,vs) for u in range(2) for v in range(2))
p,q,r=map(atom,range(3));h=dep(p,q,r)
fs=[h,dep(h,q,neg(h)),dep(conj(p,h),neg(h),dep(q,r,p))]
k=0
for e in range(256):
 for vs in itertools.product(range(4),repeat=3):
  for f in fs:
   for w in range(2):assert ev(f,w,e,vs)==ev(tr(f),w,e,vs);k+=1
out={'local_pair_exhaustive_counts':counts,'nested_pointed_cases':k,'negative_controls':negative,'scope':'All local binary relations and A,C,B truth sets for n=0..3; all ternary frames and three-atom valuations for nested formulas on two worlds. Finite evidence only.'}
(D/'logs/model-check.json').write_text(json.dumps(out,indent=2));print(out)
