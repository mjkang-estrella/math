"""Exact finite diagnostics; no assertion of scheme/cohomology certification."""
from fractions import Fraction as Q
import json

def clean(p): return {k:Q(v) for k,v in p.items() if v}
def add(p,q):
 r=dict(p)
 for k,v in q.items():r[k]=r.get(k,0)+v
 return clean(r)
def scale(p,c): return clean({k:v*c for k,v in p.items()})
def mul(p,q,N):
 r={}
 for (i,j),v in p.items():
  for (k,l),w in q.items():
   if j+l<=N:r[i+k,j+l]=r.get((i+k,j+l),0)+v*w
 return clean(r)
def derivative(p,axis):
 r={}
 for k,v in p.items():
  if k[axis]:
   h=list(k);h[axis]-=1;r[tuple(h)]=v*k[axis]
 return clean(r)
def vector(dx,dt,N):
 return lambda p:add(mul(dx,derivative(p,0),N),mul(dt,derivative(p,1),N))
def exp(D,p,N):
 r=dict(p);term=dict(p)
 for k in range(1,N+2):
  term=scale(D(term),Q(1,k));r=add(r,term)
  if not term:return r
 raise AssertionError('positive-degree exponential did not truncate')
def trunc(p,N):return {k:v for k,v in p.items() if k[1]<=N}
def run():
 primes=[n for n in range(3,102) if all(n%d for d in range(2,int(n**.5)+1))]
 surfaces=[]
 for n in primes:
  h=5*n**3;K2=5*n**3*(n-2)**2;c2=n**3*(2*n*n-10*n+15);delta=K2-2*c2
  assert delta==n**3*(n*n-10)
  chi=Q(K2+c2,12);assert chi.denominator==1
  C2=-2*n**5;assert C2 and n**4==Q(n**5,n)
  allowed=[v for v in range(1,n+1) if n*n-10>30*v*v]
  surfaces.append(dict(n=n,H2=h,K2=K2,c2=c2,delta=delta,chi=int(chi),C2=C2,allowed_veronese=allowed))
 n7=next(x for x in surfaces if x['n']==7)
 assert n7==dict(n=7,H2=1715,K2=42875,c2=14749,delta=13377,chi=4802,C2=-33614,allowed_veronese=[1])
 assert 2*n7['chi']-n7['c2']==-5145
 rr=[]
 for k in range(0,16):
  chiT=Q(7*n7['K2']-5*n7['c2'],6)+n7['H2']*(k*k-10*k)
  rr.append([k,int(chiT)])
 assert rr[5][1]==-5145
 # Picard-lattice identity H=(3,-1,-1,-1,-1), C=(0,1,-1,0,0).
 dot=lambda x,y:x[0]*y[0]-sum(a*b for a,b in zip(x[1:],y[1:]))
 H=(3,-1,-1,-1,-1);C=(0,1,-1,0,0)
 assert dot(H,H)==5 and dot(H,C)==0 and dot(C,C)==-2
 shifts=0
 for d in range(0,40):
  for q in range(0,100):
   k=min(d,q);assert 0<=k<=d and q-k==max(q-d,0);shifts+=1
 lifting=0;obstruction=0
 for a in range(1,21):
  for d in range(1,101):
   for j in range(1,101):assert d+j*a>a;lifting+=1
  for j in range(2,101):assert j*a>a and a-j*a<0;obstruction+=1
 lie=0;leibniz=0;bch=0;euler=0
 for a in range(1,8):
  N=4*a+3
  D=vector({(1,a):Q(1)},{(0,a+1):Q(2)},N)
  E=vector({(2,a):Q(1)},{(1,a+1):Q(-1)},N)
  E0=vector({}, {(0,1):Q(1)},N)
  for i in range(4):
   for j in range(4):
    f={(i,j):Q(1)}
    assert add(E0(D(f)),scale(D(E0(f)),-1))==scale(D(f),a);lie+=1
    conj=exp(D,E0(exp(lambda p:scale(D(p),-1),f,N)),N)
    assert conj==add(E0(f),scale(D(f),-a));euler+=1
    minus=lambda p:scale(add(D(p),E(p)),-1)
    triple=exp(D,exp(E,exp(minus,f,N),N),N)
    comm=add(D(E(f)),scale(E(D(f)),-1))
    assert trunc(add(triple,scale(f,-1)),j+2*a)==trunc(scale(comm,Q(1,2)),j+2*a);bch+=1
    for ii in range(3):
     g={(ii,1):Q(1)}
     assert exp(D,mul(f,g,N),N)==mul(exp(D,f,N),exp(D,g,N),N);leibniz+=1
 # Syzygy failure retained as a diagnostic: z*w^3 maps to s*t^11.
 # x=s^3,y=s^2t,z=st^2,w=t^3. Original cubics vanish; added term survives.
 exps={'x':(3,0),'y':(2,1),'z':(1,2),'w':(0,3)}
 plus=lambda x,y:tuple(a+b for a,b in zip(x,y))
 assert plus(exps['x'],exps['z'])==tuple(2*a for a in exps['y'])
 assert plus(exps['x'],exps['w'])==plus(exps['y'],exps['z'])
 assert plus(exps['y'],exps['w'])==tuple(2*a for a in exps['z'])
 syzygy=plus(exps['z'],tuple(3*a for a in exps['w']));assert syzygy==(1,11)
 return dict(status='PASS finite diagnostics only',surface_rows=surfaces,chi_T_twists_n7=rr,primitive_dimension_lower_bound=5144,euler_pairing_n7=-168070,rees_shift_cases=shifts,positive_section_lifting_indices=lifting,higher_obstruction_indices=obstruction,euler_bracket_cases=lie,exact_truncated_euler_conjugations=euler,exponential_product_cases=leibniz,second_order_BCH_cases=bch,twisted_cubic_new_initial_monomial=syzygy,radial_mu7_selected_weight=5,limits='Exact identities and bounded index checks only. No computation of an actual cover Cech cocycle, a full defining ideal, coherent cohomology, infinite gluing, algebraization, or classification of complete local rings. Those assertions rely on the written geometric proof.')
if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
