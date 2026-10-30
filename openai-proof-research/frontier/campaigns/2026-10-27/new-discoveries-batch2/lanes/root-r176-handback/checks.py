"""Exact, bounded diagnostics, not an all-order proof. Standard library only."""
import itertools as it,math,json,random
from pathlib import Path
class DS:
 def __init__(self,n):self.p=list(range(n));self.count=n
 def root(self,a):
  while self.p[a]!=a:self.p[a]=self.p[self.p[a]];a=self.p[a]
  return a
 def join(self,a,b):
  a=self.root(a);b=self.root(b)
  if a!=b:self.p[a]=b;self.count-=1
def rectangles(P):
 xs=sorted({x for x,y in P});ys=sorted({y for x,y in P})
 return [(a,b,c,d) for a in xs for b in xs if a<=b for c in ys for d in ys if c<=d and all((x,y) in P for x in range(a,b+1) for y in range(c,d+1))]
def rook(P,R,k):
 cells=sorted(P)
 def attack(a,b):
  x,y=a;u,v=b
  return (x==u and all((x,j) in P for j in range(min(y,v),max(y,v)+1))) or (y==v and all((i,y) in P for i in range(min(x,u),max(x,u)+1)))
 configs=[c for c in it.combinations(cells,k) if not any(attack(a,b) for a,b in it.combinations(c,2))];idx={c:i for i,c in enumerate(configs)};ds=DS(len(configs))
 switches=[]
 for a,b,c,d in R:
  if a<b and c<d:switches.append((((a,c),(b,d)),((a,d),(b,c))))
 for cfg,i in idx.items():
  s=set(cfg)
  for p,q in switches:
   if set(p)<=s:
    other=tuple(sorted(s-set(p)|set(q)));assert other in idx;ds.join(i,idx[other])
 return ds.count
def hilbert(P,R,k):
 V=sorted({(x+i,y+j) for x,y in P for i in [0,1] for j in [0,1]});vi={v:i for i,v in enumerate(V)}
 mons=list(it.combinations_with_replacement(range(len(V)),k));idx={m:i for i,m in enumerate(mons)};ds=DS(len(mons))
 if k>=2:
  tails=list(it.combinations_with_replacement(range(len(V)),k-2))
  for a,b,c,d in R:
   p=(vi[a,c],vi[b+1,d+1]);q=(vi[a,d+1],vi[b+1,c])
   for t in tails:ds.join(idx[tuple(sorted(t+p))],idx[tuple(sorted(t+q))])
 return len(V),ds.count
def diagnostic(P,degree):
 R=rectangles(P);rs=[rook(P,R,k) for k in range(degree+1)];H=[hilbert(P,R,k)[1] for k in range(degree+1)];v=hilbert(P,R,0)[0];d=v-len(P)
 pred=[sum(rs[j]*math.comb(d+k-j-1,k-j) for j in range(k+1)) for k in range(degree+1)]
 return dict(cells=sorted(P),vertices=v,rectangles=len(R),rook_prefix=rs,H=H,predicted_H_if_conjecture=pred,matches=H==pred,degree=degree)
def groebner_objection(P):
 V=sorted({(x+i,y+j) for x,y in P for i in [0,1] for j in [0,1]});vi={v:i for i,v in enumerate(V)};n=len(V)
 def mon(p):return tuple(sum(v==i for v in p) for i in range(n))
 def key(p):return tuple(-x for x in p)
 def div(a,b):return all(x>=y for x,y in zip(a,b))
 G=[]
 for a,b,c,d in rectangles(P):
  p=mon((vi[a,c],vi[b+1,d+1]));q=mon((vi[a,d+1],vi[b+1,c]));G.append((max(p,q,key=key),min(p,q,key=key)))
 def reduce(p):
  for steps in range(10000):
   for u,v in G:
    if div(p,u):p=tuple(x-y+z for x,y,z in zip(p,u,v));break
   else:return p
  raise RuntimeError('reduction cap')
 def show(p):return [V[i] for i,e in enumerate(p) for j in range(e)]
 for (u,v),(w,z) in it.combinations(G,2):
  l=tuple(max(x,y) for x,y in zip(u,w));a=tuple(x-y+t for x,y,t in zip(l,u,v));b=tuple(x-y+t for x,y,t in zip(l,w,z));ar=reduce(a);br=reduce(b)
  if ar!=br:return dict(vertices=V,generators=[[show(u),show(v)],[show(w),show(z)]],S_terms=[show(a),show(b)],irreducible_remainders=[show(ar),show(br)],order='grevlex; variables descending lexicographic coordinates; leading antidiagonals')
 return None
if __name__=='__main__':
 shapes={'square':set(it.product(range(2),repeat=2)),'L':{(0,0),(0,1),(1,0)}}
 for n in [3,4,5]:shapes[f'frame{n}']={(i,j) for i in range(n) for j in range(n) if i in [0,n-1] or j in [0,n-1]}
 shapes['twoholes']={(i,j) for i in range(5) for j in range(3)}-{(1,1),(3,1)}
 shapes['cornercycle']={(0,1),(1,0),(2,1),(1,2)}
 rng=random.Random(176)
 for s in range(8):shapes[f'punctured{s}']={(i,j) for i in range(5) for j in range(5) if rng.random()<.72}
 rows={name:diagnostic(P,4 if name in ['square','L','frame3'] else 3) for name,P in shapes.items()}
 # Exact polynomial identity coefficients using convolution.
 f=[2,-4,6,-4,2];g=[1,-1,1];sq=[2*sum(g[i]*g[k-i] for i in range(3) if 0<=k-i<3) for k in range(5)];assert f==sq
 out=dict(scope='finite exact diagnostics only; no nomination',shapes=rows,quadratic_extension_objection=groebner_objection(shapes['frame3']),karapetyan_even_identity=dict(n=4,a=1,coefficients=f,factor='2*(x^2-x+1)^2',verified=f==sq))
 assert rows['square']['rook_prefix']==[1,4,1,0,0]
 Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(dict(shapes=len(rows),all_prefixes_match=all(x['matches'] for x in rows.values()),quadratic_objection=out['quadratic_extension_objection'],identity_verified=True),indent=2))
