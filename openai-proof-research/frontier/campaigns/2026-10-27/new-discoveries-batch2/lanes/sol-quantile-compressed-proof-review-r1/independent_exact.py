from fractions import Fraction as F
from pathlib import Path
import json,hashlib,subprocess
L=Path(__file__).resolve().parent
def dump(n,x): (L/n).write_text(json.dumps(x,indent=2,default=str)+'\n')
S=[[F(x) for x in ['1','13/10','11/5','14/5','29/10']], [F(x) for x in ['1/2','9/10','9/10','8/5','9/5']]]
def q(k,u):return sum(s*max(F(0),min(F(1,5),u-F(j,5))) for j,s in enumerate(S[k]))
def r(u):return (q(0,u)+q(1,u))/2
a=F(159,2000)
K=list(map(F,[0,4,10,20,24,38,40]));Y=list(map(F,[0,-4,2,-8,-4,-18,-16]))
def H(x):
 if x<=0:return Y[0]
 if x>=40:return Y[-1]
 j=next(j for j in range(6) if K[j]<=x<=K[j+1])
 return Y[j]+(x-K[j])*(Y[j+1]-Y[j])/(K[j+1]-K[j])
def h(x):return a*H(x/a)
def D(t):return 2-t+2*max(F(0),t-3)-2*max(F(0),t-7)+2*max(F(0),t-17)
def d(x):return a*D(x/a)
# Independent polygon clipping, retaining exact boundary coincidences, not just a grid.
def clip(poly,k,side):
 out=[]
 for P,Q in zip(poly,poly[1:]+poly[:1]):
  vP=side*(sum(P)-k);vQ=side*(sum(Q)-k)
  if vP<=0:out.append(P)
  if (vP<0<vQ) or (vQ<0<vP):
   z=vP/(vP-vQ);out.append(tuple(P[n]+z*(Q[n]-P[n]) for n in [0,1]))
 # Remove all duplicates; retain cyclic order. Degenerate point/edge pieces harmless.
 return list(dict.fromkeys(out))
ends=list(map(F,[0,3,7,17,20]));rects=[];sym=0
for i in range(4):
 for j in range(4):
  x,X=ends[i:i+2];y,Z=ends[j:j+2]
  base=[(x,y),(X,y),(X,Z),(x,Z)];polys=[]
  for lo,hi in zip(K,K[1:]):
   p=clip(clip(base,lo,-1),hi,1)
   if p:polys.append(dict(sum_interval=[lo,hi],vertices=p))
  vertices=sorted(set(v for p in polys for v in p['vertices']))
  # Separate line-edge intersection characterization, including coincident endpoints.
  expected=set(base)
  for k in K[1:-1]:
   for xx in [x,X]:
    if y<=k-xx<=Z:expected.add((xx,k-xx))
   for yy in [y,Z]:
    if x<=k-yy<=X:expected.add((k-yy,yy))
  assert set(vertices)==expected
  slacks=[dict(s=v[0],t=v[1],slack=D(v[0])+D(v[1])-H(sum(v))) for v in vertices]
  assert min(v['slack'] for v in slacks)==0
  for p in polys:
   # H and both D terms are affine on the specified entire closed polygon.
   assert all(p['sum_interval'][0]<=sum(v)<=p['sum_interval'][1] for v in p['vertices'])
  rects.append(dict(i=i+1,j=j+1,polygons=polys,vertex_slacks=slacks))
  if i<=j:sym+=len(vertices)
assert sym==51
assert [len(z['vertex_slacks']) for z in rects if z['i']<=z['j']]==[6,6,5,4,4,5,5,6,4,6]
# Quantile densities: exact endpoints and reciprocal slopes, unit total mass.
ep=[[q(k,F(j,5)) for j in range(6)] for k in [0,1]]
assert ep==[[F(x) for x in ['0','1/5','23/50','9/10','73/50','51/25']], [F(x) for x in ['0','1/10','7/25','23/50','39/50','57/50']]]
for k in [0,1]:
 assert S[k]==sorted(S[k]) and min(S[k])>0
 assert sum((ep[k][j+1]-ep[k][j])/S[k][j] for j in range(5))==1
assert r(F(1))==20*a and sum(z[-1] for z in ep)==40*a
split={F(j,5) for j in range(6)};pre=[]
for t in [3,7,17]:
 roots=[]
 for j in range(5):
  lo,hi=F(j,5),F(j+1,5);slope=(r(hi)-r(lo))/(hi-lo)
  u=lo+(a*t-r(lo))/slope
  if lo<=u<=hi:roots.append(u)
 assert len(set(roots))==1
 pre.append(roots[0]);split.add(roots[0])
assert pre==[F(617,2200),F(1613,3100),F(4223,4700)]
split=sorted(split);target=[]
for lo,hi in zip(split,split[1:]):target.append(dict(lo=lo,hi=hi,integral=(hi-lo)*(d(r(lo))+d(r(hi)))/2))
B=2*sum(z['integral'] for z in target)
assert B==F(-83231059,641080000)
p=[17,16,15,14,13,11,10,9,7,5,3,1,0,18,19,12,8,6,4,2]
assert sorted(p)==list(range(20))
bins=[];n=0
printed=['7/10000','27/10000','89/20000','2969/520000','6997/1160000','99/20000','2573/440000','2813/440000','7253/1240000','7453/1240000','6461/1080000','143/40000','-57/40000','-21/800','-151/4000','-5149/275000','-37387/1900000','-69769/3800000','-35407/1900000','-11/500']
for i,pi in enumerate(p):
 lo,hi=F(i,20),F(i+1,20);shift=F(pi-i,20)
 assert lo+shift==F(pi,20) and hi+shift==F(pi+1,20)
 def f(u):return q(0,u)+q(1,u+shift)
 knots={lo,hi}
 for j in range(6):
  for u in [F(j,5),F(j,5)-shift]:
   if lo<u<hi:knots.add(u)
 base=sorted(knots)
 for l,b in zip(base,base[1:]):
  slope=(f(b)-f(l))/(b-l);assert slope>0
  for k in K[1:-1]:
   u=l+(a*k-f(l))/slope
   if l<u<b:knots.add(u)
 pieces=[];knots=sorted(knots)
 for l,b in zip(knots,knots[1:]):
  val=(b-l)*(h(f(l))+h(f(b)))/2
  pieces.append(dict(lo=l,hi=b,sum_lo=f(l),sum_hi=f(b),h_lo=h(f(l)),h_hi=h(f(b)),integral=val))
 v=sum(z['integral'] for z in pieces);assert v==F(printed[i]);n+=len(pieces)
 bins.append(dict(i=i,target_bin=pi,shift=shift,pieces=pieces,integral=v))
A=sum(z['integral'] for z in bins);gap=A-B
assert n==31 and A==F(-68997954679,659497410000) and gap==F(100817889097,3999532680000) and gap>0
dump('exact-evidence.json',dict(status='PASS',arithmetic='independent Fraction reconstruction; no candidate checker read/import/run',scale=a,endpoints=ep,density_rows=[[1/s for s in row] for row in S],r_slopes=[(S[0][j]+S[1][j])/2 for j in range(5)],rectangles=rects,symmetric_vertex_substitutions=sym,target_preimages=pre,target_pieces=target,B=B,permutation=p,source_bins=bins,source_piece_count=n,A=A,gap=gap))
# Regenerate accepted-body text under the guard, then bind both bytes and text.
body=L/'frozen/sol-quantile-aggregation-source-prior-r2/accepted.body';text=L/'accepted-derived.txt'
subprocess.run(['pdftotext','-layout',str(body),str(text)],check=True)
dump('accepted-derivation.json',dict(body_sha256=hashlib.sha256(body.read_bytes()).hexdigest(),derived_sha256=hashlib.sha256(text.read_bytes()).hexdigest(),matches_frozen_text=text.read_bytes()==(body.with_name('accepted.txt')).read_bytes()))
# Parse full administrative snapshots (not immutable live dependencies).
for name in ['ledger.json','prior-campaign-context.json']:
 obj=json.loads((L/'administrative'/name).read_text())
 if name=='ledger.json':assert (obj['accepted_count'],obj['total_accepted_count'],obj['next_global_outcome_number'])==(9,39,40)
print('PASS: all 16 rectangles, 51 symmetry-reduced vertices, all 31 source pieces, 20 bin integrals, exact A/B/gap')
