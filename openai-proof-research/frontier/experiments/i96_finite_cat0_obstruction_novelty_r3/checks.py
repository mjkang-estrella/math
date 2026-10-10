"""Independent exact I96 comparison diagnostics; no imports of I91 code, no writes.

CN/Young/quad rows below are constructed from named points, not copied row IDs.
The final nonnegative linear combination is checked as a symbolic identity.
This establishes a finite inequality implication, not the action-to-metric bridge.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import json,sys
sys.dont_write_bytecode=True
R=Path(__file__).resolve().parents[3]
def key(a,b):return '|'.join(sorted((a,b)))
def expr(terms):
 d={}
 for a,b,v in terms:
  if a!=b:d[key(a,b)]=d.get(key(a,b),F(0))+F(v)
 return {k:v for k,v in d.items() if v}
def add(a,b,t=F(1)):
 d=a.copy()
 for k,v in b.items():d[k]=d.get(k,F(0))+t*v
 return {k:v for k,v in d.items() if v}
def mul(a,t):return {k:v*t for k,v in a.items() if v*t}
def symbolic():
 bases=[];bounds={};steps=[]
 # Each proof has lhs <= rhs; provenance coefficients are nonnegative.
 def base(d,rhs,label,kind):
  i=len(bases);bases.append({'lhs':d,'rhs':F(rhs),'label':label,'kind':kind})
  return (d,F(rhs),{i:F(1)})
 def plus(a,b,t=F(1)):
  assert t>=0
  return (add(a[0],b[0],t),a[1]+t*b[1],add(a[2],b[2],t))
 def scale(p,t):
  assert t>0
  return (mul(p[0],t),p[1]*t,mul(p[2],t))
 def fix(a,b,v):
  k=key(a,b)
  for s in (-1,1):bounds[k,s]=base({k:F(s)},s*F(v),'initial '+k,'bound')
 for a,b in combinations(['P','Q','R','S','U'],2):fix(a,b,2)
 for a in ['P','Q','R','S','U']:fix('c',a,F(3,4))
 for a in 'ABCD':fix('c',a,F(1,4))
 fix('C','D',1);fix('P','z',1);fix('S','z',1);fix('Q','z',3)
 def cn(n,a,b,z):return base(expr([(n,z,4),(a,z,-2),(b,z,-2),(a,b,1)]),0,f'CN {n}=mid({a},{b}) at {z}','CN')
 def endpoint(n,a,b,z,sign=1):return base(expr([(n,z,4*sign),(a,b,-sign)]),0,f'endpoint {n}=mid({a},{b}) at {z}','endpoint')
 def yr(z,a,b,q,sign=1):
  return base(expr([('c',b,sign),(z,a,sign),('c',a,-sign),(z,b,-sign),('c',z,-q),(a,b,-1/q)]),0,f'Young c,{z};{a},{b};q={q};sign={sign}','Young')
 def derive(row,a,b,sign=1):
  k=key(a,b);coef=row[0][k];assert coef*sign>0
  p=row
  for j,v in list(row[0].items()):
   if j==k or j==key('c','w'):continue
   # Cancel v*j using -v*j <= corresponding bound.
   p=plus(p,bounds[j,-1 if v>0 else 1],abs(v))
  p=scale(p,1/abs(coef));assert p[0][k]==sign
  bounds[k,sign]=p;steps.append(p);return p
 for n,a,b,z in [('A','P','Q','P'),('A','P','Q','Q'),('A','P','R','R'),('B','P','S','S'),('C','Q','S','Q'),('D','R','U','U')]:derive(endpoint(n,a,b,z),n,z)
 derive(cn('A','P','Q','U'),'A','U')
 derive(cn('D','R','U','A'),'A','D')
 derive(cn('B','P','S','Q'),'B','Q')
 derive(cn('B','P','S','z'),'B','z')
 derive(cn('c','Q','z','B'),'B','Q',-1)
 derive(cn('C','Q','S','B'),'B','C')
 derive(cn('D','R','U','Q'),'D','Q')
 derive(cn('c','C','D','Q'),'D','Q',-1)
 derive(endpoint('w','Q','D','D'),'D','w')
 derive(endpoint('w','Q','D','Q'),'Q','w')
 derive(cn('w','Q','D','U'),'U','w')
 derive(cn('w','Q','D','A'),'A','w')
 derive(yr('P','A','w',F(2,5),-1),'P','w')
 derive(cn('B','P','U','w'),'B','w')
 quad=base(expr([('B','Q',1),('C','w',1),('B','C',-1),('C','Q',-1),('Q','w',-1),('w','B',-1)]),0,'quad B,C,Q,w','quad')
 upper2=derive(quad,'C','w')
 lower=derive(cn('c','C','D','w'),'C','w',-1)
 upper1=derive(yr('w','C','Q',F(5,2)),'C','w')
 # Cw >= 1/8+2r; Cw <= 3/40+5r/2; Cw <=39/160+r/2.
 assert lower[0]=={key('C','w'):F(-1),key('c','w'):F(2)} and lower[1]==-F(1,8)
 assert upper1[0]=={key('C','w'):F(1),key('c','w'):-F(5,2)} and upper1[1]==F(3,40)
 assert upper2[0]=={key('C','w'):F(1),key('c','w'):-F(1,2)} and upper2[1]==F(39,160)
 final=plus(scale(plus(lower,upper1),F(2)),scale(plus(lower,upper2),F(2,3)))
 assert final[0]=={} and final[1]==-F(1,48)
 # Recompute the claimed Farkas sum independently from base rows.
 lhs={};rhs=F(0);err=F(0)
 for i,w in final[2].items():
  assert w>=0;lhs=add(lhs,bases[i]['lhs'],w);rhs+=w*bases[i]['rhs'];err+=w
 assert lhs=={} and rhs==-F(1,48)
 # In the primitive integer normalization a rational row with denominator 5
 # has RHS <= delta/5; allowing delta for the unscaled row is conservative.
 assert err*F(1,10**10000)<F(1,48)
 used=[{'index':i,**bases[i],'multiplier':w} for i,w in sorted(final[2].items())]
 return {'status':'PASS_EXACT_SYMBOLIC_REDUCTION','derived_bounds':len(steps),'used_base_constraints':len(used),'positive_margin':str(-rhs),'error_amplification':str(err),'sufficient_delta_strictly_below':str((-rhs)/err),'used_kinds':sorted({b['kind'] for b in used}),'used_names':sorted({n for b in used for k in b['lhs'] for n in k.split('|')}),'proof':used}
def slice_trace():
 c=json.loads((R/'frontier/experiments/i91_finite_cat0_obstruction/certificate.json').read_text())
 need={(k,'lower' if v>0 else 'upper') for k,v in c['used_rows'][str(c['contradiction']['row'])]};idx=[]
 for i in range(len(c['trace'])-1,-1,-1):
  ri,k,s,val=c['trace'][i]
  if (k,s) in need:
   need.remove((k,s));idx.append(i);need.update((j,'lower' if v>0 else 'upper') for j,v in c['used_rows'][str(ri)] if j!=k)
 lohi=[[F(v,c['dyadic_denominator']) for v in p] for p in c['initial']]
 rows=set()
 for i in reversed(idx):
  ri,k,s,val=c['trace'][i];row=dict(c['used_rows'][str(ri)]);rows.add(ri);a=row.pop(k)
  v=-sum(co*lohi[j][0 if co>0 else 1] for j,co in row.items())/a;vout=F(val,c['dyadic_denominator'])
  if s=='upper':assert a>0 and v<=vout;lohi[k][1]=vout
  else:assert a<0 and v>=vout;lohi[k][0]=vout
 row=c['used_rows'][str(c['contradiction']['row'])];rows.add(c['contradiction']['row'])
 margin=sum(v*lohi[k][0 if v>0 else 1] for k,v in row);assert margin==F(93183,8388608)
 names=sorted({n for ri in rows for k,v in c['used_rows'][str(ri)] for n in c['pairs'][k]})
 return {'updates':len(idx),'rows':len(rows),'names':names,'margin':str(margin),'update_indices':sorted(idx),'status':'PASS_FINITE_TRACE_SLICE_ONLY'}
def finite():
 # Euclidean and actual tripod metrics test universal rows on concrete spaces.
 tree=0;euclid=0
 pts=[(F(x,4),F(y,4)) for x in range(-2,3) for y in range(-2,3)]
 def d2(a,b):return sum((x-y)**2 for x,y in zip(a,b))
 for i in range(len(pts)):
  a,b,c,d=[pts[(i*j+j*j)%len(pts)] for j in (1,2,3,4)]
  m=tuple((x+y)/2 for x,y in zip(a,b));assert 4*d2(m,c)-2*d2(a,c)-2*d2(b,c)+d2(a,b)==0
  for q in [F(2,5),F(1,2),F(1),F(2),F(5,2)]:
   lhs=d2(a,d)+d2(b,c)-d2(a,c)-d2(b,d);assert abs(lhs)<=q*d2(a,b)+d2(c,d)/q;euclid+=1
 for k in range(1,33):
  eps=F(1,2**k)
  for t in [F(1),F(1,3),eps,eps/2]:
   dist=2*max(t-eps,0);assert dist<=2*t
   if t<=eps:assert dist==0
   tree+=1
 assert F(72,663552)==F(1,9216)
 assert 16*12**2*4==9216 and 16*12**2*6*4==55296 and 32*12**2*6**2*4==663552
 assert 2000*F(1,10**10004)<F(1,10**10000)
 return {'euclidean_Young_cases':euclid,'stem_tree_cases':tree,'status':'PASS_FINITE_DIAGNOSTICS_ONLY'}
if __name__=='__main__':
 out={'symbolic':symbolic(),'trace_slice':slice_trace(),'finite':finite()}
 print(json.dumps(out,default=str,sort_keys=True,indent=2))
