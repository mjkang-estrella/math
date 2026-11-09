from pathlib import Path
import itertools,json
w=Path(__file__).resolve().parent
records=[]
for p in range(13,502,4):
 h=(p+3)//2;D=set(range((p-1)//2+1))|{h};E=lambda t:4*t*t-(3*p-5)*(-1)**t
 exceptional=set();mn=None;count=0
 for a in D:
  for r in range(p):
   q=tuple((a+j*r)%p for j in range(4))
   if not all(t in D for t in q):continue
   a,b,c,d=q;g=E(a)+E(d)-E(b)-E(c)
   assert g>=0 and ((g==0)==(r==0))
   if r:mn=g if mn is None else min(mn,g);count+=1
   if a-2*b+c or b-2*c+d:exceptional.add(q);assert g==16
   else:assert g==16*(b-a)**2
 assert exceptional=={(h-3,0,h,3),(3,h,0,h-3)}
 records.append(dict(p=p,nonconstant=count,minimum=mn))
def brute(D,p):
 a=tuple(D);target=sorted(a);tested=0
 for b in itertools.permutations(a):
  if b==a:continue
  tested+=1;c=tuple((2*y-x)%p for x,y in zip(a,b))
  if sorted(c)!=target:continue
  d=tuple((3*y-2*x)%p for x,y in zip(a,b))
  if sorted(d)==target:return dict(tested=tested,witness=[a,b,c,d])
 return dict(tested=tested,witness=None)
out=dict(coordinate_sweep=records,p13_n8=brute([0,1,2,3,4,5,6,8],13),negative_added_digit=brute(list(range(9)),13),negative_no_frequencies=[[0],[1],[2],[3]],negative_no_parity=dict(p=13,coordinate=[5,0,8,3],gap=4*(25+9-0-64)))
assert out['p13_n8']['witness'] is None
assert out['negative_added_digit']['witness'] is not None
(w/'computations.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k!='coordinate_sweep'},indent=2));print('sweep',len(records))
