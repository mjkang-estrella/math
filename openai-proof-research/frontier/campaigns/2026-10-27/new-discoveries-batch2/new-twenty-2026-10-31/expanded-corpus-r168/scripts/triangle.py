from fractions import Fraction as F
import pathlib,json,sys
D=pathlib.Path(__file__).resolve().parents[1];out=[]
def red(a,n):
 legs={}
 for (r,d),(l,h,b) in a.items():
  t=l+h+b;legs[r,d]=(l*h/t,l*b/t,h*b/t)
 def edge(x,y,z):return x+y+(x*y/z if z else 0)
 return {(r,d):(edge(legs[r,d][1],legs[r+1,d][0],legs[r,d-1][2] if d>1 else 0),edge(legs[r,d][2],legs[r+1,d+1][0],legs[r,d+1][1] if d<r else 0),edge(legs[r+1,d][2],legs[r+1,d+1][1],legs[r+2,d+1][0] if r<n-1 else 0)) for r in range(1,n) for d in range(1,r+1)}
for n in range(2,19):
 a={(r,d):(F(1),)*3 for r in range(1,n+1) for d in range(1,r+1)};data=[]
 for s in range(1,n):
  a=red(a,n-s+1);m=n-s;ones=sum(x==1 for tr in a.values() for x in tr)
  data.append({'reductions':s,'remaining_order':m,'ones':ones,'max_numerator_bits':max(x.numerator.bit_length() for tr in a.values() for x in tr)})
  if s>(n+1)//4:assert ones==0,(n,s,ones)
 out.append({'n':n,'steps':data,'part_d_exact_pass':True});(D/'outputs/triangle.json').write_text(json.dumps(out,indent=2));print(n,'pass',flush=True)
