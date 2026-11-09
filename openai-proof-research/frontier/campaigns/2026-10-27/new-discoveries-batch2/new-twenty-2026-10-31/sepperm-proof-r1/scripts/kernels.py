# OBSOLETE EXPLORATORY MODEL: incorrect actual-record normalization; see ATTEMPTS.md.
import json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
def add(*ps):
 c=[0]*max(map(len,ps))
 for p in ps:
  for i,x in enumerate(p):c[i]+=x
 return c
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
h=[[1]]
for r in range(1,41):
 c=mul([1,1],h[-1])
 for i in range(r-1):c=add(c,mul([0,1,1],mul(h[i],h[r-2-i])))
 h.append(c)
for r in range(1,40):
 H=add(mul([1,1],h[r]),mul([0,-1,1],h[r+1]));s=0; pref=[]
 for v in H[1:]:s+=v;pref.append(s)
 print(json.dumps({'r':r,'H':H if r<=8 else None,'minimum_prefix':min(pref),'first_negative':next((i+1 for i,x in enumerate(pref) if x<0),None)}),flush=True)
