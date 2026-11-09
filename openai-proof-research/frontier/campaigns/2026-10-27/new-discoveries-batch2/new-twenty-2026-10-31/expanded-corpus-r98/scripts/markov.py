import json
from pathlib import Path
D=Path(__file__).resolve().parents[1];out=[]
# Coprime interior Farey labels only; full non-coprime fence labels NOT tested.
for k in range(21):
 seen={};coll=[];count=0
 def walk(a,b,x,y,z,depth):
  global count
  p,q=a[0]+b[0],a[1]+b[1];v=((3+3*k)*x*z-k*(x+z))-y
  assert v>0
  if (p,q)!=(1,1):
   if v in seen and seen[v]!=(p,q):coll.append([seen[v],(p,q),v])
   seen[v]=(p,q);count+=1
  if depth:walk(a,(p,q),x,z,v,depth-1);walk((p,q),b,v,x,z,depth-1)
 # First interior interval endpoints 0/1 and 1/1 have values 1,k+2; opposite at 1/0 has value1.
 walk((1,0),(1,1),1,1,k+2,9)
 o=dict(k=k,labels=count,collisions=coll);out.append(o);print(json.dumps(o),flush=True)
(D/'outputs/markov.json').write_text(json.dumps(out,indent=2)+'\n')
