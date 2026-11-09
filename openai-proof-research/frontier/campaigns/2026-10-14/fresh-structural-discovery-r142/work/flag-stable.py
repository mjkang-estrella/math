from pathlib import Path
import runpy,json,time
R=Path(__file__).resolve().parents[1];g=runpy.run_path(str(R/'work/flag-box.py'),run_name='flaglib');beta=g['beta'];lex=g['lex'];product=g['product']
def stable_ideals(box):
 n=len(box);E=sorted(product(*(range(a) for a in box)),key=lambda a:(sum(a),a));out=[]
 pred={}
 for u in E:
  V={tuple(u[j]-(j==k) for j in range(n)) for k in range(n) if u[k]}
  for h in range(n):
   for l in range(h+1,n):
    if u[h] and u[l]+1<box[l]:V.add(tuple(u[j]-(j==h)+(j==l) for j in range(n)))
  pred[u]=V
 def walk(i,A):
  if i==len(E):out.append(frozenset(A));return
  u=E[i];walk(i+1,A)
  if pred[u]<=A:A.add(u);walk(i+1,A);A.remove(u)
 walk(0,set());return E,out
if __name__=='__main__':
 start=time.monotonic()
 for box in [(3,3,3),(2,2,2,3),(2,2,2,2,2),(2,2,2,2,2,2)]:
  E,sets=stable_ideals(box);print('box',box,'stable sets',len(sets),flush=True);cache={};found=None;checked=0;limit=False
  for A in sets:
   for B in sets:
    if not B<=A:continue
    D=A-B;L=lex(A,E)-lex(B,E)
    for W in (D,L):
     if W not in cache:cache[W]=beta(W,box)
    a,b=cache[D],cache[L];checked+=1
    if any(v>b.get(k,0) for k,v in a.items()):
     found=dict(A=sorted(A),B=sorted(B),D=sorted(D),L=sorted(L),beta={str(k):v for k,v in a.items()},lex_beta={str(k):v for k,v in b.items()});break
    if time.monotonic()-start>45:limit=True;break
   if found or limit:break
  out=dict(box=box,sets=len(sets),checked=checked,field=1000003,found=found,time_limit=limit)
  print(json.dumps(out),flush=True);(R/('packet/private/flag-stable-'+''.join(map(str,box))+'.json')).write_text(json.dumps(out,indent=2))
  if found or limit:break
