from pathlib import Path
import collections,json
L=Path(__file__).resolve().parents[1];out=[]
for m in range(5,16,2):
 q=1<<m
 for p in range(q+1,2*q,2):
  a=1;ex=[]
  for _ in range(q-1):
   ex.append(a);a<<=1
   if a&q:a^=p
   if a==1:break
  if len(ex)==q-1 and len(set(ex))==q-1:break
 log={a:i for i,a in enumerate(ex)}
 es=[(q-17,(q+19)//3),(q-(1<<(m-4))-1,q-((1<<(m-2))+4)//3),(q-3,(1<<((m+3)//2))+(1<<((m+1)//2))+4),(q-(1<<((m-1)//2))-1,(1<<(m-1))-(1<<((m-1)//2))),(q-2-((1<<(m-1))-4)//3,q-4-(q-8)//3),(q-(1<<((m+1)//2))+(1<<((m-1)//2)),q-(1<<((m+1)//2))-1),(q-3*((1<<((m+1)//2))-1),(1<<((m+1)//2))+(1<<((m-1)//2))-2),(q-(1<<(m-2))-1,(1<<(m-1))-2),(q-(1<<((m+3)//2))-3,(1<<((m+1)//2))+2),(q-3*((1<<((m-1)//2))+1),(1<<(m-1))-1),(q-5,6)]
 for j,(a,b) in enumerate(es,1):
  D={ex[(a*i)%(q-1)]^ex[(b*i)%(q-1)]^x for x,i in log.items()};D.discard(0);W=[int(x in D) for x in range(q)];step=1
  while step<q:
   for i in range(0,q,2*step):
    for k in range(i,i+step):u,v=W[k],W[k+step];W[k]=u+v;W[k+step]=u-v
   step*=2
  weights=collections.Counter((len(D)-v)//2 for v in W)
  lo=(q//4)-(1<<((m-3)//2));hi=q//4+(1<<((m-3)//2));expected={0:1,lo:lo,q//4:q//2-1,hi:hi}
  r={'m':m,'f':j,'modulus':p,'exponents':[a,b,1],'length':len(D),'weights':dict(weights),'matches':weights==expected};out.append(r)
  if not r['matches']:print('FAIL',r,flush=True)
 print('completed',m,'matches',sum(r['matches'] for r in out if r['m']==m),flush=True)
 (L/'outputs/codes.json').write_text(json.dumps(out,indent=2))
