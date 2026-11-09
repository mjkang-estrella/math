import itertools,json
from pathlib import Path
D=Path(__file__).resolve().parents[1];out=[]
for q,N in [(2,100),(3,100)]:
 V=[(1,0)]+[(i,1) for i in range(q)];counts=[[0]*3 for n in range(N+1)];hist=[0]
 def rec(c,lo,total):
  if len(c)==q+1:
   if sum(t>0 for t in c)<2:return
   a=sum(t*x*x for t,(x,y) in zip(c,V))%q;b=sum(t*x*y for t,(x,y) in zip(c,V))%q;d=sum(t*y*y for t,(x,y) in zip(c,V))%q
   rank=2 if (a*d-b*b)%q else (1 if (a or b or d) else 0)
   counts[total][2-rank]+=1;hist[0]+=1;return
  for v in range(lo,(N-total)//(q+1-len(c))+1):rec(c+[v],v,total+v)
 rec([],0,0)
 for n in range(1,N+1):
  for h in range(3):counts[n][h]+=counts[n-1][h]
 rows=[dict(n=n,k=2,q=q,B=counts[n],holds=min(counts[n][:2])>counts[n][2]) for n in range(4,N+1)]
 print('q',q,'histograms',hist,'failures',[r for r in rows if not r['holds']],flush=True);out.append(dict(q=q,method='PGL(2,2)=S3 or PGL(2,3)=S4 on projective column types; sorted multiplicities; zero columns included',histograms=hist[0],rows=rows))
(D/'outputs/codes2.json').write_text(json.dumps(out,indent=2)+'\n')
