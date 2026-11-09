from pathlib import Path
import json
N=150;rows=[]
for m in range(3,13):
 for a in range(1,m//2+1):
  b=m-a
  if a>=b:continue
  dp=[{} for _ in range(N+1)];dp[0][0]=1
  for p in range(1,N+1):
   inc=int(p%m==a%m)-int(p%m==b%m)
   for n in range(N,p-1,-1):
    for d,c in list(dp[n-p].items()):dp[n][d+inc]=dp[n].get(d+inc,0)+c
  dif=[sum(c*(1 if d>0 else -1 if d<0 else 0) for d,c in q.items()) for q in dp]
  exception={(2,3,5):45,(2,4,6):5,(3,4,7):8,(4,5,9):9}.get((a,b,m),0)
  rec={'a':a,'b':b,'m':m,'n_max':N,'negative_n':[i for i,d in enumerate(dif) if d<0],'predicted_threshold':exception,'violations_at_or_after_threshold':[i for i,d in enumerate(dif) if i>=exception and d<0],'differences':dif};rows.append(rec);print({k:v for k,v in rec.items() if k!='differences'},flush=True)
Path('outputs/residue.json').write_text(json.dumps(rows,indent=2)+'\n')
