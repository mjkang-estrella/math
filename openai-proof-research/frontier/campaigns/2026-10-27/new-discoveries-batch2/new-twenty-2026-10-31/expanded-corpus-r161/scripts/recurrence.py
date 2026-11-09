import json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for c in range(4,31):
 G=[0,1,2,3,4]
 for j in range(5,51):G.append(G[j-3]+c*G[j-4])
 # Canonical sparse coefficient vectors, implementing Definition 1.5 with its intended t-indexed suffix.
 dp=[{0:()}];collision=None;count=0
 for j in range(1,51):
  cur=dict(dp[-1]);new=[(G[j],((j,1),))]
  if j>=2:
   for a in range(c):
    for v,w in dp[max(0,j-4)].items():
     z=G[j]+a*G[j-1]+v
     if z<=100000:new.append((z,((j,1),)+(((j-1,a),) if a else ())+w))
  for v,w in new:
   if v>100000:continue
   count+=1
   if v in cur and cur[v]!=w:collision={'N':v,'a':cur[v],'b':w,'max_index':j};break
   cur[v]=w
  dp.append(cur)
  if collision:break
 r={'c':c,'max_index':j,'value_cap':100000,'distinct_values':len(cur),'generated':count,'collision':collision,'missing_below_1000':[v for v in range(1,1001) if v not in cur]};out.append(r);print(r,flush=True)
(D/'outputs/recurrence.json').write_text(json.dumps(out,indent=2)+'\n')
