import json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for c in range(4,17):
 G=[0,1,2,3,4]
 for j in range(5,84):G.append(G[j-3]+c*G[j-4])
 dp=[{0:()}];collisions=[]
 for j in range(1,81):
  cur=dict(dp[-1])
  if G[j]<=100000:cur[G[j]]=((j,1),)
  if j>=2:
   for a in range(c):
    base=G[j]+a*G[j-1]
    for v,w in dp[max(0,j-4)].items():
     z=base+v
     if z>100000 or not G[j+2]<=z<G[j+3] or z in G:continue
     word=((j,1),)+(((j-1,a),) if a else ())+w
     if z in cur and cur[z]!=word:collisions.append({'N':z,'a':cur[z],'b':word})
     cur[z]=word
  dp.append(cur)
 r={'c':c,'max_index':80,'cap':100000,'positive_values_covered':len(cur)-1,'collisions':collisions[:3],'missing_count':sum(v not in cur for v in range(1,100001)),'semantics':'additional interval restriction inferred from prose, not stated in formal legality definition; diagnostic only'};out.append(r);print(r,flush=True)
(D/'outputs/recurrence-intended.json').write_text(json.dumps(out,indent=2)+'\n')
