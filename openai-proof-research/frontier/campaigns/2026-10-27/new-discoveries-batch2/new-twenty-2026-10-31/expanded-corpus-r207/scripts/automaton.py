from pathlib import Path
import collections,json,time
L=Path(__file__).resolve().parents[1];D=json.loads((L/'outputs/adjacency.json').read_text());out={};start=time.monotonic()
def transitions(s,m):
 n,pre,last=s
 if n==0:return [(1,(0,),0)]
 inc=lambda d:min(m,d+1)
 old=tuple(map(inc,pre));newn=min(n+1,m+1);res=[]
 if pre[0]<m:res.append((newn,(0,)+old[:m-1],inc(last)))
 if last<m:res.append((newn,old+(0,) if n<m else old,0))
 for a in range(1,min(m,n)):
  if sorted(pre[:a])==list(range(a)) and pre[a-1]<m and pre[a]<m:res.append((newn,(old[:a]+(0,)+old[a:])[:m],inc(last)))
 return res
for m in range(1,7):
 states=[(0,(),0)];seen={states[0]:0};edges=[]
 for s in states:
  row=collections.Counter()
  for t in transitions(s,m):
   if t not in seen:seen[t]=len(states);states.append(t)
   row[seen[t]]+=1
  edges.append(dict(row))
  if len(states)>200000 or time.monotonic()-start>100:raise RuntimeError('state cap')
 vec={0:1};seq=[1]
 for n in range(1,61):
  new=collections.Counter()
  for i,v in vec.items():
   for j,w in edges[i].items():new[j]+=v*w
  vec=dict(new);seq.append(sum(vec.values()))
 assert seq==D[str(m)]['counts_n0_to60'],m
 out[str(m)]={'reachable_states':len(states),'edges_with_multiplicity':sum(sum(e.values()) for e in edges),'counts_n0_to60':seq,'crosscheck':'agrees with endpoint DP for every n <= 60'};print(m,out[str(m)]['reachable_states'],flush=True)
 (L/f'outputs/automaton-m{m}.json').write_text(json.dumps({'states':states,'transitions':edges},indent=2))
(L/'outputs/automaton.json').write_text(json.dumps(out,indent=2))
