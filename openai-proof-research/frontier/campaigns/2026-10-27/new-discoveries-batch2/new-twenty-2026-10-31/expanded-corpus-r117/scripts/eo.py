import itertools,collections,json,time,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
def count(n,E):
 deg=[sum(v in e for e in E) for v in range(n)];target=[x//2 for x in deg];last={v:max((i for i,e in enumerate(E) if v in e),default=-1) for v in range(n)};active=[];dp={():1}
 for k,(a,b) in enumerate(E):
  newactive=sorted(set(active+[a,b]));pos={v:i for i,v in enumerate(newactive)};keep=[v for v in newactive if last[v]>k];nxt=collections.defaultdict(int)
  for state,c in dp.items():
   s=[0]*len(newactive)
   for v,x in zip(active,state):s[pos[v]]=x
   for v in (a,b):
    z=s.copy();z[pos[v]]+=1
    if any(z[pos[u]]>target[u] or (last[u]==k and z[pos[u]]!=target[u]) for u in (a,b)):continue
    nxt[tuple(z[pos[u]] for u in keep)]+=c
  active=keep;dp=nxt
 return dp.get((),0)
out=[]
for n in range(1,7):
 P=list(itertools.combinations(range(n),2));tested=0;bad=[]
 for mask in range(1<<len(P)):
  E=[p for i,p in enumerate(P) if mask>>i&1];deg=[sum(v in e for e in E) for v in range(n)]
  if any(x%2 for x in deg):continue
  v=count(n,E);rhs=1
  for d in deg:rhs*=({0:1,2:2,4:24}[d])**(15//(d+1))
  if v**15>rhs:bad.append(mask)
  tested+=1
 row={'n':n,'labeled_even_graphs':tested,'violations':bad};print(row,flush=True);out.append(row)
for radius,ns,rt in [(2,range(13,61),24),(3,range(13,27),2640)]:
 for n in ns:
  E=sorted({tuple(sorted((v,(v+j)%n))) for v in range(n) for j in range(1,radius+1)});v=count(n,E);row={'circulant_n':n,'jumps':list(range(1,radius+1)),'EO':v,'inequality':v**(2*radius+1)<=rt**n};out.append(row);print(row,flush=True)
(D/'outputs/eo.json').write_text(json.dumps(out,indent=2))
