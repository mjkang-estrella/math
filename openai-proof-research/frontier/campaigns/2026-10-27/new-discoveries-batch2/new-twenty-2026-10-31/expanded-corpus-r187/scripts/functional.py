import pathlib,json,math
D=pathlib.Path(__file__).resolve().parents[1]
def prime(n):return n>1 and all(n%d for d in range(2,math.isqrt(n)+1))
def connected(p,a):
 parent=list(range(p));components=p
 def root(x):
  while parent[x]!=x:parent[x]=parent[parent[x]];x=parent[x]
  return x
 for x in range(p):
  u=root(x);v=root((x*x+a)%p)
  if u!=v:parent[u]=v;components-=1
 return components==1
rows=[]
for p in range(2,501):
 if prime(p):rows.append({'p':p,'I_p':sum(connected(p,a) for a in range(p))})
large=[]
for p in [100003,100019,100043]:
 assert prime(p)
 for a in range(2000):
  if connected(p,a):large.append({'p':p,'connected_parameter':a,'parameters_tested':a+1});break
 else:large.append({'p':p,'connected_parameter':None,'parameters_tested':2000})
 print(large[-1],flush=True)
(D/'outputs/functional.json').write_text(json.dumps({'full_counts':rows,'beyond_source':large},indent=2))
