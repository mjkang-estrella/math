import pathlib,json,itertools,time
L=pathlib.Path(__file__).parent
F=[(0,1),(0,5),(1,2),(1,6),(2,7),(3,5),(3,6),(4,6),(4,7),(5,7)]
FE=[0,2,3,4];C=[(0,1),(0,2),(0,3)];CE=[3,1,1,2,2,3]
PERMS=list(itertools.permutations(range(5)))
def transform(state,p):
 return tuple((p[c],sum(1<<p[i] for i in range(5) if m>>i&1)) for c,m in state)
def canonical(state):return min(transform(state,p) for p in PERMS)
def table(es,ps,n,name):
 # Colors assigned to internal edges first, then semiedges; exact S5 restricted-growth enumeration.
 items=es+[(v,-1) for v in ps]; masks=[0]*n;deg=[0]*n;cols=[-1]*len(items)
 raw={};nodes=leaves=0;start=time.monotonic()
 def dfs(i,k):
  nonlocal nodes,leaves
  nodes+=1
  if nodes%10000==0 and time.monotonic()-start>145:raise TimeoutError('145s enumeration ceiling')
  if i==len(items):
   leaves+=1;d=sum((masks[a]|masks[b]).bit_count()==4 for a,b in es)
   if d>2:return
   state=tuple((cols[len(es)+j],masks[v]) for j,v in enumerate(ps))
   if state not in raw or d<raw[state][0]:raw[state]=(d,cols[:])
   return
  a,b=items[i];forbidden=masks[a]|(masks[b] if b>=0 else 0)
  for c in range(min(k+1,5)):
   bit=1<<c
   if forbidden&bit:continue
   cols[i]=c;masks[a]|=bit;deg[a]+=1
   if b>=0:masks[b]|=bit;deg[b]+=1
   # Count only internal edges whose endpoint stars are complete.
   d=sum(deg[u]==deg[v]==3 and (masks[u]|masks[v]).bit_count()==4 for u,v in es)
   if d<=2:dfs(i+1,max(k,c+1))
   masks[a]^=bit;deg[a]-=1
   if b>=0:masks[b]^=bit;deg[b]-=1
 dfs(0,0)
 orbit={}
 for state,(d,cs) in raw.items():
  key=canonical(state)
  if key not in orbit or d<orbit[key]['cost']:
   p=next(p for p in PERMS if transform(state,p)==key)
   orbit[key]={'state':key,'cost':d,'colors':[p[c] for c in cs]}
 rows=list(orbit.values());out={'name':name,'edges':es,'ports':ps,'vertices':n,'cap':2,'complete':True,'nodes':nodes,'leaves':leaves,'raw_states':len(raw),'orbit_states':len(rows),'rows':rows,'seconds':time.monotonic()-start}
 (L/(name+'-table.json')).write_text(json.dumps(out,separators=(',',':')))
 print({k:v for k,v in out.items() if k not in ['rows','edges','ports']},flush=True)
 return out
if __name__=='__main__':
 for args in [(F,FE,8,'F'),(C,CE,4,'C')]:table(*args)
