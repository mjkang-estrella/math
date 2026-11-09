import runpy,sys,pathlib
L=pathlib.Path(__file__).resolve().parents[1];sys.argv=['young.py','2','3'];f=runpy.run_path(str(L/'scripts/young.py'))['graph']
def brute(g,k):
 start=(-1,-1);q=[start];adj={}
 for v in q:
  r,s=(0,0) if v==start else v;out=[]
  for a in range(g):
   for b in range(g):
    if v==start and not a*b:continue
    u,rem=divmod(k*b+s-a,g);t=b+r*g-k*a
    if rem==0 and 0<=u<k and 0<=t<k:
     w=(t,u);out.append(w)
     if w not in q:q.append(w)
  adj[v]=out
 keep={v for v in q if v!=start and (v[0]==v[1] or v[::-1] in adj[v])}
 while True:
  new=keep|{v for v in q if set(adj[v])&keep}
  if new==keep:break
  keep=new
 return {v:set(w for w in adj[v] if w in keep) for v in keep}
c=0
for g in range(3,21):
 for k in range(2,g):
  assert {v:set(e) for v,e in f(g,k).items()}==brute(g,k),(g,k)
  c+=1
print('PASS independent two-digit equation enumeration versus reduced digit loop:',c,'(g,k) pairs,3<=g<=20')
