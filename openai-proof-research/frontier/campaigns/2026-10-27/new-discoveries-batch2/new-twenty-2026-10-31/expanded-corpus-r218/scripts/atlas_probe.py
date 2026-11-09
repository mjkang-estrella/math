import pathlib,runpy,json,random,itertools,sys
D=pathlib.Path(__file__).resolve().parents[1]
s=(D/'scripts/finite_graphs.py').read_text().split('rows=[]')[0];ns={'__file__':str(D/'scripts/finite_graphs.py')};exec(compile(s,str(D/'scripts/finite_graphs.py'),'exec'),ns)
mc,connected,conn,removable=[ns[k] for k in ['mc','connected','conn','removable']]
def graphs():
 lines=(D/'sources/atlas.txt').read_text().splitlines();idx=0
 while idx<len(lines):
  name=lines[idx];n=int(lines[idx+1].split()[1]);idx+=2;a=[0]*n
  while idx<len(lines) and not lines[idx].startswith('GRAPH'):
   u,v=map(int,lines[idx].split());idx+=1;a[u]|=1<<v;a[v]|=1<<u
  if n==7:yield name,a
count=0;critical=0;bad=[];minslack=100.;splitchecks=0;remchecks=0
for name,a in graphs():
 n=len(a);es=[(u,v) for u in range(n) for v in range(u) if a[u]>>v&1];count+=1;c=mc(a);vals=[]
 for u,v in es:
  b=a.copy();b[u]^=1<<v;b[v]^=1<<u;vals.append(mc(b))
 if vals and all(z!=c for z in vals):
  critical+=1
  if min(vals)<c<max(vals):bad.append({'name':name,'id':374340,'mc':c,'deleted':vals})
 if not connected(a):continue
 delta=min(v.bit_count() for v in a)
 for k in range(3,delta):
  if conn(a,k):
   remchecks+=1
   if not(delta%2==0 and len(es)==n*(n-1)//2) and not removable(a,k,(delta+2)//2):bad.append({'name':name,'id':374904,'k':k})
 # split recognition by trying every clique part; independent degree connectivity is needed.
 full=(1<<n)-1
 split=any(all((a[v]&s)==(s^(1<<v)) for v in range(n) if s>>v&1) and all((a[v]&(full^s))==0 for v in range(n) if not s>>v&1) for s in range(1<<n))
 if split:
  for r in range(3,n+1):
   if not conn(a,r-1):continue
   claw=False
   for v in range(n):
    neigh=[u for u in range(n) if a[v]>>u&1]
    for sub in itertools.combinations(neigh,r):
     if all(not(a[u]>>w&1) for u,w in itertools.combinations(sub,2)):claw=True;break
    if claw:break
   if claw:continue
   splitchecks+=1
   if not any(all(a[t[i]]>>t[(i+1)%n]&1 for i in range(n)) for p in itertools.permutations(range(1,n)) for t in [(0,)+p]):bad.append({'name':name,'id':374204,'r':r})
print(json.dumps({'unlabelled_order7':count,'critical':critical,'removability_instances':remchecks,'split_hamiltonicity_instances':splitchecks,'violations':bad}));(D/'logs/atlas-results.json').write_text(json.dumps({'unlabelled_order7':count,'critical':critical,'removability_instances':remchecks,'split_hamiltonicity_instances':splitchecks,'violations':bad},indent=2))
