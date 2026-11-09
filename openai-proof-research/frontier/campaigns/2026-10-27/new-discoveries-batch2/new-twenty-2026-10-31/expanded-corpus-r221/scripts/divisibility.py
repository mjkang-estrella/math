import pathlib,json,itertools,random,time,sys
D=pathlib.Path(__file__).resolve().parents[1]
def stats(a):
 n=len(a);full=(1<<n)-1;omega=[0]*(1<<n);perfect=[True]*(1<<n);pd=[True]*(1<<n);indep=[True]*(1<<n);chi=[0]*(1<<n);bad=[];p5=False
 for s in range(1,1<<n):
  bit=s&-s;v=bit.bit_length()-1;t=s^bit
  omega[s]=max(omega[t],1+omega[t&a[v]])
  indep[s]=indep[t] and not(t&a[v])
  if indep[s]:chi[s]=1
  else:
   chi[s]=n;u=t
   while True:
    I=u|bit
    if indep[I]:chi[s]=min(chi[s],1+chi[s^I])
    if not u:break
    u=(u-1)&t
  perfect[s]=chi[s]==omega[s] and all(perfect[s^(1<<x)] for x in range(n) if s>>x&1)
  if omega[s]<2:continue
  if any(not pd[s^(1<<x)] for x in range(n) if s>>x&1):pd[s]=False;continue
  u=s;div=False
  while u:
   if perfect[u] and omega[s^u]<omega[s]:div=True;break
   u=(u-1)&s
  pd[s]=div
  if not div:bad.append(s)
 for S in itertools.combinations(range(n),5):
  s=sum(1<<v for v in S);deg=sorted((a[v]&s).bit_count() for v in S)
  if deg!=[1,1,2,2,2]:continue
  reach=1<<S[0]
  for _ in range(5):
   for v in S:
    if reach>>v&1:reach|=a[v]&s
  if reach==s:p5=True;break
 cutsets=[]
 for s in bad:
  c=s
  while c:
   if omega[c]==c.bit_count() and (s^c).bit_count()>1:
    rest=s^c;reach=rest&-rest
    for _ in range(n):
     for v in range(n):
      if reach>>v&1:reach|=a[v]&rest
    if reach!=rest:cutsets.append((s,c))
   c=(c-1)&s
 return pd[full],bad,cutsets,p5
lines=(D/'sources/atlas.txt').read_text().splitlines();idx=0;counts={};notpd=[];hits=[]
while idx<len(lines):
 name=lines[idx];n=int(lines[idx+1].split()[1]);idx+=2;a=[0]*n
 while idx<len(lines) and not lines[idx].startswith('GRAPH'):
  u,v=map(int,lines[idx].split());idx+=1;a[u]|=1<<v;a[v]|=1<<u
 res=stats(a);counts[n]=counts.get(n,0)+1
 if not res[0]:notpd.append(name)
 if res[2] or (not res[0] and not res[3]):hits.append((name,res))
out={'unlabelled_atlas_counts':counts,'not_perfectly_divisible':notpd,'violations':hits,'method':'exact subset chromatic number and clique number; hereditary perfectness; perfect max-clique transversal for every induced subgraph; clique cutset tested for each MNPD subgraph'}
print(json.dumps(out),flush=True);(D/'outputs/divisibility-atlas.json').write_text(json.dumps(out,indent=2))
