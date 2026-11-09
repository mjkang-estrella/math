import pathlib,itertools,json
D=pathlib.Path(__file__).resolve().parents[1];rows=[]
for n in range(1,6):
 es=list(itertools.combinations(range(n),2));tested=0;bad=[]
 for mask in range(1<<len(es)):
  a=[0]*n
  for j,(u,v) in enumerate(es):
   if mask>>j&1:a[u]|=1<<v;a[v]|=1<<u
  independent=[True]*(1<<n);chi=[0]*(1<<n)
  for s in range(1,1<<n):
   b=s&-s;v=b.bit_length()-1;independent[s]=independent[s^b] and not(a[v]&(s^b));chi[s]=n
   q=s
   while q:
    if q&b and independent[q]:chi[s]=min(chi[s],1+chi[s^q])
    q=(q-1)&s
  best=n
  def rec(v,classes):
   global best
   if v==n:
    z=0
    for s in range(1,1<<n):z=max(z,sum(bool(s&c) for c in classes)-chi[s])
    best=min(best,z);return
   for j,c in enumerate(classes):
    if not(a[v]&c):classes[j]|=1<<v;rec(v+1,classes);classes[j]=c
   classes.append(1<<v);rec(v+1,classes);classes.pop()
  rec(0,[])
  def cycle(k):
   for perm in itertools.permutations(range(n),k):
    if perm[0]!=min(perm) or perm[1]>perm[-1]:continue
    if all(a[perm[j]]>>perm[(j+1)%k]&1 for j in range(k)):return True
   return False
  for l in range(2,n+1):
   if l+1<=n and cycle(l+1):continue
   complete=(n==l and mask==(1<<len(es))-1)
   if best<chi[-1]-l or (l>=3 and not complete and best<chi[-1]-l+1):bad.append([mask,l,best,chi[-1]])
  tested+=1
 r={'n':n,'all_labelled_simple_graphs':tested,'violations':bad};rows.append(r);print(r,flush=True)
(D/'outputs/chromatic.json').write_text(json.dumps(rows,indent=2))
