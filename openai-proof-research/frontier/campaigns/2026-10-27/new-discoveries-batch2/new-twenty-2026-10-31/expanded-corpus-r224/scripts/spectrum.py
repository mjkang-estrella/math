import pathlib,gzip,json
D=pathlib.Path(__file__).resolve().parents[1];s=gzip.decompress((D/'raw/atlas.dat.gz').read_bytes()).decode().splitlines();j=0;spec={};counts={}
while j<len(s):
 n=int(s[j+1].split()[1]);j+=2;es=[]
 while j<len(s) and not s[j].startswith('GRAPH'):es.append(tuple(map(int,s[j].split())));j+=1
 if n==0:continue
 adj=[0]*n
 for u,v in es:adj[u]|=1<<v;adj[v]|=1<<u
 a=[0]*(1<<n);a[0]=1;ind=[True]*(1<<n)
 for m in range(1,1<<n):
  bit=m&-m;k=bit.bit_length()-1;ind[m]=ind[m^bit] and not(adj[k]&(m^bit))
  t=m
  while t:
   if ind[t]:a[m]+=(-1 if t.bit_count()%2==0 else 1)*a[m^t]
   t=(t-1)&m
 spec.setdefault(n,set()).add(a[-1]);counts[n]=counts.get(n,0)+1
print(json.dumps({n:{'graphs':counts[n],'distinct_acyclic_orientation_counts':len(v),'values':sorted(v)} for n,v in spec.items()}))
