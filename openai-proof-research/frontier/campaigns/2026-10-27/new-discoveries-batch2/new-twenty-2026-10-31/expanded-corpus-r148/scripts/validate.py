import pathlib,json,itertools,collections,runpy
L=pathlib.Path(__file__).resolve().parents[1]
petrov=json.loads((L/'outputs/petrov.json').read_text());statuses=collections.Counter()
for x in petrov:
 statuses[x['status']]+=1
 if x['status']!='SAT':continue
 counts=sum(x['matrix'],[]);dest=[0]*len(counts);k=x['k']
 for s,t,u,v in x['certificate']:
  assert u//k==s//k and u%k==t%k and v//k==t//k and v%k==s%k
  counts[s]-=1;assert counts[s]>=0;dest[u]+=1
  if s!=t:counts[t]-=1;assert counts[t]>=0;dest[v]+=1
 assert not any(counts) and all(c==1 for c in dest)
print('Petrov certificates checked',len(petrov),dict(statuses))
D=json.loads((L/'outputs/jacobi-28.json').read_text())
for n in range(3,10):
 counts=collections.Counter()
 for p in itertools.permutations(range(1,n+1)):
  good=True
  for i,a in enumerate(p):
   j=i+1
   while j<n and p[j]>a:j+=1
   if (j-i-1)%2:good=False;break
  if good:counts[p[-2],p[-1]]+=1
 assert sum(counts.values())==D[n-2]['total']
 # Independently compute up-down Entringer numbers literally.
 E=collections.Counter(p[0] for p in itertools.permutations(range(1,n)) if all((p[i]<p[i+1])==(i%2==0) for i in range(n-2)))
 assert all(counts[a,b]==E[a-b] for a in range(1,n+1) for b in range(1,n+1))
 print('Jacobi literal cross-check',n,sum(counts.values()))
print('Validation PASS')
