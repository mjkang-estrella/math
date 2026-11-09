import random,json
rng=random.Random(106362167)
def graph(m,n):return [[j*n+k for j in range(max(0,i-1),min(m,i+2)) for k in range(max(0,l-1),min(n,l+2)) if (j,k)!=(i,l)] for i in range(m) for l in range(n)]
def positive(D,A):
 N=len(A)
 for q in range(N):
  if D[q]:continue
  E=D.copy()
  for iteration in range(1000):
   burnt={q}
   while True:
    new=burnt|{v for v in range(N) if v not in burnt and E[v]<sum(w in burnt for w in A[v])}
    if new==burnt:break
    burnt=new
   if len(burnt)==N:return False
   U=set(range(N))-burnt
   for v in U:
    for w in A[v]:
     if w not in U:E[v]-=1;E[w]+=1
   if E[q]:break
  else:return None
 return True
out=[]
for m,n in [(4,4),(4,5),(5,5),(5,6),(6,6)]:
 A=graph(m,n);deg=3*m-3;hits=0;unknown=0;trials=10000
 for t in range(trials):
  D=[0]*(m*n)
  if t<3*m-2:
   # source's optimal first-column divisor with one chip removed, also row/column translations
   for i in range(m):D[i*n]=2 if i in [0,m-1] else 3
   q=rng.choice([i*n for i in range(m)]);D[q]-=1
  else:
   for k in range(deg):D[rng.randrange(m*n)]+=1
  r=positive(D,A)
  if r:hits+=1;print('candidate',m,n,D,flush=True)
  if r is None:unknown+=1
 out.append({'m':m,'n':n,'degree_tested':deg,'effective_divisors_sampled':trials,'positive_rank_candidates':hits,'reduction_cap_unknown':unknown});print(out[-1],flush=True);open('outputs/gonality.json','w').write(json.dumps(out,indent=2))
