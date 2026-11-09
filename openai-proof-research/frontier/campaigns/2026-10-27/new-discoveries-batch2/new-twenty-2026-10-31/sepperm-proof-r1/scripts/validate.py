from math import comb
import pathlib,json,itertools,collections
D=pathlib.Path(__file__).resolve().parents[1];N=250
q=[0]*(N+1)
for n in range(1,N+1):q[n]=(n==1)+q[n-1]+sum(q[i]*q[n-i] for i in range(1,n))
powers=[[0]*(N+1) for _ in range(N+1)];powers[0][0]=1;powers[1]=q[:]
for j in range(2,N+1):
 for n in range(N+1):powers[j][n]=powers[j-1][n]-(powers[j-1][n-1]+powers[j-2][n-1] if n else 0)
 assert all(x>=0 for x in powers[j])
h=[]
for r in range(N+1):
 row=[0]*(r+1)
 row=[0]*(2*r+1)
 for i in range(r+1):
  v=comb(r+1,i+1)*comb(r+i,i)//(r+1)
  for l in range(r+1):row[i+l]+=v*comb(r,l)
 h.append(row)
S=[[0]*(n+1) for n in range(N+1)]
for n in range(1,N+1):
 for k in range(1,n+1):
  r=k-1;m=n-k
  S[n][k]=sum(c*(powers[j][m]+(powers[j+1][m] if j+1<=N else 0)) for j,c in enumerate(h[r]) if j<=m)
 assert sum(S[n])==q[n]
 assert n<3 or S[n][1]<S[n][2] and all(S[n][k]>=S[n][k+1] for k in range(2,n))
 print(json.dumps({'n':n,'row':S[n],'log_concave':all(S[n][k]**2>=S[n][k-1]*S[n][k+1] for k in range(2,n))}),flush=True)
for r in range(1,N):
 H=[0]*(2*r+5)
 for j,c in enumerate(h[r]):H[j]+=c;H[j+1]+=c
 for j,c in enumerate(h[r+1]):H[j+1]-=c;H[j+2]+=c
 pref=list(itertools.accumulate(H[1:]));# Prefix positivity is an experimental test, not assumed.
 # No assertion: this stronger sufficient condition may fail.
 print(json.dumps({'kernel_r':r,'coefficient_min':min(H),'prefix_min':min(pref),'H':H if r<=6 else None}),flush=True)
for n in range(1,8):
 row=collections.Counter()
 for p in itertools.permutations(range(n)):
  if any(tuple(1+sum(p[t[j]]<p[t[i]] for j in range(4)) for i in range(4)) in [(2,4,1,3),(3,1,4,2)] for t in itertools.combinations(range(n),4)):continue
  row[sum(all(p[j]<p[i] for j in range(i)) for i in range(n))]+=1
 assert [row[k] for k in range(n+1)]==S[n]
print('PASS: exact n<=250; independent avoidance enumeration n<=7; kernel diagnostics r<=249',flush=True)
(D/'results-exact.json').write_text(json.dumps({'rows':S,'q':q,'kernel_indices_diagnosed':249}))
