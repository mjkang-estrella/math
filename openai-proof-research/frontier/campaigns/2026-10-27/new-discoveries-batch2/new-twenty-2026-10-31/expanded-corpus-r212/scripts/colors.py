import itertools,random,json,pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(212);out=[]
def color(A,q):
 n=len(A);col=[-1]*n
 def dfs(done,used):
  if done==n:return 1
  v=max((i for i in range(n) if col[i]<0),key=lambda i:(len({col[j] for j in A[i] if col[j]>=0}),sum(col[j]<0 for j in A[i])))
  forbidden={col[j] for j in A[v] if col[j]>=0};ans=0
  for c in range(min(used+1,q)):
   if c in forbidden:continue
   col[v]=c;ans+=(q-used if c==used else 1)*dfs(done+1,max(used,c+1));col[v]=-1
  return ans
 return dfs(0,0)
def girth(A,k):
 if k==3:return any(j in A[h] for i in range(len(A)) for j,h in itertools.combinations(A[i],2))
 return any(len(A[i]&A[j])>=2 for i in range(len(A)) for j in range(i))
def graph(n):
 while True:
  stubs=list(range(n))*3;rng.shuffle(stubs);A=[set() for _ in range(n)]
  for i,j in zip(stubs[::2],stubs[1::2]):
   if i==j or j in A[i]:break
   A[i].add(j);A[j].add(i)
  else:return A
A=[set() for _ in range(10)]
for i in range(5):
 for a,b in [(i,(i+1)%5),(i,i+5),(i+5,(i+2)%5+5)]:A[a].add(b);A[b].add(a)
P={q:color(A,q) for q in [3,4]};H=[set() for _ in range(14)]
for i in range(7):
 for d in [0,1,3]:H[i].add(7+(i+d)%7);H[7+(i+d)%7].add(i)
HW={q:color(H,q) for q in [3,4]};print('references',P,HW,flush=True)
for n in range(6,19,2):
 for z in range(40):
  A=graph(n);tri=girth(A,3);square=girth(A,4)
  if tri and square:continue
  for q in [3,4]:
   c=color(A,q);lower=(q==4 and not tri);upper=not square
   row={'n':n,'trial':z,'q':q,'triangle_free':not tri,'square_free':not square,'colorings':c,'edges':[(i,j) for i in range(n) for j in A[i] if i<j],'lower_applicable':lower,'upper_applicable':upper,'lower_violated':lower and c**10<P[q]**n,'upper_violated':upper and c**14>HW[q]**n};out.append(row)
   print(json.dumps(row),flush=True)
(D/'outputs/colors.json').write_text(json.dumps({'petersen':P,'heawood':HW,'rows':out},indent=2)+'\n')
