import random,math,json,itertools
random.seed(129)
def conn(n,E):
 adj=[set() for _ in range(n)]
 for a,b in E:adj[a].add(b);adj[b].add(a)
 if min(map(len,adj))<3:return False
 for r in range(3):
  for cut in itertools.combinations(range(n),r):
   alive=set(range(n))-set(cut);seen={min(alive)};stack=list(seen)
   while stack:
    v=stack.pop()
    for u in adj[v]&alive-seen:seen.add(u);stack.append(u)
   if seen!=alive:return False
 return True
def gamma(n,E):
 w=[7**i for i in range(n-1)]+[0];steps=[w[a]-w[b] for a,b in E];steps+= [-s for s in steps];S={0};L=[1]
 for t in range(1,4):S.update({a+b for a in S for b in steps});L.append(len(S))
 h=[sum((-1)**j*math.comb(n,j)*L[i-j] for j in range(i+1)) for i in range(4)];ga=[]
 for i in range(4):ga.append(h[i]-sum(ga[j]*math.comb(n-1-2*j,i-j) for j in range(i)))
 return ga,L
for n in range(7,12):
 cases=[]
 for trial in range(100):
  p=random.choice([.4,.5,.6,.7]);E={e for e in itertools.combinations(range(n),2) if random.random()<p}
  if conn(n,E):cases.append(('random',E))
 for extra in range(8):
  E={(a,b) for a in range(3) for b in range(3,n)}
  for j,e in enumerate(itertools.combinations(range(3),2)):
   if extra>>j&1:E.add(e)
  cases.append(('split',E.copy()));E.add((3,4));cases.append(('split+one',E.copy()));E.remove((0,3))
  if conn(n,E):cases.append(('swap',E.copy()))
 for typ,E in cases:
  ga,L=gamma(n,E);expected=False
  for A in itertools.combinations(range(n),3):
   B=set(range(n))-set(A)
   edge=lambda a,b:tuple(sorted((a,b))) in E
   if all(edge(a,b) for a in A for b in B) and not any(edge(a,b) for a,b in itertools.combinations(B,2)):expected=True;break
  ok=(ga[3]==0)==expected
  print(json.dumps({'kind':typ,'n':n,'edges':sorted(E),'gamma':ga,'ehrhart':L,'ok':ok}),flush=True)
