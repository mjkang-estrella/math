import random,json,time,pathlib,math
random.seed(680609);D=pathlib.Path(__file__).resolve().parents[1];start=time.monotonic();out=[]
def assess(a):
 n=len(a);inc=[set() for _ in a]
 for v in range(n):
  for w in a[v]:inc[w].add(v)
 if any(not s for s in inc):return None
 z=[]
 for v in range(n):
  closed=a[v]|{v};s={w for w in range(n) if w not in closed and inc[w]<=closed};ne=set(a[v])
  for w in s:ne|=a[w]
  z.append(len(ne)-len(s)-1)
 return max(z),sum(z),z
for n in [7,9,12,16,24,32]:
 best=None;count=0
 for restart in range(10):
  a=[{(v+j)%n for j in [1,2,3]} for v in range(n)];cur=assess(a)
  for step in range(1400):
   v=random.randrange(n);old=random.choice(tuple(a[v]));w=random.randrange(n)
   if w==v or w in a[v] or v in a[w]:continue
   a[v].remove(old);a[v].add(w);q=assess(a);count+=1
   temp=0.05+1.5*(1-step/1400)
   if q is not None and (q[:2]<=cur[:2] or random.random()<math.exp(min(0,((cur[0]-q[0])*n+cur[1]-q[1])/temp))):cur=q
   else:a[v].remove(w);a[v].add(old)
   if best is None or cur[:2]<best['score']:
    best={'score':cur[:2],'slacks':cur[2],'arcs':[[v,w] for v in range(n) for w in sorted(a[v])]}
   if cur[0]<0:break
 out.append({'n':n,'evaluations':count,'best':best})
print(json.dumps({'seed':680609,'seconds':time.monotonic()-start,'results':out},indent=2));(D/'outputs/quasi.json').write_text(json.dumps(out,indent=2))
