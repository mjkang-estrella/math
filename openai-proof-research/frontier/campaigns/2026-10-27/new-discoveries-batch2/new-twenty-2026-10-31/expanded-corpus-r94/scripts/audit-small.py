from pathlib import Path
import json,itertools as it
D=Path(__file__).resolve().parents[1];out=[]
# Independent cycle convex-hull recursion through 13, separate from semicircle checker.
for n in range(5,14,2):
 full=(1<<n)-1;g=[0]*(1<<n)
 def hull(s):
  while True:
   t=s
   for a,b in it.combinations([i for i in range(n)if s>>i&1],2):
    delta=(b-a)%n
    step=1 if delta<=n//2 else -1
    v=a
    while v!=b:t|=1<<v;v=(v+step)%n
    t|=1<<b
   if s==t:return s
   s=t
 errors=0
 for s in range(1<<n):
  terminal=hull(s)!=full
  gone=full^s; m=n//2
  shortcut=any(all(gone>>((i+j)%n)&1 for j in range(m))for i in range(n))
  errors+=terminal!=shortcut
  if not terminal:
   vals={g[s^(1<<i)]for i in range(n)if s>>i&1};k=0
   while k in vals:k+=1
   g[s]=k
 r=dict(n=n,states=1<<n,terminal_predicate_disagreements=errors,initial_nimber=g[full]);out.append(r);print(r)
(D/'outputs/cycle-independent.json').write_text(json.dumps(out,indent=2)+'\n')
