from checks import *
out=[]
for n in range(5,66,2):
 for k in range(3,n,2):
  g=math.gcd(n,k-1)
  if g<3:continue
  patterns=[({0,1},{2}), (set(range(g-1)),set(range(2,g,2)))]
  for a,(R,C) in enumerate(patterns):
   _,_,_,H,V=board(n,k,R,C);z=len(cycles(compose(V,H)))
   out.append(dict(n=n,k=k,g=g,pattern=a,cycles=z))
(L/'mixed-checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('triple deviations', [r for r in out if r['pattern']==0 and r['cycles']!=r['g']-2][:8])
print('chain failures', [r for r in out if r['pattern']==1 and r['cycles']!=1][:8])
