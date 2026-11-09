from pathlib import Path
import json,math
L=Path(__file__).resolve().parents[1];out=[]
def autos(a):
 n=len(a);p={};used=set()
 def rec():
  if len(p)==n:yield [p[i] for i in range(n)];return
  u=max((x for x in range(n) if x not in p),key=lambda x:sum(y in p for y in a[x]))
  cand=set(range(n))-used
  for v in a[u]:
   if v in p:cand&=a[p[v]]
  for w in sorted(cand):
   if all((v in a[u])==(p[v] in a[w]) for v in p):
    p[u]=w;used.add(w);yield from rec();used.remove(w);del p[u]
 yield from rec()
for family in ['mobius','prism']:
 for h in range(3,16):
  n=2*h;a=[set() for _ in range(n)]
  def edge(x,y):a[x].add(y);a[y].add(x)
  if family=='mobius':
   for i in range(n):edge(i,(i+1)%n);edge(i,(i+h)%n)
  else:
   for i in range(h):edge(i,(i+1)%h);edge(i+h,(i+1)%h+h);edge(i,i+h)
  minimum=n;count=0;witness=None;transitive=set()
  for p in autos(a):
   count+=1;transitive.add(p[0]);seen=set();lengths=[]
   for i in range(n):
    if i in seen:continue
    j=i;k=0
    while j not in seen:seen.add(j);k+=1;j=p[j]
    lengths.append(k)
   order=math.lcm(*lengths);regular=sum(k for k in lengths if k==order)
   if regular<minimum:minimum=regular;witness=p
  r={'family':family,'h':h,'vertices':n,'automorphisms_checked':count,'vertex_transitive':len(transitive)==n,'minimum_regular_vertices':minimum,'bound_holds':3*minimum>=2*n,'exception_note':'mobius h=3 is K3,3, explicitly excluded; split-PX classification not asserted','witness':witness};out.append(r);print({k:v for k,v in r.items() if k not in ['witness','exception_note']},flush=True)
 (L/'outputs/orbits.json').write_text(json.dumps(out,indent=2))
