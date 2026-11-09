import pathlib,sys,itertools,json,time,math
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D.parent/'expanded-corpus-r58/deps'))
import z3
start=time.monotonic();out=[]
def orient(a,b,c):return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
def crosses(a,b,c,d):return orient(a,b,c)*orient(a,b,d)<0 and orient(c,d,a)*orient(c,d,b)<0
for n in range(4,14):
 # Integer parabola: all points are vertices of a convex polygon, no collinear triples.
 pts=[(i,i*i) for i in range(n)];ts=list(itertools.combinations(range(n),3));s=z3.Solver();s.set(timeout=5000)
 vs=[z3.Bool('t'+str(i)) for i in range(len(ts))]
 for i,t in enumerate(ts):
  for h,u in enumerate(ts[:i]):
   common=len(set(t)&set(u));inter=common>0 or any(crosses(pts[a],pts[b],pts[c],pts[d]) for a,b in itertools.combinations(t,2) for c,d in itertools.combinations(u,2))
   if common>1 or not inter:s.add(z3.Or(z3.Not(vs[i]),z3.Not(vs[h])))
 threshold=math.ceil(n*n/9+2);s.add(z3.PbGe([(v,1) for v in vs],threshold));r=str(s.check());rec={'n':n,'triangles':len(ts),'threshold':threshold,'status':r,'points':pts}
 if r=='sat':rec['witness']=[t for v,t in zip(vs,ts) if z3.is_true(s.model().eval(v))]
 out.append(rec);print(rec,flush=True)
 if r=='sat' or time.monotonic()-start>95:break
(D/'outputs/triangles.json').write_text(json.dumps(out,indent=2)+'\n')
