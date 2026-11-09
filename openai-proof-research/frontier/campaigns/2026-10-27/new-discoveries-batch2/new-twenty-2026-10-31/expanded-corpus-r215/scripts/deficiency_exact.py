import sys,pathlib,json,itertools,random,time
D=pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(D.parent/'fresh-corpus-r10/pydeps'))
from sympy.solvers.simplex import linprog
rng=random.Random(215 if len(sys.argv)==1 else 1215); results=[];start=time.monotonic()
for d in (range(5,11) if len(sys.argv)==1 else range(11,15)):
 for rep in range(20 if len(sys.argv)==1 else 12):
  w=sorted(rng.randint(1,35) for _ in range(d))
  if sum(w)%2==0:w[-1]+=1
  wins=[]
  for bits in itertools.product([0,1],repeat=d):
   score=sum(a*b for a,b in zip(w,bits))
   if score*2>sum(w) and all((score-w[i])*2<sum(w) for i in range(d) if bits[i]):wins.append(bits)
  val,x=linprog([1]*d,[[-b for b in bits] for bits in wins],[-1]*len(wins))
  delta=2-val; r={'d':d,'w':w,'cover':list(map(str,x)),'deficiency':str(delta),'reciprocal':str(1/delta)};results.append(r)
  print(r,flush=True)
  if (1/delta).q!=1:
   (D/'outputs/deficiency-exact-suspect.json').write_text(json.dumps(r,indent=2)+'\n');break
  if time.monotonic()-start>100:break
 if (1/delta).q!=1 or time.monotonic()-start>100:break
(D/'outputs'/('deficiency-exact.json' if len(sys.argv)==1 else 'deficiency-deeper.json')).write_text(json.dumps(results,indent=2)+'\n')
