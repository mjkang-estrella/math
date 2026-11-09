import pathlib,sys,itertools,time,json,random,math
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D.parent/'expanded-corpus-r58/deps'))
import z3
mode=sys.argv[1];start=time.monotonic();rng=random.Random(215);out=[]
patterns=set()
for x,y,z in itertools.permutations(range(3)):
 for p in [(x,x,y,z,x),(y,z,x,x,x),(x,z,x,y,x),(z,x,y,x,x)]:patterns.add(p)
def check(m,a,b,c,kind):
 s=z3.Solver();s.set(timeout=1500)
 A=[z3.Int('a'+str(i)) for i in range(m)];B=[z3.Int('b'+str(i)) for i in range(m)];L=[z3.Int('l'+str(i)) for i in range(m)];S=[z3.Int('s'+str(i)) for i in range(m)]
 for v in A+B+L+S:s.add(v>=0,v<3)
 s.add(A[0]==0)
 for i in range(m):
  ao=A[(i+a)%m] if kind=='alpha' else B[(i+b)%m]
  bo=B[(i+b)%m] if kind=='alpha' else A[(i+a)%m]
  vs=[A[i],B[i],ao,bo,S[i]]
  s.add(z3.Or(*[z3.And(*[v==n for v,n in zip(vs,p)]) for p in patterns]))
  s.add(z3.Distinct(L[i],L[(i-c)%m],S[i]))
 return str(s.check())
params=[]
if mode=='alpha':
 for m in range(3,85):
  for c in range(1,(m-1)//2+1):
   if math.gcd(c,m)>1:params.append((m,1,1,c,'alpha'))
else:
 for m in range(3,16):
  for a in range(1,(m-1)//2+1):
   for b in range(a,(m-1)//2+1):
    for c in range(1,(m-1)//2+1):
     if math.gcd(math.gcd(math.gcd(m,a),b),c)==1:params.append((m,a,b,c,'beta'))
 for _ in range(1000):
  m=rng.randint(16,60);a=rng.randint(1,(m-1)//2);b=rng.randint(1,(m-1)//2);c=rng.randint(1,(m-1)//2);params.append((m,a,b,c,'beta'))
for p in params:
 r=check(*p);out.append({'params':p,'status':r});print(p,r,flush=True)
 if r=='unsat' or time.monotonic()-start>102:break
(D/'outputs'/('snarks-'+mode+'.json')).write_text(json.dumps({'scope':'diagnostic constraint model of Lemma 5.2; not a certified semantic bridge','patterns':sorted(patterns),'results':out,'wall':time.monotonic()-start},indent=2)+'\n')
