import pathlib,json,random,time,sys,itertools,math
D=pathlib.Path(__file__).resolve().parents[1];n=int(sys.argv[1]);t=int(sys.argv[2]);rng=random.Random(193+n);N=1<<n;m=n//t*((1<<t)-1)+1;target=math.factorial(t)**(n//t)
preds=[[s^(1<<i) for i in range(n) if s>>i&1] for s in range(N)]
def count(A):
 d=[0]*N;d[0]=int(0 in A)
 for s in range(1,N):
  if s in A:d[s]=sum(d[v] for v in preds[s])
 return d[-1]
base=set();prefix=0
for b in range(n//t):
 for x in range(1<<t):base.add(prefix|(x<<(b*t)))
 prefix|=((1<<t)-1)<<(b*t)
assert len(base)==m and count(base)==target
start=time.monotonic();best=target;steps=0;restarts=0;A=base.copy();val=target;witness=None
while time.monotonic()-start<95:
 steps+=1
 if steps%2000==0:A=base.copy();val=target;restarts+=1
 u=rng.choice(tuple(A-{0,N-1}));v=rng.randrange(1,N-1)
 if v in A:continue
 A.remove(u);A.add(v);z=count(A)
 temp=max(.2,target*.03*(1-steps%2000/2000))
 if z>=val or rng.random()<math.exp((z-val)/temp):val=z
 else:A.remove(v);A.add(u)
 if z>best:best=z;witness=sorted(A);print(n,t,best,steps,flush=True)
 if best>target:break
out={'n':n,'t':t,'family_size':m,'tower_chains':target,'best_chains':best,'proposals':steps,'restarts':restarts,'seconds':time.monotonic()-start,'witness':witness,'coverage':'seeded stochastic swaps only; not exhaustive'}
(D/f'outputs/towers-{n}-{t}.json').write_text(json.dumps(out,indent=2));print(out,flush=True)
