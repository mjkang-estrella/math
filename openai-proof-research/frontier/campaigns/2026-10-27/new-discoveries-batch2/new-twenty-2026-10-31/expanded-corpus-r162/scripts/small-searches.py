import pathlib,json,itertools,math,random,time
D=pathlib.Path(__file__).resolve().parents[1];out={};start=time.monotonic()
def save(): (D/'outputs/small-searches.json').write_text(json.dumps(out,indent=2))
# All binary subsets of H(2,q), quotient parameter check.
res=[]
for q in [2,3,4]:
 N=q*q;adj=[sum(1<<j for j in range(N) if (i//q==j//q) != (i%q==j%q)) for i in range(N)];par=set();perfect=0
 for s in range(1,1<<(N-1)): # complement representatives: last vertex out
  ins={q*2-2-(s&a).bit_count() for i,a in enumerate(adj) if s>>i&1}
  if len(ins)!=1:continue
  outs={(s&a).bit_count() for i,a in enumerate(adj) if not s>>i&1}
  if len(outs)!=1:continue
  b=ins.pop();c=outs.pop();perfect+=1;par.add((b,c))
  if (b+c)//math.gcd(b,c)>q and 2*q*q<(q+1)*(b+c):raise Exception(('counterexample',q,s,b,c))
 res.append({'q':q,'n':2,'subsets_mod_complement':(1<<(N-1))-1,'perfect_subsets':perfect,'parameters':sorted(par)})
out['344692']=res;save();print('Hamming',res,flush=True)
# Exact integer-scaled rational sums for all permutations until the first zero; no float testing.
res=[]
for n in [8,9,10]:
 L=math.lcm(*(j*j-i*i for i in range(1,n+1) for j in range(i+1,n+1)))
 w={(a,b):L//(a*a-b*b) for a in range(1,n+1) for b in range(1,n+1) if a!=b};count=0;witness=None
 for p in itertools.permutations(range(1,n+1)):
  count+=1
  if sum(w[a,b] for a,b in zip(p,p[1:]))==0:witness=p;break
 res.append({'n':n,'permutations_visited':count,'witness':witness,'common_denominator':L})
out['344049']=res;save();print('Sun',res,flush=True)
# Balanced cube cuts; orientations can freely split crossing edges between -1 and +1.
res=[];rng=random.Random(162)
for d in [4,7,10,13]:
 N=1<<d;M=d*N//2;target=next(z for z in range(M//3-1,M//3+3) if z%2==0 and max(z,(M-z)//2,(M-z+1)//2)-min(z,(M-z)//2)<=1)
 f=[int(i>=N//2) for i in range(N)];rng.shuffle(f);nb=[[v^(1<<j) for j in range(d)] for v in range(N)]
 cross=sum(f[v]!=f[u] for v in range(N) for u in nb[v])//2;goal=M-target
 for step in range(300000):
  if cross==goal:break
  a=rng.randrange(N);b=rng.randrange(N)
  if f[a]==f[b]:continue
  delta=2*d-2*sum(f[v]!=f[a] for v in nb[a])-2*sum(f[v]!=f[b] for v in nb[b])+2*int(b in nb[a])
  if abs(cross+delta-goal)<abs(cross-goal) or rng.random()<0.002:
   f[a]^=1;f[b]^=1;cross+=delta
 actual=sum(f[v]!=f[u] for v in range(N) for u in nb[v])//2
 assert actual==cross and sum(f)==N//2
 row={'d':d,'target_zero':target,'actual_zero':M-cross,'steps':step+1,'success':cross==goal}
 if cross==goal:
  (D/f'outputs/cube-{d}.json').write_text(json.dumps({'dimension':d,'ones':[i for i in range(N) if f[i]],'zero_edges':target,'crossing_edges':cross}))
 res.append(row);print('cube',row,flush=True)
out['349146']=res;save()
print('wall',time.monotonic()-start)
