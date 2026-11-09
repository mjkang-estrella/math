import pathlib,sys,itertools,time,json
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D.parent/'expanded-corpus-r58/deps'))
import z3
start=time.monotonic();out=[]
for alpha,beta,gamma in itertools.product(range(1,5),range(4,8),range(3,8)):
 if alpha+beta+gamma<13:continue
 N=alpha*beta+alpha*gamma+beta*gamma;s=z3.Solver();s.set(timeout=1800)
 A=[z3.Int('a'+str(i)) for i in range(alpha)];B=[z3.Int('b'+str(i)) for i in range(beta)];C=[z3.Int('c'+str(i)) for i in range(gamma)]
 seq=A+B+C;s.add(C[-1]==0)
 for u,v in zip(seq,seq[1:]):s.add(u>v)
 t=[a-b for a in A for b in B]+[b-c for b in B for c in C]
 for a in A:
  for c in C:s.add((a-c)%2==0);t.append((a-c)/2)
 for x in t:s.add(x>=1,x<=N)
 s.add(z3.Distinct(t));r=str(s.check());rec={'type':[alpha,beta,gamma],'N':N,'status':r}
 if r=='sat':rec['entries']=[s.model().eval(x).as_long() for x in seq]
 out.append(rec);print(rec,flush=True)
 if r=='sat' or time.monotonic()-start>100:break
(D/'outputs/ulrich.json').write_text(json.dumps(out,indent=2)+'\n')
