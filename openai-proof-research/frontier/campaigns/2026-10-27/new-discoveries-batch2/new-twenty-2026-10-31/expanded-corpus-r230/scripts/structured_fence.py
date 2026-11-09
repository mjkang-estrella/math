import pathlib,sys,random,json,itertools
D=pathlib.Path(__file__).resolve().parents[1]
src=(D/'scripts/fence.py').read_text().split('N,lo,hi=')[0];exec(compile(src,str(D/'scripts/fence.py'),'exec'))
rng=random.Random(230);done=0
for n in (24,32,48):
 patterns={0,(1<<(n-1))-1,sum(1<<i for i in range(n-1) if i%2)}
 for a in range(1,n-1):patterns.add((1<<a)-1)
 for period in (3,4,5,7,9):
  for run in range(1,period):patterns.add(sum(1<<i for i in range(n-1) if i%period<run))
 for _ in range(60):patterns.add(rng.getrandbits(n-1))
 for w in sorted(patterns):
  for m in (2,3,5,10,20):
   a=poly(n,m,w);down=False
   for j in range(1,len(a)):
    if a[j]<a[j-1]:down=True
    if down and a[j]>a[j-1]:print('COUNTEREXAMPLE',n,m,w,j,a,flush=True);sys.exit(1)
   done+=1
 print(json.dumps(dict(n=n,patterns=len(patterns),m=[2,3,5,10,20],cumulative=done,result='no dip')),flush=True)
