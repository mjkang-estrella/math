import pathlib,json,itertools,sys,time
D=pathlib.Path(__file__).resolve().parents[1]; cap=int(sys.argv[1]); seeds=sys.argv[2]=='seeds';start=time.monotonic();out=[];total=0
for c in range(1,cap+1):
 cnt=pre=ext=0
 for k in range(1,4):
  for lower in itertools.combinations(range(1,c),k-1):
   A=lower+(c,); mask=(1<<c)-1
   for seed in range(1<<c) if seeds else [mask]:
    cnt+=1;total+=1;state=seed;seen={};w=[]
    while state not in seen:
     seen[state]=len(w);bit=int(any(not(state>>(x-1)&1) for x in A));w.append(bit);state=((state<<1)|bit)&mask
    mu=seen[state];p=len(w)-mu
    # state repeat gives eventual period; pull preperiod back at output level
    while mu and w[mu-1]==w[mu+p-1]:mu-=1
    if not mu:continue
    pre+=1
    def val(n):
     if n < -c:return 1
     if n<0:return seed>>(-n-1)&1
     if n<len(w):return w[n]
     return w[mu+(n-mu)%p]
    # check all k: b=kp+x; after b+mu periodic; for sufficiently large k all prefix comparisons stabilize
    good=True
    for x in A:
     for kk in range(1,(mu+c)//p+3):
      b=kk*p+x
      if any(val(n)==0 and val(n-b)==0 for n in range(b+mu+p)):
       good=False;break
     if not good:break
    if good:
     ext+=1;(D/'outputs/subtraction-counterexample.json').write_text(json.dumps({'A':A,'seed':seed,'preperiod':mu,'period':p,'w':w}));print('COUNTEREXAMPLE',A,seed,mu,p,flush=True);sys.exit()
    if time.monotonic()-start>105:
     out.append({'max_move':c,'cases':cnt,'positive_preperiod':pre,'all_extensions':ext,'complete':False});(D/f'outputs/subtraction-{sys.argv[2]}-{cap}.json').write_text(json.dumps({'total':total,'rows':out},indent=2));sys.exit()
 out.append({'max_move':c,'cases':cnt,'positive_preperiod':pre,'all_extensions':ext,'complete':True});print(out[-1],flush=True)
(D/f'outputs/subtraction-{sys.argv[2]}-{cap}.json').write_text(json.dumps({'total':total,'rows':out},indent=2))
