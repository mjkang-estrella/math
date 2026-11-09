import pathlib,sys,itertools,time,json,functools,math
D=pathlib.Path(__file__).resolve().parents[1]
ns={'__file__':str(D/'scripts/gao.py')};exec((D/'scripts/gao.py').read_text().split('# Independent')[0],ns);nu=ns['nu'];mac=ns['mac']
cs={():1};out=[]
for n in range(1,10):
 t=time.monotonic();neg=[];mn=10**20;mx=0;count=0;nonzero=0
 for w in itertools.permutations(range(1,n+1)):
  if w[-1]==n:c=0
  else:
   sub=1
   for k in range(2,n):
    for z in itertools.combinations(w,k):
     if z[-1]==max(z):continue
     ranks={a:i+1 for i,a in enumerate(sorted(z))};sub+=cs[tuple(ranks[a] for a in z)]
   c=nu(w)-sub
  cs[w]=c;count+=1;mn=min(mn,c);mx=max(mx,c);nonzero+=bool(c)
  if c<0:neg.append([w,c])
 row=dict(n=n,count=count,min=mn,max=mx,negative=neg,nonzero=nonzero,seconds=time.monotonic()-t);out.append(row);print(json.dumps(row),flush=True);(D/'gao-fast-coverage.json').write_text(json.dumps(out,indent=2)+'\n')
