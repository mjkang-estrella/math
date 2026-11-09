import itertools,json,time,sys
A={(3,2,1,4),(3,2,4,1),(4,2,1,3)}
B={tuple(reversed(t)) for t in [(2,3,1,4),(3,2,1,4),(4,2,1,3)]}
def insert(ps,patterns,n):
 out=[]
 for p in ps:
  for pos in range(n):
   q=p[:pos]+(n,)+p[pos:];bad=False
   for ix in itertools.combinations([i for i in range(n) if i!=pos],3):
    ix=sorted((*ix,pos));vals=[q[i] for i in ix];s=sorted(vals);pat=tuple(s.index(v)+1 for v in vals)
    if pat in patterns:bad=True;break
   if not bad:out.append(q)
 return out
def counts(ps,n):
 ds=[0]*(n+1)
 for p in ps:
  mx=0;k=0
  for j,v in enumerate(p,1):mx=max(mx,v);k+=mx==j
  ds[k]+=1
 return ds
pa=pb=[()];start=time.monotonic()
for n in range(1,int(sys.argv[1])+1):
 pa=insert(pa,A,n);pb=insert(pb,B,n);ca,cb=counts(pa,n),counts(pb,n)
 print(json.dumps(dict(n=n,Pi5=ca,reversePi4=cb,equal=ca==cb,wall=time.monotonic()-start)),flush=True)
 if ca!=cb:break
