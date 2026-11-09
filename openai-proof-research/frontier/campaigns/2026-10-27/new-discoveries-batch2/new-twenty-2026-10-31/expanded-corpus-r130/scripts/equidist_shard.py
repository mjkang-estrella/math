import pathlib,sys,json,collections,itertools,time
D=pathlib.Path(__file__).resolve().parents[1];n=int(sys.argv[1]);kind=sys.argv[2];start=int(sys.argv[3]);end=int(sys.argv[4]);H=collections.Counter();count=0

def record(p):
 global count
 small=n+1;large=-1;rmin=rmax=0
 for x in reversed(p):
  if x<small:rmin+=1;small=x
  if x>large:rmax+=1;large=x
 if kind=='p':
  low=n+1;lmin=0
  for x in p:
   if x<low:lmin+=1;low=x
  H[rmin,lmin,rmax,sum(p[i]<p[i+1] for i in range(n-1))]+=1
 else:H[p.count(0),sum(x==i for i,x in enumerate(p)),rmin,n-len(set(p))]+=1
 count+=1

def perm(p,rem,ap,bound):
 if not rem:record(p);return
 for x in rem:
  if x>bound:continue
  nb=bound
  for a,b in ap:
   if x<a and b<nb:nb=b
  nap=ap+[(p[-1],x)] if p and p[-1]<x else ap
  perm(p+[x],[y for y in rem if y!=x],nap,nb)

def inv(p,seen,repeated):
 if len(p)==n:record(p);return
 for x in range(max(0,repeated),len(p)+1):inv(p+[x],seen|1<<x,max(repeated,x) if seen>>x&1 else repeated)
if kind=='p':
 prefixes=list(itertools.permutations(range(n),2))
 for index in range(start,min(end,len(prefixes))):
  prefix=prefixes[index];p=list(prefix);perm(p,[y for y in range(n) if y not in p],[(p[0],p[1])] if p[0]<p[1] else [],n)
  print(json.dumps(dict(prefix_index=index,prefix=prefix,total_objects_so_far=count)),flush=True)
else:
 prefixes=list(itertools.product(*[range(i+1) for i in range(5)]))
 for index in range(start,min(end,len(prefixes))):
  p=prefixes[index];seen=0;rep=-1;good=True
  for x in p:
   if x<rep:good=False;break
   if seen>>x&1:rep=max(rep,x)
   seen|=1<<x
  if good:inv(list(p),seen,rep)
  print(json.dumps(dict(prefix_index=index,prefix=p,total_objects_so_far=count)),flush=True)
name=f'equidist-{n}-{kind}-{start}-{end}'
(D/'outputs'/(name+'.json')).write_text(json.dumps(dict(n=n,kind=kind,prefix_range=[start,end],count=count,hist=[[*key,v] for key,v in sorted(H.items())]))+'\n')
print('COMPLETE',name,count,flush=True)
