import itertools,json,sys,time
N=int(sys.argv[1]);out=[]
def theta(p):
 unseen=set(range(len(p)));cyc=[]
 while unseen:
  a=max(unseen); c=[a];unseen.remove(a);b=p[a]
  while b!=a:c.append(b);unseen.remove(b);b=p[b]
  cyc.append(c)
 return tuple(x for c in reversed(cyc) for x in c)
def rank(a):return tuple(sum(x<y for x in a) for y in a)
patterns=list(itertools.permutations(range(3)))
if len(sys.argv)>2:patterns=[tuple(map(int,sys.argv[2]))]
for pat in patterns:
 prev=[()]
 for n in range(1,N+1):
  nxt=[];counts={k:0 for k in [1,2,4,8,16,32,64]};witness=[]
  for p in prev:
   for pos in range(n):
    q=p[:pos]+(n-1,)+p[pos:]
    # only new triples involving maximum
    m=pat.index(2); lo=[i for i in range(3) if i!=m]; inc=pat[lo[0]]<pat[lo[1]]
    pairs=itertools.combinations(range(pos+1,n),2) if m==0 else itertools.product(range(pos),range(pos+1,n)) if m==1 else itertools.combinations(range(pos),2)
    if any((q[i]<q[j])==inc for i,j in pairs):continue
    nxt.append(q);r=q
    for k in range(1,65):
     r=theta(r)
     if k in counts and r==q:counts[k]+=1
     if k==8 and r==q:
      s=q
      for _ in range(4):s=theta(s)
      if s!=q:witness.append(q)
  rec=dict(pattern=pat,n=n,avoid=len(nxt),counts=counts,witness=witness[:3]);print(json.dumps(rec),flush=True);out.append(rec)
  prev=nxt
json.dump(out,open('outputs/pattern-'+str(N)+'-'+(''.join(sys.argv[2:]) or 'all')+'.json','w'),indent=2)
