import sys,json,collections,hashlib
N=int(sys.argv[1]);u,v=sys.argv[2:];orders={'riop':'RXL','rpop':'RLX','iop':'LXR','pop':'LRX'}
D=[{(-1,0,0,0):1}]
def run(order,l,r,s,nl,nr,index):
 val=0
 for x in order:
  if x=='X':
   if s:break
   val+=1
  else:
   t=l if x=='L' else r;n=nl if x=='L' else nr
   val+=t[index]
   if t[1]!=0:break
 return val
for n in range(1,N+1):
 d=collections.Counter()
 for nl in range(n):
  nr=n-1-nl
  for l,lc in D[nl].items():
   for r,rc in D[nr].items():
    for s in [0,1]:
     if nr and r[0]==s:continue
     a=run(orders[u],l,r,s,nl,nr,2);b=run(orders[v],l,r,s,nl,nr,3)
     d[s,l[1]+r[1]+s,a,b]+=lc*rc
 D.append(d);h=collections.Counter()
 for (s,z,a,b),c in d.items():h[z,a,b]+=c
 # third pair does not refine omi, but stronger refined test is also recorded
 basic=collections.Counter()
 for (z,a,b),c in h.items():basic[a,b]+=c
 bad=[(key,c,h[key[0],key[2],key[1]]) for key,c in list(h.items()) if c!=h[key[0],key[2],key[1]]]
 badbasic=[(key,c,basic[key[1],key[0]]) for key,c in list(basic.items()) if c!=basic[key[1],key[0]]]
 print(json.dumps(dict(nodes=n,pair=[u,v],objects=sum(d.values()),states=len(d),refined_bad_first=bad[:3],basic_bad_first=badbasic[:3],hist_sha256=hashlib.sha256(repr(sorted(h.items())).encode()).hexdigest())),flush=True)
