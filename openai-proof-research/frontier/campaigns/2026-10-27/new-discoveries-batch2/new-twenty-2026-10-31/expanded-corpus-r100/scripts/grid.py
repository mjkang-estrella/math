import itertools,json,time,sys
out=[]
def calc(n,r):
 N=2*n;full=(1<<N)-1;adj=[]
 for i in range(N):
  a=1<<(i^1)
  if i>=2:a|=1<<(i-2)
  if i+2<N:a|=1<<(i+2)
  adj.append(a)
 def nonface(mask):
  while mask:
   seen=0;todo=mask&-mask
   while todo:
    b=todo&-todo;todo^=b;seen|=b;todo|=adj[b.bit_length()-1]&mask&~seen
   if seen.bit_count()>r:return True
   mask&=~seen
  return False
 # Alexander dual: sigma is a face iff its complement has a component >r.
 faces=[]
 for size in range(N-r):
  fs=[sum(1<<i for i in a) for a in itertools.combinations(range(N),size) if nonface(full^sum(1<<i for i in a))];faces.append(fs)
 ranks=[0]
 for sz in range(1,len(faces)):
  idx={v:i for i,v in enumerate(faces[sz-1])};basis={}
  for mask in faces[sz]:
   v=0;b=mask
   while b:
    q=b&-b;b^=q;v^=1<<idx[mask^q]
   while v:
    pivot=v.bit_length()-1
    if pivot not in basis:basis[pivot]=v;break
    v^=basis[pivot]
  ranks.append(len(basis))
 ranks.append(0)
 betti={str(sz-1):len(faces[sz])-ranks[sz]-ranks[sz+1] for sz in range(len(faces))}
 return dict(n=n,r=r,dual_face_counts=list(map(len,faces)),dual_reduced_betti_F2=betti)
for n in range(2,7):
 for r in range(n,2*n):
  row=calc(n,r);out.append(row);print(row,flush=True)
for n in range(10,17):
 for r in range(2*n-5,2*n):
  row=calc(n,r);out.append(row);print(row,flush=True)
  json.dump(out,open('outputs/grid.json','w'),indent=2)
