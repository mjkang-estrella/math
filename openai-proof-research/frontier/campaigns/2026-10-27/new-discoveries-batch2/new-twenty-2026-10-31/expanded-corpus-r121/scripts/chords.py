import sys,math,json
n=int(sys.argv[1]);allcount=trees=0
# Ordered endpoints: recursively match smallest free endpoint. Reject cyclic intersection graphs early.
def rec(left,E,parent,edges):
 global allcount,trees
 if not left:
  allcount+=1
  if edges==n-1:trees+=1
  return
 a=left[0]
 for j,b in enumerate(left[1:],1):
  P=parent[:];add=0;good=True
  def root(i):
   while P[i]!=i:i=P[i]
   return i
  for i,(c,d) in enumerate(E):
   if a<c<b<d or c<a<d<b:
    u,v=root(i),root(len(E))
    if u==v:good=False;break
    P[u]=v;add+=1
  if good:rec(left[1:j]+left[j+1:],E+[(a,b)],P,edges+add)
rec(list(range(2*n)),[],list(range(n)),0)
print(json.dumps(dict(n=n,acyclic_intersection_matchings=allcount,tree_matchings=trees,claimed=math.comb(3*n,n)//(2*n+1))))
