# Family G_{a,b}: hub edge xy, twins t,u adjacent to both x,y, a triangles at x, b triangles at y.
# Verify gamma~c(G)=n/2 by brute force, and M(G) has the perfect-matching OCD of size n/2 (lower bound n/2
# from vertex-node counting), hence equality.
import sys, json, itertools, pathlib
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent)); from ocd import ocd_number, middle, conn_mask
def build(a,b):
    x,y,t,u=0,1,2,3; E=[(x,y),(t,x),(t,y),(u,x),(u,y)]; F=[(t,x),(u,y)]; nxt=4
    for i in range(a): p,q=nxt,nxt+1; nxt+=2; E+=[(x,p),(x,q),(p,q)]; F.append((p,q))
    for j in range(b): p,q=nxt,nxt+1; nxt+=2; E+=[(y,p),(y,q),(p,q)]; F.append((p,q))
    adj=[0]*nxt
    for p,q in E: adj[p]|=1<<q; adj[q]|=1<<p
    return adj,E,F
out=[]
for a in range(1,4):
  for b in range(1,4):
    adj,E,F=build(a,b); n=len(adj)
    g=ocd_number(adj)
    M=middle(adj)
    Eo=[(u,v) for u in range(n) for v in range(u+1,n) if adj[u]>>v&1]
    D=0
    for e in F: D|=1<<(n+Eo.index(tuple(sorted(e))))
    full=(1<<len(M))-1; dom=0
    for v in range(len(M)):
        if D>>v&1: dom|=M[v]|(1<<v)
    ok=(dom==full) and conn_mask(M, full&~D)
    out.append({'a':a,'b':b,'n':n,'ocd_G':g,'matching_OCD_in_M':ok,'size':len(F),'equality':ok and g==len(F)==n//2})
    print(out[-1],flush=True)
