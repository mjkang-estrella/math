import sys,os,json
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from sarkozy import build
from ils import ils
p,k,n=map(int,sys.argv[1:4]); secs=float(sys.argv[4]); seed=int(sys.argv[5]); out=sys.argv[6] if len(sys.argv)>6 else None
verts,adj,used,Dr=build(p,k,n); N=len(verts)
best,it=ils(adj,N,secs,seed)
print('p,k,n',p,k,n,'N',N,'best',len(best),'iterations',it,'target >',p**(n*(1-1/k**2))/p**(n-len(used)),flush=True)
if out: json.dump({'p':p,'k':k,'n':n,'used':used,'slice':[list(verts[v]) for v in sorted(best)]},open(out,'w'))
