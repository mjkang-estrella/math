import sys,os,json,random
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from sarkozy import build, greedy_ls
import itertools
p,k,n=map(int,sys.argv[1:4]); iters=int(sys.argv[4]); out=sys.argv[5]
verts,adj,used,Dr=build(p,k,n); N=len(verts)
b,A=greedy_ls(adj,N,iters,7)
I=[verts[v] for v in range(N) if A>>v&1]
free=[i for i in range(n) if i not in used]
full=[]
for v in I:
    for f in itertools.product(range(p),repeat=len(free)):
        c=[0]*n
        for t,i in enumerate(used): c[i]=v[t]
        for t,i in enumerate(free): c[i]=f[t]
        full.append(c)
json.dump({'p':p,'k':k,'n':n,'slice_size':b,'slice':[list(v) for v in I],'used':used,'A':full},open(out,'w'))
print('slice',b,'|A|',len(full))
