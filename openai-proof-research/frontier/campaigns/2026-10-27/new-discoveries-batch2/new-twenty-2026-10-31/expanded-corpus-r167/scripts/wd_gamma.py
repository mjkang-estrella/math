# For non-trivially WD connected graphs: decide whether gamma(G x C4) < 2 gamma(G) (exact B&B), and same for C5.
import sys,json,time,pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from g6 import parse
from wd import nbh,wellcovered,mds_sizes,trivially,strong,cyc
def dom_le(n,N,k):
    # is there a dominating set of size <= k ?  B&B
    full=(1<<n)-1
    maxc=max(bin(x).count('1') for x in N)
    def rec(dom,k):
        if dom==full: return True
        if k==0: return False
        und=full&~dom; cnt=bin(und).count('1')
        if cnt>k*maxc: return False
        # pick undominated vertex with fewest dominators
        best=None;bc=99; m=und
        while m:
            v=(m&-m).bit_length()-1; m&=m-1
            c=bin(N[v]).count('1')
            if c<bc: bc=c;best=v
        m=N[best]
        while m:
            u=(m&-m).bit_length()-1; m&=m-1
            if rec(dom|N[u],k-1): return True
        return False
    return rec(0,k)
def gamma(n,N):
    k=1
    while not dom_le(n,N,k): k+=1
    return k
if __name__=='__main__':
    t0=time.time(); out={'checked':0,'C4_gamma_drop':0,'no_C4_drop':[]}
    for f in sys.argv[1:]:
        for line in open(f):
            n,adj=parse(line)
            if not wellcovered(n,adj): continue
            N=nbh(n,adj)
            if len(mds_sizes(n,N))!=1 or trivially(n,adj,N): continue
            g=gamma(n,N); out['checked']+=1
            nP,NP=strong(n,N,4,nbh(*cyc(4)))
            if dom_le(nP,NP,2*g-1): out['C4_gamma_drop']+=1
            else:
                nQ,NQ=strong(n,N,5,nbh(*cyc(5)))
                out['no_C4_drop'].append({'g6':line.strip(),'gamma':g,'C5_drop':dom_le(nQ,NQ,2*g-1)})
    out['secs']=round(time.time()-t0,1); print(json.dumps(out))
