import sys,json
sys.path.insert(0,__file__.rsplit('/',1)[0])
from hj_counts import build
k=int(sys.argv[1]); n=k-1
V,idx,cl,st=build(k,n); N=len(V)
conf=[0]*N
for g in cl:
    for x in g:
        for y in g:
            if x!=y: conf[x]|=1<<y
starmask=[sum(1<<x for x in s) for s in st]
sols=[]
def rec(blue,red):
    # find a star not hit
    best=None;bc=99
    for sm in starmask:
        if sm&blue: continue
        av=sm&~red
        c=bin(av).count('1')
        if c<bc: bc=c;best=av
        if c==0: return
    if best is None:
        sols.append(blue); return
    av=best; r2=red
    while av:
        x=(av&-av).bit_length()-1; av&=av-1
        if conf[x]&blue==0:
            rec(blue|1<<x, r2|conf[x])
        r2|=1<<x
rec(0,0)
# minimal solutions only distinct; report count and sizes
sizes={}
for b in sols: sizes[bin(b).count('1')]=sizes.get(bin(b).count('1'),0)+1
print(json.dumps({'k':k,'nsol':len(sols),'sizes':sizes,'examples':[[V[i] for i in range(N) if b>>i&1] for b in sols[:40]]}))
