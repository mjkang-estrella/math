# Exhaustive search for chord diagrams with genus range {1,2} (329080).
# Uses heredity: if D' is a sub-diagram of D (delete chords) then every thickening of D restricts
# to a thickening of D' that is a subsurface, so max g(D') <= max g(D) and min g(D') <= min g(D).
# Hence C_n = {D with n chords : max genus <= 2} is generated from C_{n-1} by adding one chord.
import sys,json,random,time,pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from chord import canon,prep,faces
N=int(sys.argv[1]); out=sys.argv[2]
def maxg_ok(w,rng):
    L=len(w); n=L//2; theta=prep(w); gs=set()
    masks=list(range(0,1<<L,2)); rng.shuffle(masks)
    for mask in masks:
        g=(2+n-faces(theta,L,mask))//2; gs.add(g)
        if g>2: return None
    return gs
rng=random.Random(1)
C={(0,0):{0,1}}  # n=1
res={'1':{'class_size':1,'gr12':[]}}
t=time.time()
for n in range(2,N+1):
    cand=set()
    for w in C:
        L=len(w)
        for i in range(L+1):
            for j in range(i,L+1):
                u=list(w); u.insert(j,n-1); u.insert(i,n-1); cand.add(canon(tuple(u)))
    newC={}
    for w in cand:
        gs=maxg_ok(w,rng)
        if gs is not None: newC[w]=gs
    C=newC
    gr12=[''.join(str(c+1) for c in w) for w,gs in C.items() if gs=={1,2}]
    ranges={}
    for gs in C.values(): ranges[str(sorted(gs))]=ranges.get(str(sorted(gs)),0)+1
    res[str(n)]={'candidates':len(cand),'class_size':len(C),'ranges_in_class':ranges,'gr12':sorted(gr12)}
    print(n,len(cand),len(C),ranges,sorted(gr12),f"t={time.time()-t:.1f}",flush=True)
    pathlib.Path(out).write_text(json.dumps(res,indent=1)+'\n')
