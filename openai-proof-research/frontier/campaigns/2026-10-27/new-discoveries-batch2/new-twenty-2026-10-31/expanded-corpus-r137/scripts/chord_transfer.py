# 329080 existence part: D_m = 123123 followed by m isolated chords at the end.
# Record, over all side masks, the set of (faces - m, end-edge inner/outer sides on same face?).
import sys,pathlib,json
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
def dart_data(w,mask):
    L=len(w); partner=[0]*L; seen={}
    for i,c in enumerate(w):
        if c in seen: partner[i]=seen[c]; partner[seen[c]]=i
        else: seen[c]=i
    side=[(mask>>i)&1 for i in range(L)]
    sig=[0]*L
    for i in range(L):
        s=side[i]; step=1 if s==0 else -1; j=(i+step)%L
        while side[j]!=s: j=(j+step)%L
        sig[i]=j
    comp=[-1]*L;f=0
    for i in range(L):
        if comp[i]<0:
            x=i
            while comp[x]<0: comp[x]=f; x=sig[partner[x]]
            f+=1
    extra=(0 not in side)+(1 not in side)
    # dart i represents the boundary segment from endpoint i to sig(i) on side(i).
    # end edge = backbone arc between endpoint L-1 and endpoint 0. Its inner side is the inner boundary
    # segment from the largest inner endpoint l to the smallest inner endpoint a, traversed in the face
    # cycle between darts tau(l) and a; its outer side is the outer segment from the smallest outer
    # endpoint v to the largest outer endpoint u, traversed between tau(v) and u.  So compare comp[a], comp[u].
    inner=[i for i in range(L) if side[i]==0]; outer=[i for i in range(L) if side[i]==1]
    ein=comp[inner[0]] if inner else 'emptyIn'
    eout=comp[outer[-1]] if outer else 'emptyOut'
    return f+extra, ein==eout
def state(w,mask):
    f,same=dart_data(w,mask); return f-(len(w)//2-3),same
# empirical check of the transfer rules: adding an isolated chord at the end edge
#  in-in / out-out: (d,s)->(d,s); in-out (either order): (d,True)->(d,True), (d,False)->(d-2,True)
viol=0;checked=0
for m in range(0,5):
    w=[0,1,2,0,1,2]
    for k in range(m): w+=[3+k,3+k]
    w2=tuple(w+[3+m,3+m]); w=tuple(w); L=len(w)
    for mask in range(1<<(L+2)):
        d,s=state(w,mask&((1<<L)-1)); d2,s2=state(w2,mask)
        b1=(mask>>L)&1; b2=(mask>>(L+1))&1
        exp=(d,s) if b1==b2 else ((d,True) if s else (d-2,True))
        checked+=1
        if (d2,s2)!=exp: viol+=1
print('transfer rule check',checked,'violations',viol)
res={}
for m in range(0,7):
    w=[0,1,2,0,1,2]
    for k in range(m): w+= [3+k,3+k]
    w=tuple(w); n=len(w)//2; S=set()
    for mask in range(1<<len(w)):
        f,same=dart_data(w,mask); S.add((f-m,same))
    gs=sorted({(2+n-(fm+m))//2 for fm,_ in S})
    res[m]={'pairs':sorted(S),'genera':gs}; print(m,sorted(S),gs,flush=True)
pathlib.Path(sys.argv[1]).write_text(json.dumps({str(k):{'pairs':[list(p) for p in v['pairs']],'genera':v['genera']} for k,v in res.items()},indent=1)+'\n')
