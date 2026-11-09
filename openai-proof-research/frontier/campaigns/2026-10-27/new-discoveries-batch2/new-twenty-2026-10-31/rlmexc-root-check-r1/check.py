import itertools,sys,json
def stats(p):
    n=len(p)  # p[i] = pi(i+1), values 1..n
    inv=sum(1 for i in range(n) for j in range(i+1,n) if p[i]>p[j])
    excv=frozenset(p[i] for i in range(n) if p[i]>i+1)
    rlmv=frozenset(p[i] for i in range(n) if all(p[i]<p[j] for j in range(i+1,n)))
    seen=[0]*n; mc=n
    for s in range(n):
        if not seen[s]:
            L=0;x=s
            while not seen[x]: seen[x]=1; x=p[x]-1; L+=1
            mc=min(mc,L)
    return inv,excv,rlmv,mc
out={}
for n,R,E in [(8,{1,4,6,7},{2,3,5,8}),(9,{1,5,7,8},{2,3,4,6,9})]:
    raw={k:0 for k in range(1,n+1)}; hits=[]
    for p in itertools.permutations(range(1,n+1)):
        inv,excv,rlmv,mc=stats(p)
        if rlmv==frozenset(R) and excv==frozenset(E):
            hits.append((p,inv,mc))
            for k in range(1,mc+1): raw[k]+=(-1)**inv
    out[n]={'hits':[[list(h[0]),h[1],h[2]] for h in hits],'raw_coeff_k3':raw[3],'vor_coeff_k3':(-1)**(n-1)*raw[3]}
    print(n,len(hits),'raw k=3:',raw[3],'VoR k=3:',(-1)**(n-1)*raw[3])
json.dump(out,open(sys.argv[1],'w'),indent=1)
