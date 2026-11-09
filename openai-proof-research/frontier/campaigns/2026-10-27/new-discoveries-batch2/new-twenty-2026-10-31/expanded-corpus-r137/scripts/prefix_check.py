# 368752: build P_m(n) literally (source Def. 2.1) and measure |dS|/|S| for S = colour-sum fibre set.
import itertools,json,sys
def flip(v,i,d,m):
    perm,col=v
    p=list(perm[:i][::-1])+list(perm[i:]); c=[(x+d)%m for x in col[:i][::-1]]+list(col[i:])
    return (tuple(p),tuple(c))
res=[]
for n,ms in ((1,[6,8,12]),(2,[6,8,10,12]),(3,[8,10])):
    for m in ms:
        V=[(p,c) for p in itertools.permutations(range(n)) for c in itertools.product(range(m),repeat=n)]
        k=m//2; S={v for v in V if sum(v[1])%m<k}
        edges=set()
        for v in V:
            for i in range(1,n+1):
                for d in (1,-1):
                    w=flip(v,i,d,m); edges.add(frozenset((v,w)))
        bd=sum(1 for e in edges if len(e)==2 and len(e&S)==1)
        deg=set()
        res.append({'n':n,'m':m,'V':len(V),'S':len(S),'boundary':bd,'ratio':bd/len(S),'bound':n*(n+1)/k})
        print(res[-1],flush=True)
json.dump(res,open('outputs/prefix-reversal-check.json','w'),indent=1)
