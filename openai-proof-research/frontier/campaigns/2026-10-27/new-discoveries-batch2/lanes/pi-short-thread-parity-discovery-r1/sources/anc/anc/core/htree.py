import brute, decomp
def H(a,b,l,c,d):
    """u has legs a,b; v has legs c,d (markable lengths); bridge of l markable edges. Each leg ends in a pendant edge."""
    edges=[]; nxt=[2]
    def leg(root,x):
        prev=root
        for _ in range(x+1):
            v=nxt[0]; nxt[0]+=1; edges.append((prev,v)); prev=v
    prev=0
    for _ in range(l-1):
        v=nxt[0]; nxt[0]+=1; edges.append((prev,v)); prev=v
    edges.append((prev,1))
    for x in (a,b): leg(0,x)
    for x in (c,d): leg(1,x)
    return nxt[0],edges
for p in [(5,2,1,3,1),(3,1,3,4,1)]:
    n,e=H(*p)
    print("H",p,"n=",n,"m=",sum(p),"decomp G=",decomp.grundy_original_tree(n,e),"brute G=",brute.grundy_tree(n,e))
