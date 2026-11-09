# min over balanced 3-partitions of class-edges for a blow-up of base graph H (parts independent). pure python
import sys,json
def comps(total,caps):
    out=[]
    suf=[0]*(len(caps)+1)
    for i in range(len(caps)-1,-1,-1): suf[i]=suf[i+1]+caps[i]
    def rec(i,rem,cur):
        if i==len(caps):
            if rem==0: out.append(tuple(cur))
            return
        for v in range(max(0,rem-suf[i+1]),min(caps[i],rem)+1):
            cur.append(v); rec(i+1,rem-v,cur); cur.pop()
    rec(0,total,[]); return out
def D3(edges,sizes):
    n=sum(sizes); t=n//3
    cost=lambda c: sum(c[u]*c[v] for u,v in edges)
    C=comps(t,sizes); best=None; arg=None
    memo={}
    for c1 in C:
        rem=tuple(s-x for s,x in zip(sizes,c1))
        if rem not in memo:
            bb=None;aa=None
            for c2 in comps(t,rem):
                c3=tuple(r-x for r,x in zip(rem,c2))
                if c3<c2: continue
                v=cost(c2)+cost(c3)
                if bb is None or v<bb: bb=v;aa=(c2,c3)
            memo[rem]=(bb,aa)
        bb,aa=memo[rem]; val=cost(c1)+bb
        if best is None or val<best: best=val; arg=(c1,)+aa
    return best,arg
if __name__=='__main__':
    spec=json.loads(open(sys.argv[1]).read())
    for edges,sizes in spec:
        n=sum(sizes); b,a=D3(edges,sizes)
        print(sizes,'n=',n,'D3b=',b,'bound=',round(4*n*n/81,3),'ratio=',round(b/n/n,5),'VIOL' if b>4*n*n/81+1e-9 else '',a,flush=True)
