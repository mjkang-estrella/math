# Generating polynomials P_n^{(1)} (pattern 1-23) and P_n^{(2)} (pattern 1-32) by a rank-of-last DP,
# cross-checked against brute force for small n.
import itertools, sys, json, pathlib
def occ123(s):
    n=len(s); return sum(1 for j in range(1,n-1) if s[j]<s[j+1] for i in range(j) if s[i]<s[j])
def occ132(s):
    n=len(s); return sum(1 for j in range(1,n-1) if s[j]>s[j+1] for i in range(j) if s[i]<s[j+1])
def padd(p,q,sh=0):
    if len(p)<len(q)+sh: p.extend([0]*(len(q)+sh-len(p)))
    for i,c in enumerate(q):
        if c: p[i+sh]+=c
def polys(N,cls):
    # state: dict rank a of last element (1..m) -> polynomial
    res=[[1],[1]]
    st={1:[1]}
    for m in range(1,N):
        new={}
        for a,p in st.items():
            for b in range(1,m+2):
                if cls==1: sh=(a-1) if b>a else 0
                else: sh=(b-1) if b<=a else 0
                q=new.setdefault(b,[])
                padd(q,p,sh)
        st=new
        tot=[]
        for p in st.values(): padd(tot,p)
        while len(tot)>1 and tot[-1]==0: tot.pop()
        res.append(tot)
    return res
def brute(n,f):
    c={}
    for s in itertools.permutations(range(n)):
        k=f(s); c[k]=c.get(k,0)+1
    return [c.get(i,0) for i in range(max(c)+1)]
if __name__=='__main__':
    N=int(sys.argv[1])
    P1=polys(N,1); P2=polys(N,2)
    for n in range(0,9):
        if n>=1:
            assert brute(n,occ123)==P1[n],(n,brute(n,occ123),P1[n])
            assert brute(n,occ132)==P2[n],(n,)
    print('brute force check n<=8 ok')
    for n in range(8): print(n,P1[n],P2[n])
    out=pathlib.Path(sys.argv[2]); out.write_text(json.dumps({'P1':P1,'P2':P2}))
