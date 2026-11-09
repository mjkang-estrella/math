# Grundy values of the edge-removal game on spiders S(j,l): centre with j pendant edges and one leg of l edges.
# STARKAYLES_{k,n} = S(k-2, n) (star on k vertices, one branch extended to a path of edge-length n; index shift
# conventions do not affect periodicity).  S(0,l) = Kayles(l), S(j,0) = *j.
import sys,json
J=int(sys.argv[1]); L=int(sys.argv[2])
K=[0]*(L+1)
for n in range(1,L+1):
    s=set()
    for a in range(n):          # remove one edge: a + b = n-1
        s.add(K[a]^K[n-1-a])
    for a in range(n-1):        # remove two adjacent edges: a+b=n-2
        s.add(K[a]^K[n-2-a])
    g=0
    while g in s: g+=1
    K[n]=g
S=[[0]*(L+1) for _ in range(J+1)]
S[0]=K[:]
for j in range(1,J+1):
    S[j][0]=j
    for l in range(1,L+1):
        s=set()
        for r in range(1,j+1): s.add(S[j-r][l])          # centre/leaves remove pendants only
        for r in range(0,j+1): s.add((j-r)^K[l-1])        # centre removes leg edge (+ r pendants)
        Sj=S[j]
        for i in range(1,l):                              # vertex v_i on leg, 1<=i<=l-1
            s.add(Sj[i-1]^K[l-i]); s.add(Sj[i]^K[l-i-1]); s.add(Sj[i-1]^K[l-i-1])
        s.add(Sj[l-1])                                    # end vertex v_l
        g=0
        while g in s: g+=1
        Sj[l]=g
def period(seq,start_min=0):
    # smallest (p, n0) with seq[n+p]==seq[n] for n0<=n<len-p, require at least 3p+... tail coverage
    n=len(seq); best=None
    for p in range(1,n//4):
        # find minimal n0
        n0=None
        for t in range(n-p-1,-1,-1):
            if seq[t]!=seq[t+p]: n0=t+1;break
        else: n0=0
        if n-n0>=3*p+50 and n0<=n//2:
            return p,n0
    return None
out={'L':L,'kayles_period':period(K),'kayles_head':K[:30]}
for j in range(J+1):
    out[f'j{j}']={'period':period(S[j]),'max':max(S[j]),'head':S[j][:24]}
print(json.dumps(out))
