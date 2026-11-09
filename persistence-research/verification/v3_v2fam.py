# Independent computation of sup v2 over a 1-insertion family A(nu):
# all decimal strings using exactly the non-1 digits nu plus any number of 1s.
# v2(n) >= k iff 2^k | (last k digits). Build suffixes right-to-left; with
# t = suffix/2^k, appending digit d at position k is allowed iff d = t (mod 2),
# and t' = (d*5^k + t)/2. Runs of 1s terminate (v2(9s-10^k) is finite), so the
# DFS is finite; its termination is itself a proof that sup v2 < infinity.
import sys
from collections import Counter
sys.setrecursionlimit(10000)
def v2(x):
    return (x & -x).bit_length()-1 if x else 10**9
def supv2(nu, want_witness=True):
    digs=sorted(set(nu)); rem0=tuple(nu.count(d) for d in digs)
    best=[-1,None]; nodes=[0]
    def dfs(k,t,rem,s):
        nodes[0]+=1
        full = sum(rem)==0
        val = k + v2(t) if full else k
        if full and k==0: val=-1
        if val>best[0]: best[0]=val; best[1]=s if full else None
        p5=5**k
        # digit 1 (unlimited) if t odd
        if t&1:
            dfs(k+1,(p5+t)>>1,rem,s+10**k)
        for i,d in enumerate(digs):
            if rem[i] and (d&1)==(t&1):
                r=list(rem); r[i]-=1
                dfs(k+1,(d*p5+t)>>1,tuple(r),s+d*10**k)
    dfs(0,0,rem0,0)
    return best[0],best[1],nodes[0]
# note: at k=0, t=0 (even) so the last digit must be even: odd-terminal members
# have v2=0, which never beats the even-terminal maximum.
for nu in ([4,4,7],[2,6],[2]+[7]*6+[8]*6+[9]*2):
    b,w,n=supv2(nu)
    print(f"nu={''.join(map(str,nu))}: sup v2 = {b}  (DFS nodes {n})")
    if w is not None:
        print("   full-member witness:", w, "digits:", len(str(w)), "v2:", v2(w),
              "non-1 multiset ok:", sorted(c for c in str(w) if c!='1')==sorted(map(str,nu)))
