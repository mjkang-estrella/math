# Counts of 132-avoiding permutations pi of [n] with pi^2 (SAv), pi^2,pi^3 (Omega_{1,2,3}) and all powers (PAv) avoiding 132.
import sys
def avoid132(p):
    # O(n) check using stack technique: 132-avoiding iff no i<j<k with p_i < p_k < p_j
    n=len(p); minleft=[0]*n; m=10**9
    for i in range(n): minleft[i]=m; m=min(m,p[i])
    st=[]  # scan right to left keeping candidates for '2'
    for j in range(n-1,-1,-1):
        # find any k>j with minleft[j] < p_k < p_j
        while st and st[-1]<=minleft[j]: st.pop()
        if st and st[-1]<p[j]: return False
        st.append(p[j])
    return True
def gen132(n):
    # recursive: 132-avoiders: n placed at position i; left part > right part values
    if n==0: yield (); return
    for i in range(n):
        # left has i elements with values n-i..n-1 (0-based: values n-1-i..n-2), right has values 0..n-2-i
        for L in gen132(i):
            for R in gen132(n-1-i):
                yield tuple(x+(n-1-i) for x in L)+(n-1,)+R
def compose(p,q): return tuple(p[q[i]] for i in range(len(p)))
def order_powers(p):
    n=len(p); ident=tuple(range(n)); pw=p; out=[]
    while True:
        out.append(pw)
        if pw==ident: return out
        pw=compose(p,pw)
N=int(sys.argv[1])
for n in range(1,N+1):
    sav=om=pav=0; pav_fix=0
    for p in gen132(n):
        p2=compose(p,p)
        if not avoid132(p2): continue
        sav+=1
        p3=compose(p,p2)
        if not avoid132(p3): continue
        om+=1
        if all(avoid132(x) for x in order_powers(p)):
            pav+=1
            if p[n-1]==n-1: pav_fix+=1
    print(n,'SAv',sav,'Omega123',om,'PAv',pav,'PAv_with_n_fixed',pav_fix,flush=True)
