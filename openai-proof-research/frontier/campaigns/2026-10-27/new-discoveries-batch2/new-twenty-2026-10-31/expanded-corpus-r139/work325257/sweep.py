# Sweep n in [a,b]: (a) literal (j<=2^k) and corrected (j<2^k); (b) odd n: Descartes count on P(-x) (all real
# roots are negative since VH_n, D_n have positive coefficients), sign of P(-1), P(-1/2), root bracket;
# (c) even n: Descartes count; (e) P_n(-1) vs GF coefficient; (f) even n>=20.
import sys, json, pathlib, math
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent)); from tatami import P
a,b=int(sys.argv[1]),int(sys.argv[2]); out=pathlib.Path(sys.argv[3]); CAP=int(sys.argv[4]) if len(sys.argv)>4 else 10**9
M=b+2**10
# GF coefficients g_m for m=n-2: (1+z)(1-2z) / ((1-2z^2) sqrt(1-4z^2))
L=b+1
c=[0]*L
for k in range(0,L,2): c[k]=math.comb(k,k//2)            # 1/sqrt(1-4z^2)
d=[0]*L
for k in range(L):
    d[k]=c[k]+(2*d[k-2] if k>=2 else 0)                     # /(1-2z^2)
num=[1,-1,-2]                                               # (1+z)(1-2z)=1-z-2z^2
g=[sum(num[t]*d[k-t] for t in range(3) if k-t>=0) for k in range(L)]
cache={}
def getP(n):
    if n not in cache: cache[n]=P(n)
    return cache[n]
def sc(q):
    s=[x for x in q if x]; return sum(1 for u,v in zip(s,s[1:]) if (u>0)!=(v>0))
def sign_at(p,xn,xd):  # sign of p(xn/xd), xd>0: Horner on p(x)*xd^D with incremental powers
    D=len(p)-1; acc=p[D]; pw=1
    for k in range(D-1,-1,-1):
        pw*=xd; acc=acc*xn+p[k]*pw
    return (acc>0)-(acc<0)
rows=[]; viol=[]
for n in range(a,b+1):
    p=getP(n); r={'n':n,'deg':len(p)-1}
    pm1=sum(cc if k%2==0 else -cc for k,cc in enumerate(p)); r['e_ok']=(pm1==g[n-2])
    if not r['e_ok']: viol.append(('e',n))
    neg=[cc if k%2==0 else -cc for k,cc in enumerate(p)]; r['desc_neg']=sc(neg)
    if n%2==0:
        r['c_ok']= True if r['desc_neg']==0 else 'undecided'
        if n>=20: r['f_ok']=(sum(abs(x) for x in p)==pm1); 
        if n>=20 and not r['f_ok']: viol.append(('f',n))
    else:
        r['b_count_one']= True if r['desc_neg']==1 else 'undecided'
        r['sign_m1']=sign_at(p,-1,1); r['sign_mhalf']=sign_at(p,-1,2)
        r['b_bracket_ok']=(r['sign_m1']<0 and r['sign_mhalf']>=0)
        if not r['b_bracket_ok']: viol.append(('b-bracket',n))
    if r.get('c_ok')=='undecided' or r.get('b_count_one')=='undecided': viol.append(('descartes-undecided',n))
    # (a): n mod 2^k == 2 (k>=2 automatically)
    for k in range(2,20):
        if 2**k> n+2: break
        if n % 2**k != 2: continue
        I=(n-2)//2**(k-1)
        for j in range(1,2**k+1):
            if n+j>CAP: continue
            q=getP(n+j)
            eq=all((p[i] if i<len(p) else 0)==(q[i] if i<len(q) else 0) for i in range(I+1))
            if not eq:
                bad=min(i for i in range(I+1) if (p[i] if i<len(p) else 0)!=(q[i] if i<len(q) else 0))
                viol.append(('a-literal' if j==2**k else 'a-corrected',n,k,j,bad))
    rows.append(r)
    with open(str(out)+'.partial','a') as fh: fh.write(json.dumps({'row':r,'viol_so_far':len(viol)})+'\n')
    print(json.dumps({'n':n,'viol':[x for x in viol if x[1]==n]}),flush=True)
    for m in [x for x in cache if x< n]: del cache[m]
out.write_text('\n'.join(json.dumps(x) for x in rows)+'\n')
print(json.dumps({'range':[a,b],'violations':viol}))
