# 340286 exact evaluation/interpolation test (see lecture_hall.py header for definitions).
import sys, json, time, random
from fractions import Fraction as Fr
def det(M):
    M=[row[:] for row in M]; n=len(M); d=Fr(1)
    for c in range(n):
        p=next((r for r in range(c,n) if M[r][c]!=0),None)
        if p is None: return Fr(0)
        if p!=c: M[c],M[p]=M[p],M[c]; d=-d
        d*=M[c][c]; inv=1/M[c][c]
        for r in range(c+1,n):
            f=M[r][c]*inv
            if f:
                for k in range(c,n): M[r][k]-=f*M[c][k]
    return d
def ells(yv,imax):
    ell={}
    for i in range(1,imax+1):
        rows=list(range(1,(i+1)//2+1)); cols=list(range(i//2+1,i+1))
        def E(Lval):
            P=lambda s: Lval if s==i else ell[s]
            return -det([[(-P(c-r+1)) if c>=r else Fr(0) for c in cols] for r in rows])
        b=E(Fr(0)); a=E(Fr(1))-b
        t=Fr(1)
        for k in range(1,i+1): t*=yv[k]**(i+1-k)
        ell[i]=(t-b)/a
    return ell
def interp(xs,vs):
    # Newton -> monomial coefficients (exact)
    n=len(xs); coef=list(vs)
    for j in range(1,n):
        for i in range(n-1,j-1,-1): coef[i]=(coef[i]-coef[i-1])/(xs[i]-xs[i-j])
    poly=[Fr(0)]*n
    for i in range(n-1,-1,-1):
        # poly = poly*(x-xs[i]) + coef[i]
        new=[Fr(0)]*n
        for k in range(n-1): new[k+1]+=poly[k]
        for k in range(n): new[k]-=xs[i]*poly[k]
        new[0]+=coef[i]; poly=new
    return poly
if __name__=='__main__':
    imax=int(sys.argv[1]); j=int(sys.argv[2]); seed=int(sys.argv[3]); t0=time.time()
    random.seed(seed); base={k:Fr(random.randint(2,7)) for k in range(1,imax+1)}
    K=2*imax+6
    vals=[]
    for y0 in range(1,K+1):
        yv=dict(base); yv[j]=Fr(y0); vals.append(ells(yv,imax))
        if time.time()-t0>100: print(json.dumps({'timeout_at_point':y0})); sys.exit()
    res=[]
    for i in range(1,imax+1):
        a=max(i-1-j,0); deg=a+i
        xs=[Fr(y0) for y0 in range(1,deg+2)]; poly=interp(xs,[vals[x-1][i]*Fr(x)**a for x in range(1,deg+2)])
        # verify on extra points
        ok=all(sum(c*Fr(x)**k for k,c in enumerate(poly))==vals[x-1][i]*Fr(x)**a for x in range(deg+2,min(K,deg+5)+1))
        low=[k for k,c in enumerate(poly) if c!=0]
        res.append({'i':i,'a':a,'deg_bound':deg,'interp_verified':ok,'lowest_nonzero_power_of_N':low[0] if low else None,'negative_power_certified':bool(low) and ok and low[0]<a})
    print(json.dumps({'imax':imax,'free_variable':j,'others':{k:str(v) for k,v in base.items() if k!=j},'any_negative':any(r['negative_power_certified'] for r in res),'all_verified':all(r['interp_verified'] for r in res),'sec':round(time.time()-t0,1),'rows':res}))
