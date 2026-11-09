# 340286 (Katthan arXiv:1809.01377v1, Def. 3.1, Conj. 3.4): Lecture Hall sequence via (LHS_i):
#   E_i(P) = -det of M(P) rows 1..ceil(i/2), cols floor(i/2)..i,  M_{r,c} = -P_{c-r+1} (c>=r) else 0,
#   E_i = y1^i y2^(i-1) ... yi.
# Exact certificate test: specialise all variables except y_j to fixed integers; a negative power of y_j in the
# resulting univariate Laurent polynomial proves l_i is not a polynomial (a polynomial specialises to a polynomial).
import sys, json, time, random
import sympy as sp
def run(imax, j, seed, tlimit):
    random.seed(seed); y=sp.Symbol('y'); t0=time.time()
    vals={k: sp.Integer(random.randint(2,9)) for k in range(1,imax+1)}
    Y=lambda k: y if k==j else vals[k]
    ell={}
    out=[]
    for i in range(1,imax+1):
        if time.time()-t0>tlimit: break
        L=sp.Symbol('L')
        P=lambda s: L if s==i else ell[s]
        rows=list(range(1,(i+1)//2+1)); cols=list(range(i//2+1, i+1))  # 1-indexed; matches the printed E_3, E_4
        Mx=sp.Matrix(len(rows),len(cols),lambda a,b: (-P(cols[b]-rows[a]+1)) if cols[b]>=rows[a] else 0)
        E=-Mx.det(method='berkowitz')
        target=sp.Integer(1)
        for k in range(1,i+1): target*=Y(k)**(i+1-k)
        sol=sp.solve(sp.Eq(sp.expand(E),target),L)
        assert len(sol)==1
        li=sp.cancel(sp.together(sol[0]))
        num,den=sp.fraction(li)
        dpoly=sp.Poly(den,y); npoly=sp.Poly(num,y)
        # den should be c*y^a; check whether y^a divides num
        a=dpoly.degree(); assert len(dpoly.terms())==1
        low=min(m[0] for m,_ in npoly.terms()) if npoly.terms() else 0
        neg = low < a
        ell[i]=li
        out.append({'i':i,'den_y_degree':a,'num_lowest_y_power':low,'negative_power':neg})
        if neg: break
    return out
def symbolic_check():
    ys=sp.symbols('y1:9'); ell={}
    for i in range(1,7):
        L=sp.Symbol('L'); P=lambda s: L if s==i else ell[s]
        rows=list(range(1,(i+1)//2+1)); cols=list(range(i//2+1,i+1))
        Mx=sp.Matrix(len(rows),len(cols),lambda a,b: (-P(cols[b]-rows[a]+1)) if cols[b]>=rows[a] else 0)
        t=sp.Integer(1)
        for k in range(1,i+1): t*=ys[k-1]**(i+1-k)
        ell[i]=sp.factor(sp.solve(sp.Eq(sp.expand(-Mx.det()),t),L)[0])
    return ell
if __name__=='__main__' and sys.argv[1]=='sym':
    e=symbolic_check(); [print(k,v) for k,v in e.items()]; sys.exit()
if __name__=='__main__':
    imax=int(sys.argv[1]); seed=int(sys.argv[3]); j=int(sys.argv[2])
    r=run(imax,j,seed,95)
    print(json.dumps({'imax':imax,'variable':j,'seed':seed,'reached':r[-1]['i'] if r else 0,'any_negative':any(x['negative_power'] for x in r),'rows':r}))
