"""Pure-integer, exact finite certificates for Davis Conjecture 3.1.

No SymPy and no floating point.  Coefficients use ascending degree order.
Running this writes 38 certificates and a receipt.  They remain computational
evidence until the literal finite polynomial checker is formalized in Lean.
"""
from math import comb, isqrt
from pathlib import Path
import json
from hashlib import sha256

def trim(a):
    while len(a)>1 and a[-1]==0: a.pop()
    return a

def add(a,b):
    return trim([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)
                 for i in range(max(len(a),len(b)))])

def scale(a,c): return trim([c*v for v in a])

def mul(a,b):
    r=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): r[i+j]+=x*y
    return trim(r)

def monic_div(a,b):
    assert b[-1]==1
    r=a[:];q=[0]*(len(a)-len(b)+1)
    for i in range(len(q)-1,-1,-1):
        q[i]=r[i+len(b)-1]
        for j,v in enumerate(b):r[i+j]-=q[i]*v
    assert all(v==0 for v in r)
    return trim(q)

def falling_polynomials(n):
    fs=[[1]]
    for i in range(n):fs.append(mul(fs[-1],[-i,1]))
    return fs

def scaled_P(n,fs):
    out=[0]
    for i in range(n+1):
        out=add(out,scale(mul(mul(fs[i],fs[i]),mul(fs[n-i],fs[n-i])),comb(n,i)))
    return out

def shifted_integral_coefficients(a,m,q):
    # q^degree f(y+m/q); every coefficient is an integer.
    N=len(a)-1
    return [sum(a[j]*comb(j,i)*m**(j-i)*q**(N-j+i) for j in range(i,N+1))
            for i in range(N+1)]

def main():
    fs=falling_polynomials(43)
    rows=[]
    sd=scaled_P(5,fs)
    for d in range(5,43):
        sn=scaled_P(d+1,fs)
        # 200(d+1)d! times the source's cross-multiplied difference.
        q=[d*(d+1)//2,-2*d,2]
        H=add(mul(add(scale(mul([d-2,2],q),200),[-199*(d+1)*(d-2)]),sd),
              scale(mul([d-2,2],sn),-200))
        common=mul(fs[(d+1)//2],fs[(d+1)//2])
        reduced=monic_div(H,common)
        den=2000
        m=1000*d+isqrt((d+2)*10**6)
        assert (m-1000*d)**2 <= (d+2)*10**6
        coeffs=shifted_integral_coefficients(reduced,m,den)
        assert all(c>0 for c in coeffs),d
        rows.append(dict(d=d,threshold_numerator=m,threshold_denominator=den,
                         common_falling_index=(d+1)//2,degree=len(reduced)-1,
                         reduced_coefficients=reduced,
                         shifted_scaled_coefficients=coeffs))
        sd=sn
    out=Path(__file__).with_name('certificates.json')
    out.write_text(json.dumps(rows,indent=2)+'\n')
    receipt=dict(cases=len(rows),all_coefficients_strictly_positive=True,
                 coefficient_count=sum(len(r['shifted_scaled_coefficients']) for r in rows),
                 sha256=sha256(out.read_bytes()).hexdigest(),discovery_credit=0,
                 formal_status='finite certificates not yet replayed in Lean')
    Path(__file__).with_name('certificate-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt))

if __name__=='__main__':main()
