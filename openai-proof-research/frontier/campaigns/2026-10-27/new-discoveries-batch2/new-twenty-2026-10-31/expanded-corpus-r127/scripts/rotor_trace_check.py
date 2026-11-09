# Diagnostic (floating point): p(t)=Tr prod_{k<e} X_k(t), X_k=[[1+z,-z(1-t z^k)],[1-t z^k,0]] equals 2+q_e t^e
# for every primitive e-th root z; checked by evaluating at e+1 sample points and interpolating.
import numpy as np, math, json
res=[]
for e in range(1,31):
    qe=0 if e%2 else (2 if e%4==0 else -2); worst=0
    for s in range(1,e+1):
        if math.gcd(s,e)!=1: continue
        z=np.exp(2j*np.pi*s/e)
        ts=np.exp(2j*np.pi*np.arange(e+1)/(e+1))*0.7
        vals=[]
        for t in ts:
            P=np.eye(2,dtype=complex)
            for k in range(e):
                g=1-t*z**k; P=P@np.array([[1+z,-z*g],[g,0]])
            vals.append(np.trace(P))
        coef=np.fft.fft(np.array(vals))/(e+1)/ (0.7**np.arange(e+1))
        target=np.zeros(e+1,dtype=complex); target[0]+=2; target[e]+=qe
        worst=max(worst,float(np.max(np.abs(coef-target))))
    res.append((e,qe,worst))
print(json.dumps({'max_abs_error_by_e':res}))
