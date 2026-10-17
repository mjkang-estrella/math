# Original exploratory comparison only; no author proof verification.
import numpy as np
from scipy.optimize import minimize
w=np.exp(2j*np.pi/3)
r=np.sort(np.roots([27,0,-66,8*np.sqrt(26-2*np.sqrt(97)),3]).real)
c=1/np.sqrt(1+r*r); s=r*c
v=[np.array([0,1,-w])/np.sqrt(2),np.array([0,1,-w*w])/np.sqrt(2)]
for j in range(4):
    p=2*c[0]*c[j]/3; q=c[0]*c[j]/3+s[0]*s[j]
    sig=0 if j==0 else np.arccos(np.clip((.25-p*p-q*q)/(2*p*q),-1,1))
    for sign in ([1] if j==0 else [1,-1]):
        v.append(np.array([np.sqrt(2/3)*c[j]*np.exp(1j*sign*sig),-c[j]/np.sqrt(6)-s[j]/np.sqrt(2),-c[j]/np.sqrt(6)+s[j]/np.sqrt(2)]))
v=np.array(v)
def vec(t):
    a=t[:3]+1j*t[3:];return a/np.linalg.norm(a)
def loss(t):return np.max(np.abs(v.conj()@vec(t))**2)
rng=np.random.default_rng(20261016)
best=None
for i in range(12):
    opt=minimize(loss,rng.normal(size=6),method='Nelder-Mead',options={'maxiter':10000,'xatol':1e-11,'fatol':1e-11})
    if best is None or opt.fun<best.fun:best=opt
print('roots',r)
print('correct_pairs',sum(abs(abs(np.vdot(v[i],v[j]))**2-.25)<1e-8 for i in range(9) for j in range(i)))
print('witness',vec(best.x),'scores',np.abs(v.conj()@vec(best.x))**2)
print('probe only: upper bound at witness',best.fun)
