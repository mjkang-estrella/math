"""Bounded numerical diagnostics, not a proof or mathematical acceptance gate."""
import sys
sys.dont_write_bytecode = True
import json
import numpy as np

rng = np.random.default_rng(325201)
def adj(a): return a.conj().T
def root(a, exponent):
    w,v=np.linalg.eigh(a)
    return (v*(w**exponent))@adj(v)
def mob(c,y):
    i=np.eye(c.shape[0])
    return root(i-c@adj(c),-.5)@(y+c)@np.linalg.inv(i+adj(c)@y)@root(i-adj(c)@c,.5)
def norm(a): return np.linalg.norm(a,2)
worst_identity=0.
worst_inverse=0.
worst_clipping=0.
for _ in range(12):
    c=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3));c*=.71/norm(c)
    y=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3));y*=.93/norm(y)
    i=np.eye(3);dc=root(i-adj(c)@c,.5)
    m=mob(c,y)
    rhs=dc@np.linalg.inv(i+adj(y)@c)@(i-adj(y)@y)@np.linalg.inv(i+adj(c)@y)@dc
    worst_identity=max(worst_identity,norm(i-adj(m)@m-rhs))
    worst_inverse=max(worst_inverse,norm(mob(-c,m)-y))
    h=np.diag([1.,1.7,4.]);r=.8;s=root(h,.5)
    d=rng.normal(size=(3,3))+1j*rng.normal(size=(3,3));d*=r/norm(d)
    x=np.linalg.inv(s)@d@s
    j=np.diag(np.maximum(1,r*r*np.diag(h)));sj=root(j,.5)
    worst_clipping=max(worst_clipping,norm(sj@x@np.linalg.inv(sj)))
out={'seed':325201,'samples':12,'matrix_size':3,
     'largest_mobius_identity_residual':float(worst_identity),
     'largest_mobius_inverse_residual':float(worst_inverse),
     'largest_clipped_norm':float(worst_clipping),
     'scope':'Finite numerical diagnostics only. Algebraic proofs are in construction.md. Not independent review, formal verification, or acceptance.'}
print(json.dumps(out,indent=2))
assert worst_identity<1e-10 and worst_inverse<1e-10 and worst_clipping<=1+1e-10
