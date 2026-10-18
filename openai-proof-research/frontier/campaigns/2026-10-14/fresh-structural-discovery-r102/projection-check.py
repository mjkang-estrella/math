#!/usr/bin/env python3
"""Seeded finite algebra diagnostics, not a proof or source verification."""
import itertools,json,numpy as np
rng=np.random.default_rng(1022026); count=0
norm=lambda x:float(np.sum(x*x))
def gram(t):return np.einsum('rij,rkj->ik',t,t)
def sym(t):return sum(t.transpose(p) for p in itertools.permutations(range(3)))/6
def project(t,p):return np.einsum('ai,bj,ck,ijk->abc',p,p,p,t)
def comm(t):return sum(norm(a@b-b@a) for a in t for b in t)
for n in range(1,9):
 for scale in [.03,.3,1.,3.]:
  t=sym(rng.normal(size=(n,n,n)))*scale
  b=gram(t); beta2=norm(b-np.eye(n)); w,v=np.linalg.eigh(b)
  good=(w>=.5)&(w<=1.5); p=v[:,good].T; s=project(t,p)
  lifted=project(s,p.T); qrank=n-int(good.sum())
  assert qrank<=4*beta2+1e-8
  assert norm(t-lifted)<=18*beta2+1e-8
  bs=gram(s); eye=np.eye(len(s))
  assert norm(bs-eye)<=36*beta2+1e-8
  assert np.sqrt(comm(s))<=np.sqrt(comm(t))+6*np.sqrt(beta2)+1e-8
  if len(s):assert np.linalg.eigvalsh(bs).max()<=1.5+1e-8
  count+=5
  # Three-mode clipping, including zero spectral values through explicit branch.
  factors=np.minimum(1.,2/np.sqrt(np.maximum(w,1e-300)))
  h=(v*factors)@v.T; clipped=project(t,h)
  assert np.linalg.eigvalsh(gram(clipped)).max()<=4+1e-7
  assert norm(t-clipped)<=9*np.sum(np.maximum(np.sqrt(np.maximum(w,0))-2,0)**2)+1e-7
  count+=2
# The Loewner replacement MUST retain the noncommuting congruence H.
nmat=np.diag([.2,.8]); erow=np.array([[1.,1.],[1.,1.]])
wrong=25*erow-np.linalg.inv(nmat)@erow@np.linalg.inv(nmat)
assert np.linalg.eigvalsh(wrong).min()<-.01
print(json.dumps({'status':'PASS','seed':1022026,'finite_assertions':count,'reason_checked_control':'Naive c^-2 Erow congruence replacement is not PSD for noncommuting Erow.','limits':'Floating finite algebra only; no density construction, global rounding, entropy proof, or upstream replay.'},indent=2))
