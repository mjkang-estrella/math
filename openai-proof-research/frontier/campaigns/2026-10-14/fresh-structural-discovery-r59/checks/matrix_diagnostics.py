#!/usr/bin/env python3
"""MIT. Finite floating-point diagnostics; not universal proof or verification."""
import itertools, json, math
import numpy as np
from numpy.polynomial.hermite import hermgauss
rng=np.random.default_rng(1175901)
def norm(a):return float(np.linalg.norm(a,2))
def herm(a):return (a+a.conj().T)/2
def power(a,t):
 w,v=np.linalg.eigh(herm(a))
 return (v*np.maximum(w,0)**t)@v.conj().T
def pairs(items):
 if not items:yield [];return
 a=items[0]
 for k in range(1,len(items)):
  b=items[k]
  for rest in pairs(items[1:k]+items[k+1:]):yield [(a,b)]+rest
def tuple_matrices(m,d):
 a=[herm(rng.normal(size=(d,d))+1j*rng.normal(size=(d,d))) for _ in range(m)]
 c=math.sqrt(norm(sum(x@x for x in a)))
 return [x/c for x in a]
worst_pair=0.;worst_gaussian=0.;max_hermite_error=0.;cases=0;partition_cases=0
for m,d in [(2,2),(3,3),(3,5)]:
 x=tuple_matrices(m,d)
 for q in [1,2,3,4]:
  total=np.zeros((d,d),complex)
  for pp in pairs(list(range(2*q))):
   b=np.zeros((d,d),complex)
   for labels in itertools.product(range(m),repeat=q):
    word=[None]*(2*q)
    for label,(i,j) in zip(labels,pp):word[i]=word[j]=label
    prod=np.eye(d,dtype=complex)
    for j in word:prod=prod@x[j]
    b+=prod
   worst_pair=max(worst_pair,norm(b));assert norm(b)<=1+1e-10
   total+=b;partition_cases+=1
  count=math.prod(range(1,2*q,2))
  worst_gaussian=max(worst_gaussian,float(np.linalg.eigvalsh(herm(total))[-1])/count)
  nodes,weights=hermgauss(q+1);nodes*=math.sqrt(2);weights/=math.sqrt(math.pi)
  quad=np.zeros((d,d),complex)
  for idx in itertools.product(range(q+1),repeat=m):
   wt=math.prod(weights[j] for j in idx)
   g=sum(nodes[j]*x[k] for k,j in enumerate(idx))
   quad+=wt*np.linalg.matrix_power(g,2*q)
  err=norm(total-quad);max_hermite_error=max(max_hermite_error,err)
  assert err<1e-8 and np.linalg.eigvalsh(herm(total))[0]>-1e-9
  cases+=1
# Positive Gaussian dual pairing, using a finite quadrature law with exact
# first/second moments. This tests the algebra, not convergence of sign quadrature.
m,d=3,5;a=tuple_matrices(m,d)
nodes,weights=hermgauss(7);nodes*=math.sqrt(2);weights/=math.sqrt(math.pi)
x=[np.zeros((d,d),complex) for _ in range(m)];absavg=np.zeros((d,d),complex)
for idx in itertools.product(range(7),repeat=m):
 g=np.array([nodes[j] for j in idx]);wt=math.prod(weights[j] for j in idx)
 ag=sum(g[j]*a[j] for j in range(m));w,v=np.linalg.eigh(ag)
 sg=(v*np.sign(w))@v.conj().T
 for j in range(m):x[j]+=wt*g[j]*sg
 absavg+=wt*(v*np.abs(w))@v.conj().T
y=sum(a[j]@x[j] for j in range(m))
assert norm(y-absavg)<1e-11
assert norm(sum(xx@xx for xx in x))<=1+1e-11
# Nontrivial selector example: mostly small charts and two larger ones.
S,N,q=14,7,3
u=rng.normal(size=(S,N,m))/math.sqrt(m)
u[:2]*=8
z=[[sum(u[s,i,j]*x[j] for j in range(m)) for i in range(N)] for s in range(S)]
mom=[sum(np.linalg.matrix_power(zz,2*q) for zz in chart) for chart in z]
Q=[power(mm,1/q) for mm in mom]
bound=norm(power(sum(mom)/S,1/q));h=2*bound
proj=[]
for qq in Q:
 w,v=np.linalg.eigh(qq);proj.append((v*(w<=h))@v.conj().T)
slack=float(np.linalg.eigvalsh(herm(sum(proj)-S/2*np.eye(d)))[0])
assert slack>=-1e-9
max_cut=max(norm(z[s][i]@proj[s])**2/h for s in range(S) for i in range(N))
assert max_cut<=1+1e-9
assert np.trace(y@sum(proj)).real>=S/2*np.trace(y).real-1e-8
# Exact chart reconstructions from the pseudoinverse, and the trace ordering.
tmax=0.; trace_total=0j; recon_error=0.
for ss in range(S):
 pinv=np.linalg.pinv(u[ss])
 bb=[sum(pinv[j,i]*a[j] for j in range(m)) for i in range(N)]
 tmax=max(tmax,max(float(np.sum(np.linalg.svd(bi,compute_uv=False))) for bi in bb))
 for j in range(m):
  recon_error=max(recon_error,norm(sum(u[ss,i,j]*bb[i] for i in range(N))-a[j]))
 trace_total+=sum(np.trace(bb[i]@z[ss][i]@proj[ss]) for i in range(N))
assert recon_error<1e-10
assert abs(trace_total-np.trace(y@sum(proj)))<1e-9
assert np.trace(y).real<=2*N*tmax*math.sqrt(h)+1e-8
assert np.trace(-np.eye(d)@sum(proj)).real<S/2*np.trace(-np.eye(d)).real
# Control: dropping variance normalization invalidates the scalar bound q=1.
bad=np.array([[2.]])
assert float((bad@bad)[0,0])>1
print(json.dumps({'status':'PASS','seed':1175901,'wick_tuple_moment_cases':cases,
 'individual_pairing_cases':partition_cases,'max_pairing_norm':worst_pair,
 'max_even_moment_ratio':worst_gaussian,'max_hermite_replay_error':max_hermite_error,
 'positive_pairing_error':norm(y-absavg),'selector_projector_ranks':[int(round(np.trace(p).real)) for p in proj],
 'chart_reconstruction_error':recon_error,'trace_pairing_replay_error':abs(trace_total-np.trace(y@sum(proj))),'positivity_negative_control':'fails for Y=-I','selector_sum_slack':slack,'max_cutoff_ratio':max_cut,
 'variance_hypothesis_negative_control':'fails without variance normalization',
 'scope':'Finite floating-point algebra diagnostics only; no proof of full construction, asymptotics, or novelty.'},indent=2))
