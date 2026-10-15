"""Finite affine-array relaxation; floating results are diagnostics, not proofs."""
import argparse,itertools,json,math,time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix,vstack
p=argparse.ArgumentParser();p.add_argument('--A',type=int,default=3);p.add_argument('--K',type=int,default=4);p.add_argument('--pattern',type=str,default=None);args=p.parse_args();A,K=args.A,args.K

def liouville(n):
 s=1;p=2
 while p*p<=n:
  while n%p==0:n//=p;s=-s
  p+=1
 return -s if n>1 else s
forms=sorted({(a//math.gcd(a,b),b//math.gcd(a,b)) for a in range(1,A+1) for b in range(a*K+1)})
ix={f:i for i,f in enumerate(forms)};m=len(forms)
if m>25:raise ValueError('More than 25 sign variables; change finite grid, not proof scope.')
# Bit zero is fixed at 0 (+1); each column represents the symmetric pair {w,-w}.
codes=np.arange(1<<(m-1),dtype=np.uint32)<<1
signs=1-2*((codes[:,None]>>np.arange(m,dtype=np.uint32))&1).astype(np.int8)
reflect=[ix[(a,a*K-b)] for a,b in forms]
rc=np.sum(((signs[:,reflect]<0).astype(np.uint32))<<np.arange(m,dtype=np.uint32),axis=1,dtype=np.uint32)
mask=(1<<m)-1
rc=np.where(rc&1,rc^mask,rc)
canon=codes<=rc
codes=codes[canon];signs=signs[canon];rc=rc[canon]
rsigns=1-2*((rc[:,None]>>np.arange(m,dtype=np.uint32))&1).astype(np.int8)
low=[f for f in forms if f[1]<=f[0]*(K-1)]
li=[ix[f] for f in low];si=[ix[(a,b+a)] for a,b in low]
def quotient(v,ii):
 w=v[:,ii];bits=(w*w[:,ii.index(0)][:,None]<0) if 0 in ii else (w*w[:,0][:,None]<0)
 return np.sum(bits.astype(np.uint32)<<np.arange(len(ii),dtype=np.uint32),axis=1,dtype=np.uint32)
# Normalize each projected vector by its own first sign, independently on each side.
def project(v,ii):
 w=v[:,ii];return np.sum((w*w[:,0,None]<0).astype(np.uint32)<<np.arange(len(ii),dtype=np.uint32),axis=1,dtype=np.uint32)
blocks=[]
for a in range(1,A+1):
 for b in range(a*K-3):
  js=[];ss=[]
  for j in range(5):
   d=math.gcd(a,b+j);js.append(ix[(a//d,(b+j)//d)]);ss.append(liouville(d))
  blocks.append((js,np.array(ss,dtype=np.int8)))
def orbit(e):return {e,tuple(-x for x in e),e[::-1],tuple(-x for x in e[::-1])}
patterns=[];seen=set()
for e in itertools.product((-1,1),repeat=5):
 if e not in seen:patterns.append(e);seen.update(orbit(e))
if args.pattern:patterns=[tuple(1 if c=='+' else -1 for c in args.pattern)]
results=[]
for e in patterns:
 t=time.time();allowed=np.ones(len(codes),dtype=bool)
 forbidden=orbit(e)
 for js,sg in blocks:
  vals=signs[:,js]*sg
  for f in forbidden:allowed &= ~np.all(vals==f,axis=1)
 keep=np.flatnonzero(allowed);v=signs[keep];rv=rsigns[keep];N=len(keep)
 if not N:
  results.append({'pattern':''.join('+' if x>0 else '-' for x in e),'states':0,'status':2,'message':'empty support'});continue
 rr=[];cc=[];dd=[];r=0
 for i in range(m):
  for j in range(i+1,m):
   vals=(v[:,i]*v[:,j]+rv[:,i]*rv[:,j]).astype(np.int8)
   nz=np.flatnonzero(vals);rr.extend([r]*len(nz));cc.extend(nz.tolist());dd.extend(vals[nz].tolist());r+=1
 projs=[project(v,li),project(v,si),project(rv,li),project(rv,si)]
 rowdict={}
 for col in range(N):
  for code,sgn in [(projs[0][col],1),(projs[1][col],-1),(projs[2][col],1),(projs[3][col],-1)]:
   key=int(code)
   if key not in rowdict:rowdict[key]=r;r+=1
   rr.append(rowdict[key]);cc.append(col);dd.append(sgn)
 for col in range(N):rr.append(r);cc.append(col);dd.append(1)
 mat=coo_matrix((dd,(rr,cc)),shape=(r+1,N),dtype=float).tocsr();rhs=np.zeros(r+1);rhs[-1]=1
 res=linprog(np.zeros(N),A_eq=mat,b_eq=rhs,bounds=(0,None),method='highs')
 row={'pattern':''.join('+' if x>0 else '-' for x in e),'states':N,'variables':m,'equalities':r+1,'status':int(res.status),'message':res.message,'seconds':time.time()-t}
 if res.x is not None:row.update({'positive_weights':int(np.sum(res.x>1e-9)),'max_equality_residual':float(np.max(np.abs(mat@res.x-rhs)))})
 results.append(row);print(json.dumps(row),flush=True)
out={'A':A,'K':K,'forms':forms,'primitive_variables':m,'constraints':['zero missing pattern and its sign/reversal orbit at every grid consecutive block','exact content-factor identifications lambda(dL)=lambda(d)lambda(L)','all cross-slope primitive-pair correlations zero','global sign symmetry (all odd affine moments)','full joint affine-array base-shift stationarity','full joint intercept reflection at center K/2'],'status':'finite floating LP only; no infinite model, certificate or D1 proof','results':results}
suffix=f'A{A}-K{K}'+('-'+args.pattern if args.pattern else '')
Path(__file__).with_name('lp-'+suffix+'.json').write_text(json.dumps(out,indent=2)+'\n')
