#!/usr/bin/env python3
"""Exact finite algebra plus labeled synthetic floats; no entropy computation."""
from fractions import Fraction as Q
import json, math
N=0
def check(x):
 global N
 N+=1
 if not x: raise AssertionError(N)
def mm(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def eye(n):return [[Q(i==j) for j in range(n)] for i in range(n)]
def inv(a):
 n=len(a);b=[list(map(Q,r))+e for r,e in zip(a,eye(n))]
 for i in range(n):
  p=next((p for p in range(i,n) if b[p][i]),None)
  if p is None:raise ValueError('singular Dirichlet matrix')
  b[i],b[p]=b[p],b[i];v=b[i][i];b[i]=[x/v for x in b[i]]
  for j in range(n):
   if i!=j:
    v=b[j][i];b[j]=[x-v*y for x,y in zip(b[j],b[i])]
 return [r[n:] for r in b]
def A(v):return [[Q(v),Q(-1)],[Q(1),Q(0)]]
def det2(a):return a[0][0]*a[1][1]-a[0][1]*a[1][0]

def main():
 greens=[]; periodic=[]; thresholds=[]
 for n in range(1,15):
  for mode in range(6):
   v=[Q((3+(i+mode)%7)*(-1 if (i*mode)%3==1 else 1)) for i in range(n)]
   w=[Q((-1)**i*(i+2),i+1) for i in range(n)]
   D=[[v[i] if i==j else Q(-1) if abs(i-j)==1 else Q(0) for j in range(n)] for i in range(n)]
   G=inv(D);check(mm(D,G)==eye(n))
   U=[row[0] for row in G]; t=[Q(1)];prev=Q(0)
   for x in v:prev,tnew=t[-1],x*t[-1]-prev;t.append(tnew)
   for i in range(n):
    check(v[i]*U[i]-(Q(1) if i==0 else U[i-1])-(Q(0) if i==n-1 else U[i+1])==0)
    for j in range(n):check(G[i][j]==t[min(i,j)]*U[max(i,j)])
   force=[-w[i]*U[i]**2 for i in range(n)]
   second=[sum(G[i][j]*force[j] for j in range(n)) for i in range(n)]
   check(second[0]==-sum(w[i]*U[i]**3 for i in range(n)))
   check(sum(G[i][i]*w[i]*U[i] for i in range(n))==sum(t[i]*w[i]*U[i]**2 for i in range(n)))
   if mode==0 and n in [1,2,5,14]:greens.append({'length':n,'curvature':str(second[0]),'kind':'exact rational varied-Dirichlet identity'})
 for L in [3,5,10,100]:
  for m in [1,2,3,5,8,12]:
   T=eye(2)
   for _ in range(2*m):T=mm(A(L),T)
   P,Qminus=T[0][0],-T[0][1]; b=2*Qminus/P;B=mm(A(b),T)
   check(det2(B)==1);check(B[0][0]+B[1][1]==0);check(mm(B,B)==[[-Q(1),Q(0)],[Q(0),-Q(1)]])
   wrong=mm(A(b+Q(1,1000)),T);check(wrong[0][0]+wrong[1][1]!=0)
   periodic.append({'L':L,'m':m,'b':str(b)})
 for j in [2,3,4,8,16,32,64,128,256,512,1024]:
  ell=Q(j**4);d=Q(1,j**2);theta=Q(1,j**3);u=Q(1,j**4);n0=1<<(j**8-1).bit_length()
  check(theta*theta==d/ell);check(d/theta==j);check(u/theta==Q(1,j));check(theta*n0>=j**5)
  a=0
  while min(d,u*2**a)<=theta:a+=1
  eps=min(d,u*2**a);check(theta<eps<=2*theta)
  for m in range(-4,5):
   initial=min(d,u*Q(2)**m);terminal=min(d,u*Q(2)**(a+m))
   check(initial/eps<=Q(2)**max(0,m)/j)
   check(terminal/eps<=Q(2)**max(0,m))
  thresholds.append({'j':j,'ell':str(ell),'B':str(d*ell),'theta':str(theta),'initial_to_theta':str(u/theta),'theta_times_n0':str(theta*n0),'crossing_dyadic_index':a})
 # Exact exponent and fixed observation-complexity bookkeeping.
 check(Q(1,4)+Q(1,8)-1==-Q(5,8))
 check(1-3*Q(4,5)==-Q(7,5))
 check(Q(1,50)-2*Q(49,50)*2<-3)
 check(4/(1-Q(49,50))==200)
 check(1-2*Q(1,11)>=Q(4,5))
 try:inv([[Q(0)]])
 except ValueError:check(True)
 else:check(False)
 # Synthetic losses B = sqrt(ell), log(ell), log(log(ell)); no map values.
 floats=[]
 for ell in [100.,10000.,1000000.]:
  for label,B in [('sqrt',math.sqrt(ell)),('log',math.log(ell)),('loglog',math.log(math.log(ell)))]:
   theta=math.sqrt(B)/ell
   floats.append({'ell':ell,'hypothetical_B':B,'case':label,'theta':theta,'seed_over_theta':1/math.sqrt(B),'theta_over_d':1/math.sqrt(B)})
 return {'scope':'finite algebra and synthetic scaling, not analytic proof certification or standard-map entropy evidence','exact_assertions':N,'green_examples':greens,'rational_periodic_cocycles':periodic,'exact_hypothetical_crossings':thresholds,'floating_diagnostics':{'kind':'hypothetical deficit sequences; no standard-map trajectories','rows':floats},'negative_controls':['critical 1x1 Dirichlet matrix is singular','perturbed cancellation coefficient has nonzero trace']}
if __name__=='__main__':print(json.dumps(main(),indent=2,sort_keys=True))
