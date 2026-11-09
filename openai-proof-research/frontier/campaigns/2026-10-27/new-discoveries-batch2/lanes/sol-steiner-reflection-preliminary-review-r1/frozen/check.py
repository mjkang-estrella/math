#!/usr/bin/env python3
import resource,signal,os,itertools,json,time
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(35,35));signal.alarm(45)
from fractions import Fraction as Q
start=time.monotonic()
n=30;m=n-1
# Actual edges of a star, vertex 0 the centre. Distance = cardinality of
# union of unique paths connecting the first tuple entry to the others.
def distance(t):
 edges=set()
 for v in t[1:]:
  u=t[0]
  if u!=v:
   if u:edges.add(u)
   if v:edges.add(v)
 return len(edges)
d=lambda s:2*s**3-26*s**2+32*s+30
L=lambda s:86*s**3-728*s**2+894*s+810
P=lambda s:29*d(s)+(s+29)**3*L(s)
# Independent direct contraction of the ORIGINAL four-index distance tensor.
# 15*A*x = s*J-15*x. For each of four distinct s, recover a cubic identity.
values={}
for s in [0,5,8,9]:
 x=[s+29]+[-1]*29;y=[s-15*v for v in x]
 out=[0]*n
 for t in itertools.product(range(n),repeat=4):
  i,j,k,l=t;out[i]+=distance(t)*x[j]*x[k]*y[l]
 assert 2*out[0]==29*d(s)
 assert all(2*v==L(s) for v in out[1:])
 values[str(s)]={'15g_center':out[0],'15g_leaf':out[1]}
assert d(5)==-210 and d(8)==-354
assert L(5)==-2170 and L(8)==5402
assert P(5)<0<P(8)
# Alternative exact negativity certificate: d''=12s-52>0 on [5,8],
# hence convexity bounds d by the negative chord. Exact chord gap factor:
# d - chord = 2*(s-5)*(s-8)*(s+0) [check coefficients via values].
# Indeed chord slope=-48, chord=30-48s.
for s in [Q(5),Q(11,2),Q(6),Q(7),Q(8)]:
 assert d(s)-(30-48*s)==2*s*(s-5)*(s-8)
# Direct rational negative quartic value, no inference to unsymmetric spectrum.
s=5;x=[34]+[-1]*29
g=[Q(29*d(s),30)]+[Q(L(s),30)]*29
quartic=sum(a*b for a,b in zip(x,g));assert quartic<0
result={'PASS':True,'n':n,'k':4,'direct_tensor_tuples':4*n**4,'cubic_unisolvence_points':list(values),'direct_values':values,'d_endpoints':[d(5),d(8)],'L_endpoints':[L(5),L(8)],'P_endpoints':[P(5),P(8)],'quartic_at_34_minus1':str(quartic),'seconds':time.monotonic()-start,'limits':{'AS_MiB':512,'CPU_s':35,'alarm_s':45},'interpretation':'exact identity checks; proof uses IVT and algebra, not finite positive checks'}
print(json.dumps(result,indent=2))
