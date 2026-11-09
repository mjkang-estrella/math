import pathlib,resource,os,time,itertools
from fractions import Fraction as Q
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));start=time.monotonic()
# P_{j,k}: interval [(k-1+(j-k)y)/n, (k+(j-k)y)/n].
def area(s):
 n=len(s);lines=[(s[j]-1,j+1-s[j]) for j in range(n)];cuts={Q(0),Q(1)}
 for a,b in lines:
  for c,d in lines:
   if b!=d:
    for offset in [-1,0,1]:
     t=Q(c-a+offset,b-d)
     if 0<t<1:cuts.add(t)
 def width(t):
  left=sorted(Q(a)+b*t for a,b in lines);end=left[0]+1;v=Q(1)
  for x in left[1:]:
   v+=min(Q(1),max(Q(0),x+1-end));end=max(end,x+1)
  return v/n
 cuts=sorted(cuts);return sum((b-a)*(width(a)+width(b))/2 for a,b in zip(cuts,cuts[1:]))
for n in range(1,8):
 best=Q(1);w=None;count=0
 for s in itertools.permutations(range(1,n+1)):
  if time.monotonic()-start>100:print('BUDGET STOP at',n,count,flush=True);raise SystemExit
  a=area(s);count+=1
  if a<best:best=a;w=s
 print(n,'min_area',str(best),'witness',w,'permutations',count,flush=True)
