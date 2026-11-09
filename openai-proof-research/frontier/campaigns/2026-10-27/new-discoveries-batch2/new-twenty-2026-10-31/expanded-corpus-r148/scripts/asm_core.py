import pathlib,json,sys,collections,time
L=pathlib.Path(__file__).resolve().parents[1]
def enumerate_poly(n,stop,target):
 dp={0:{(0,0):1}}
 for row in range(1,stop+1):
  nd={}
  for prev,poly in dp.items():
   trans=[]
   def rec(j,state,mask,neg):
    if j==n:
     if state==1 and (row!=stop or target is None or mask==target):trans.append((mask,neg))
     return
    p=prev>>j&1
    for b in [0,1]:
     s=state+b-p
     if s in [0,1]:rec(j+1,s,mask|(b<<j),neg+(p==1 and b==0))
   rec(0,0,0,0)
   for mask,w in trans:
    out=nd.setdefault(mask,collections.defaultdict(int));f=mask.bit_length() if row==1 else None
    for (z,oldf),c in poly.items():out[z+w,f if f is not None else oldf]+=c
  dp=nd;print('n',n,'row',row,'states',len(dp),'terms',sum(map(len,dp.values())),flush=True)
 return next(iter(dp.values()))
def mul(a,b):
 d=collections.defaultdict(int)
 for (x,y),v in a.items():
  for (z,w),u in b.items():d[x+z,y+w]+=v*u
 return dict(d)
def unref(a):
 d=collections.defaultdict(int)
 for (x,y),v in a.items():d[x,0]+=v
 return dict(d)
