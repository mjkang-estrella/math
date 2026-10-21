"""Small bounded sufficient tests for q=1; failure is inconclusive."""
from diagnostic import *
from collections import defaultdict
from pathlib import Path

def peel(S,m,mode):
 remaining=set(S);lines=[]
 directions=[(0,1),(1,0),(1,1),(1,-1),(2,1),(2,-1),(1,2),(1,-2),(3,1),(3,-1),(1,3),(1,-3)]
 for cap in range(m,0,-1):
  candidates=[]
  for a,b in directions:
   bags=defaultdict(list)
   for j,k in remaining:bags[a*j+b*k].append((j,k))
   for c,pts in bags.items():
    n=len(pts)
    if (mode=='row' and n>=cap) or (mode=='column' and n<=cap):candidates.append((n,a,b,c,pts))
  if not candidates:return False,lines
  z=max(candidates);n,a,b,c,pts=z;remaining.difference_update(pts);lines.append([a,b,c,n])
  if not remaining:return mode=='column' or cap==1,lines
 return mode=='row',lines

if __name__=='__main__':
 records=[]
 # Only ten-point critical strip, 43<=m<=150; fixed 49 rational parameter choices, bounded directions.
 for m in range(43,151):
  for d in range(isqrt(10*m*m)+1,isqrt(10*(m+1)*(m+1))-2):
   chi=(d+2)*(d+1)//2-10*m*(m+1)//2;mode='row' if chi>=0 else 'column';win=None
   for z in range(1,50):
    delta=F(z,100);S=diagram(10,d,m,delta);ok,lines=peel(S,m,mode)
    if ok:win={'delta':str(delta),'lines':lines};break
   record={'r':10,'d':d,'m':m,'chi':chi,'mode':mode,'certificate':win};records.append(record)
   print('CASE',d,m,'chi',chi,'certificate',win['delta'] if win else None,flush=True)
 Path(__file__).resolve().parents[1].joinpath('scratch/line-peeling.json').write_text(json.dumps(records,indent=2))
