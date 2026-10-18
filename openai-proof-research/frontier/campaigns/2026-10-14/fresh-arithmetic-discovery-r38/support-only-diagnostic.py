#!/usr/bin/env python3
"""MIT. Finite support-only quotient comparisons, not a uniform proof."""
import importlib.util,json,sys
from pathlib import Path
p=Path(__file__).parent
s=importlib.util.spec_from_file_location('q',p/'quotient-diagnostic.py');q=importlib.util.module_from_spec(s);s.loader.exec_module(q)
def main():
 rows=[]
 for m in range(3,7):
  n=m*(m+1)//2;nh=(m-2)*(m-1)//2;rho=tuple(range(m,0,-1))
  band=q.induce({x:1 for x in q.parts(nh)},{x:1 for x in q.parts(2*m-1) if len(x)<=4})
  bad=[]
  for lam in q.parts(n):
   if lam in [(n,),(1,)*n]:continue
   tr=q.transpose(lam);kd=max(q.kostka(lam,rho),q.kostka(tr,rho));b=max(band[lam],band[tr]);v=max(kd,b)
   if v<m-1:bad.append({'lambda':lam,'K':kd,'band':b,'bound':v})
  rows.append({'m':m,'bad':bad})
 return rows
if __name__=='__main__':print(json.dumps(main(),indent=2))
