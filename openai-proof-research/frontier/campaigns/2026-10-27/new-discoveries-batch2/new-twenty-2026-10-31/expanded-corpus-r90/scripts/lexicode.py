from itertools import combinations
from functools import reduce
from operator import xor
from math import comb
from pathlib import Path
import json
out=[]
for k in [2,4,8]:
 used=set();code=[];xorcode=[]
 for v in combinations(range(1,2*k+1),k-1):
  if reduce(xor,v,0)==0:xorcode.append(v)
  cores=list(combinations(v,k-2))
  if any(c in used for c in cores):continue
  code.append(v);used.update(cores)
 nonoverlap=next(((a,b) for i,a in enumerate(code) for b in code[i+1:] if not set(a)&set(b)),None)
 rec={'k':k,'vertices_exhausted':comb(2*k,k-1),'lexicode_count':len(code),'expected':comb(2*k,k)//(2*(k+1)),'nonoverlap':nonoverlap,'xor_zero_count':len(xorcode),'same_xor_code':code==xorcode,'first_difference':next((v for v in code if v not in set(xorcode)),None),'code':code}
 out.append(rec);print({a:b for a,b in rec.items() if a!='code'},flush=True)
Path('outputs/lexicode.json').write_text(json.dumps(out,indent=2)+'\n')
