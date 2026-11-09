from itertools import product,groupby
import json
from pathlib import Path
D=Path(__file__).resolve().parents[1]
out=[]
for n in range(1,15):
 best=2**n;minim=[];tested=0
 for q in product('01',repeat=n-1):
  w='0'+''.join(q)
  if w>w[::-1]: # partial reversal pruning; some equivalent representatives remain
   r=w[::-1];r=''.join(str(1-int(c)) for c in r) if r[0]=='1' else r
   if w>r:continue
  counts={'':1}
  for c in w:
   for s,v in list(counts.items()):counts[s+c]=counts.get(s+c,0)+v
  mx=max(counts.values());tested+=1
  if mx<best:best=mx;minim=[]
  if mx==best:
   runs=[len(list(g)) for _,g in groupby(w)]
   minim.append({'word':w,'longest_run':max(runs),'runs':len(runs),'ties':sum(v==mx for v in counts.values())})
 row={'n':n,'tested_first_letter_zero_words_after_partial_reversal_pruning':tested,'min_maxocc':best,'minimizers':minim};print(n,tested,best,len(minim),sorted(set(x['longest_run'] for x in minim)),sum(x['ties']>1 for x in minim),flush=True);out.append(row)
 (D/'outputs/words.json').write_text(json.dumps(out,indent=2)+'\n')
