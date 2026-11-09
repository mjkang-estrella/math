from pathlib import Path
import json,random,time
D=Path(__file__).resolve().parents[1];out=[]
for n in range(2,6):
 allowed=[x for x in range(1<<n) if x.bit_count()>=2];A=sum(1<<x for x in allowed);count=0;best=n; witness=None
 def rec(fam,forbid):
  global count,best,witness
  undecided=A&~(fam|forbid)
  if not undecided:
   if not fam:return
   count+=1;v=[x for x in allowed if fam>>x&1];ab=sum(2*sum(x>>e&1 for x in v)>len(v) for e in range(n))
   if ab<best:best=ab;witness=v
   return
  bit=undecided&-undecided;s=bit.bit_length()-1
  rec(fam,forbid|bit)
  nf=fam|bit
  for x in allowed:
   if fam>>x&1:nf|=1<<(s|x)
  if not nf&forbid:rec(nf,forbid)
 rec(0,0)
 row={'n':n,'all_union_closed_nonempty_families_min_set_size_2':count,'minimum_strictly_abundant':best,'minimum_example':witness};out.append(row);print(row,flush=True)
(D/'union-search.json').write_text(json.dumps(out,indent=2)+'\n')
