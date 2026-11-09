from pathlib import Path
import json
D=Path(__file__).resolve().parents[1]
def parts(n,m=None):
 if n==0:yield ();return
 for x in range(min(n,m or n),0,-1):
  for q in parts(n-x,x):yield (x,)+q
def wide(p):
 for mask in range(1,1<<len(p)):
  q=tuple(x for j,x in enumerate(p) if mask>>j&1)
  if any(sum(q[:k])<sum(min(k,x) for x in q) for k in range(1,len(q)+1)):return False
 return True
def latin(p):
 # Process smaller rows first, with exact backtracking over injective row assignments.
 col=[0]*max(p);rows=sorted(p)
 def place(r):
  if r==len(rows):return True
  m=rows[r];full=(1<<m)-1
  def fill(unfilled,used):
   if not unfilled:return place(r+1)
   j=min(unfilled,key=lambda j:(full&~used&~col[j]).bit_count());avail=full&~used&~col[j]
   rest=unfilled-{j}
   while avail:
    z=avail&-avail;avail-=z;col[j]|=z
    if fill(rest,used|z):return True
    col[j]^=z
   return False
  return fill(set(range(m)),0)
 return place(0)
res=[]
for n in range(1,19):
 total=wc=0
 for p in parts(n):
  total+=1
  if not wide(p):continue
  wc+=1;assert latin(p),p
 res.append({'area':n,'partitions':total,'wide':wc,'wide_without_latin':0});print(res[-1],flush=True)
(D/'outputs/tableaux.json').write_text(json.dumps(res,indent=2)+'\n')
