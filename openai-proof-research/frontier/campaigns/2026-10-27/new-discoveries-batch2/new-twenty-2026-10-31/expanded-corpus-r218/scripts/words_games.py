from pathlib import Path
import json,sys
from functools import lru_cache
D=Path(__file__).resolve().parents[1]
if sys.argv[1]=='words':
 out=[]
 def effective(n):q=2*((n+2)//4)+1;return n-q,q
 for n in range(8,int(sys.argv[2])+1):
  count=0;bad=[]
  for bits in range(1<<(n-1)): # complement symmetry fixes leading letter 0
   na=n-bits.bit_count();nb=n-na
   if min(na,nb)<4:continue
   i,k=effective(na);j,l=effective(nb)
   if k!=l:continue
   count+=1;lower=i//2+j//2;seen=set();pref=[0]
   for t in range(n):pref.append(pref[-1]+((bits>>t)&1))
   for h in range(1,n//2+1):
    for t in range(n-2*h+1):
     if pref[t+h]-pref[t]==pref[t+2*h]-pref[t+h]:seen.add((2*h,(bits>>t)&((1<<(2*h))-1)))
   if len(seen)<lower:bad.append({'bits':bits,'n':n,'count':len(seen),'bound':lower})
  row={'n':n,'complement_representatives':count,'violations':bad};out.append(row);print(json.dumps(row),flush=True)
  (D/'logs/words-results.json').write_text(json.dumps(out,indent=2))
else:
 out=[];chi=[1,0,-1,1,0,-1,0,1,-1,0]
 for n in range(1,int(sys.argv[2])+1):
  full=(1<<n)-1
  @lru_cache(None)
  def sg(bits):
   options=set();left=full^bits
   while left:
    b=left&-left;left^=b;t=bits|b
    if t&(t>>1)&(t>>2):continue
    options.add(sg(t))
   g=0
   while g in options:g+=1
   return g
  bad=[];known=[];checks=0
  for a in range(2,n-2):
   b=n-a-1
   if b<2 or chi[a%10]*chi[b%10]:continue
   checks+=1;g=sg(1<<a)
   if g<=1:
    z={'a':a,'b':b,'sg':g}
    (known if (a,b)==(4,4) else bad).append(z)
  row={'board_length':n,'nonregular_interior_boards':checks,'cached_positions':sg.cache_info().currsize,'listed_exceptions':known,'violations':bad};out.append(row);print(json.dumps(row),flush=True)
  (D/'logs/game-results.json').write_text(json.dumps(out,indent=2));sg.cache_clear()
