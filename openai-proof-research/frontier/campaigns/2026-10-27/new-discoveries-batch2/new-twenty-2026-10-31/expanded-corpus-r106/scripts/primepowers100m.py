from math import isqrt
import json
N=100000000
s=bytearray(b'\1')*(isqrt(N)+1);s[:2]=b'\0\0'
for p in range(2,isqrt(len(s)-1)+1):
 if s[p]:s[p*p::p]=b'\0'*(((len(s)-1-p*p)//p)+1)
pps=[]
for p in range(len(s)):
 if s[p]:
  q=p*p
  while q<=N:pps.append(q);q*=p
pps=sorted(set(pps));print('N',N,'primepowers',len(pps),flush=True)
mask=(1<<(N+1))-1;cur=1;union=0
for m in range(1,6):
 nxt=0
 for q in pps:nxt|=(cur<<q)&mask
 cur=nxt
 if m>=2:union|=cur
 print('m',m,'reachable',cur.bit_count(),flush=True)
bad=((mask^union)>>24);count=bad.bit_count();first=[]
while bad and len(first)<100:
 t=bad&-bad;first.append(t.bit_length()-1+24);bad^=t
out={'N':N,'primepowers_count':len(pps),'summands':'2..5, repetition allowed','exceptions_n_gt_23_count':count,'first_exceptions':first}
open('outputs/primepowers100m.json','w').write(json.dumps(out,indent=2));print(out)
