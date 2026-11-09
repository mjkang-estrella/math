"""Exact finite diagnostics and DFA reachability; not a literal formal certificate."""
import os,resource,itertools,json
from pathlib import Path
for key in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[key]='1'
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(25,25))
def step(states,letters,k):
 out=set()
 for last,run in states:
  for bit in letters:
   nr=run+1 if bit!=last else 1
   assert nr<2*k,(k,last,run,bit)
   out.add((bit,nr))
 return out
# All numbers of 11u blocks, all free bits, every suffix in the tail:
# longest alternating suffix DFA, with closure at block boundaries.
dfa=[]
for k in range(3,65):
 states={('',0)}; seen=set()
 while states!=seen:
  seen=set(states); t=step(step(states,'1',k),'1',k)
  for _ in range(k-2):t=step(t,'01',k)
  states|=t
 for _ in range(2*k+1):states=step(states,'1',k)
 dfa.append({'k':k,'reachable_states':len(seen)})
# Independent integer arithmetic: exact floor remainder and rearranged rational inequality.
n=[0]
for k in range(1,201):n.append(k*k*(n[-1]+k+10))
for k in range(3,201):
 H=n[k-1]+3; R=n[k]-2*k-2-H; B,r=divmod(R,k); D=n[k]-1-(k-2)*B
 assert R>=0 and 0<=D and r<k
 assert k*D<=2*n[k]+k*(n[k-1]+3*k+5)
 assert k*k*n[k-1]<=n[k]
# Membership looks at ALL possible anchors, including those beyond tested bush index.
def internal(w):
 if not w:return True
 if w[0]=='1':return False
 # Prefix-incomparability means the FIRST equal adjacent pair determines
 # the only possible anchor. This tests all anchors, without listing them.
 for t in range(1,len(w)):
  if w[t]==w[t-1]:
   j=(t-1)//2
   if w[t]=='0' and t%2==1 and j>=1:
    return len(w)<n[j] if j<len(n) else True
   return False
 return True
checked=0
for k in (3,4):
 H=n[k-1]+3;B,r=divmod(n[k]-(2*k+2)-H,k)
 for mode in range(4):
  free=['0'*(k-2),'1'*(k-2),('01'*k)[:k-2],('10'*k)[:k-2]][mode]
  w='01'*k+'00'+('11'+free)*B+'1'*(r+H)
  assert len(w)==n[k] and not internal(w) and internal(w[:-1])
  # Scan every suffix; each test checks every anchor allowed by its length.
  assert not any(internal(w[i:]) for i in range(1,len(w)))
  checked+=1
out={'status':'PASS','proof_certificate':False,'all_anchor_suffix_words':checked,'integer_cases':198,'dfa':dfa,'limits':{'address_bytes':536870912,'cpu_seconds':25,'threads':1}}
Path(__file__).with_name('independent-evidence.json').write_text(json.dumps(out,indent=2)); print(json.dumps({k:v for k,v in out.items() if k!='dfa'}))
