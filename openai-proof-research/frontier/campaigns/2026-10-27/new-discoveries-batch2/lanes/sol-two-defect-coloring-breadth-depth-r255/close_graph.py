import json,pathlib,time,collections,sys
from transfer import PERMS
L=pathlib.Path(__file__).parent;start=time.monotonic();CAP=int(sys.argv[1]) if len(sys.argv)>1 else 2
t=json.loads((L/'L-table.json').read_text());assert t['complete']
C=json.loads((L/'C-table.json').read_text())
maps=[]
for p in PERMS:
 maps.append({c*32+m:p[c]*32+sum(1<<p[i] for i in range(5) if m>>i&1) for c in range(5) for m in range(32) if m.bit_count()==3 and m>>c&1})
expanded={}
for i,r in enumerate(t['rows']):
 for j,mp in enumerate(maps):
  k=sum(mp[c*32+m]<<(8*a) for a,(c,m) in enumerate(r['state']));v=(r['cost']<<24)|(i<<7)|j
  if k not in expanded or v>>24<expanded[k]>>24:expanded[k]=v
idx={}
for ports in [(2,3),(0,1,2),(0,1,2,3)]:
 d=collections.defaultdict(list)
 for k,v in expanded.items():d[tuple(((k>>(8*i))&255)//32 for i in ports)].append(k)
 idx[ports]=d
print('expanded L',len(expanded),flush=True)
calls=0;found=None;complete=True
def opts(req,budget):
 global calls
 calls+=1
 if calls%500==0 and time.monotonic()-start>160:raise TimeoutError('160s close ceiling')
 ports=tuple(sorted(req));key=tuple(req[i]//32 for i in ports)
 for k in idx[ports].get(key,[]):
  base=expanded[k]>>24
  if base>budget:continue
  cost=base+sum((((k>>(8*i))&31)|(req[i]&31)).bit_count()==4 for i in ports)
  if cost<=budget:yield k,cost
def port(k,i):return (k>>(8*i))&255
try:
 for cr in C['rows']:
  s=[c*32+m for c,m in cr['state']];base=cr['cost']
  for a,da in opts({2:s[0],3:s[1]},CAP-base):
   for c,dc in opts({0:s[5],1:s[3],2:port(a,0)},CAP-base-da):
    for b,db in opts({0:s[2],1:port(a,1),2:s[4],3:port(c,3)},CAP-base-da-dc):
     found={'L_keys':[a,b,c],'L_witnesses':[expanded[k] for k in [a,b,c]],'claw':cr,'cost':base+da+dc+db};break
    if found:break
   if found:break
  if found:break
except TimeoutError as e:complete=False;print(str(e),flush=True)
out={'complete':complete,'cap':CAP,'expanded_L':len(expanded),'calls':calls,'witness':found,'seconds':time.monotonic()-start,'conclusion':'witness' if found else ('no coloring with <='+str(CAP)+' defects on this construction only' if complete else 'incomplete')}
(L/('G-result.json' if CAP==2 else 'G-zero-result.json')).write_text(json.dumps(out,indent=2));print(out,flush=True)
