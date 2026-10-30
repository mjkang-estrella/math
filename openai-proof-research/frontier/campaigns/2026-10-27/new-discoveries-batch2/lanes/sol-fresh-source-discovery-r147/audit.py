import json,hashlib,datetime,gzip,re,math
from pathlib import Path
from fractions import Fraction as F
L=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
j=json.loads((L/'checks.json').read_text());unique={tuple(r['c']):r for d in j['degrees'] for r in d['candidates']}
verified=[]
for c,r in unique.items():
 # Recompute values using the forward-difference table, independently of comb.
 a=list(c);luc0,luc1=2,1;ok=True
 for n in range(r['finite_N']+1):
  lim=1 if n==0 else luc1-(n%2==0)
  if n:
   luc0,luc1=luc1,luc0+luc1
  if abs(a[0])>lim:ok=False
  a=[a[k]+(a[k+1] if k+1<len(a) else 0) for k in range(len(a))]
 C=sum((F(abs(x),math.factorial(k)) for k,x in enumerate(c)),F(0));N=r['finite_N'];d=len(c)-1
 tail=C*N**d<=F(3,2)**N and F(N+1,N)**d<=F(3,2)
 assert ok==r['finite_pass'] and tail==r['tail_pass']
 verified.append(dict(c=list(c),degree=d,global_pass=ok and tail))
save('independent-checks.json',dict(utc=now(),records=len(verified),all_pass=all(r['global_pass'] for r in verified),max_degree=max(r['degree'] for r in verified),verified=verified,scope='finite set of explicit polynomials, no infinite-family assertion'))
pat=re.compile(r'2508[.]17335|139140|Kiro|Nishry|IntegerValued.*Growth|GrowthConstraint|GoldenRatio',re.I)
rels=['root-edge-irregulator-final-freeze-r1/omega-tree.txt.gz','root-edge-irregulator-final-freeze-r1/openai-tree.txt.gz','sol-fresh-source-discovery-r138/sources/omega-compare.json','sol-fresh-source-discovery-r141/registry-delta.json']
regs=[]
for rel in rels:
 p=L.parent/rel;b=p.read_bytes();s=gzip.decompress(b).decode() if p.suffix=='.gz' else b.decode();hits=[line for line in s.splitlines() if pat.search(line)]
 regs.append(dict(path=str(p),sha256=sha(b),hits=hits,limit='lexical retained tree/returned comparison screen only; no omitted-delta or full-proof clearance'))
save('registry-screen.json',dict(utc=now(),records=regs,omega='490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c inherited23:50UTC',openai='7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a inherited unchanged',capped=['aa026->a19a300 paths','a19a->490f300 paths'],r140='only three named source-facing Markdown paths of first interval',current_proof_clearance=False))
print('verified unique',len(verified),'max degree',max(r['degree'] for r in verified),'registry hits',[len(r['hits']) for r in regs])
