import os,resource,json,hashlib,zipfile,time
from pathlib import Path
from functools import lru_cache
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(20,20));resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
t=time.monotonic()
@lru_cache(None)
def gb(n,k):
 if k<0 or k>n:return 0
 if k==0:return 1
 return gb(n-1,k-1)+4**k*gb(n-1,k)
# Recurrence, not author's rational product implementation.
rows=[]
for i in range(5):
 terms=[]
 for h in range(max(i-2,0),min(2,i)+1):
  a=i-h;b=2-a
  terms.append((-1)**a*4**(a*(a-1)//2+b*(b-1)//2)*8**b*gb(4-i,2-h)*gb(i,h))
 rows.append(dict(i=i,terms=terms,value=sum(terms)))
# Separate coefficient multiplication, independent loop.
cols=[]
for i in range(5):
 p=[1]
 for a in [8*4**s for s in range(4-i)]+[-4**s for s in range(i)]:
  p=[(p[k] if k<len(p) else 0)+(a*p[k-1] if k else 0) for k in range(len(p)+1)]
 cols.append(p[2])
assert cols==[r['value'] for r in rows]==[91392,5208,60,-84,1428]
assert abs(cols[2])<abs(cols[3]);assert all(abs(cols[2])<abs(v) for i,v in enumerate(cols) if i!=2)
packet=Path('../fresh-corpus-r17/formula-only-packet.zip');manifest=json.loads(Path('../fresh-corpus-r17/packet-manifest.json').read_text()); members=[]
with zipfile.ZipFile(packet) as z:
 for n in z.namelist():
  b=z.read(n);h=hashlib.sha256(b).hexdigest(); members.append(dict(name=n,sha256=h,expected=(manifest.get(n) if n!='packet-manifest.json' else hashlib.sha256(Path('../fresh-corpus-r17/packet-manifest.json').read_bytes()).hexdigest()),match=(manifest.get(n)==h if n!='packet-manifest.json' else hashlib.sha256(Path('../fresh-corpus-r17/packet-manifest.json').read_bytes()).hexdigest()==h)))
  dest=Path('packet')/n
  assert dest.resolve().is_relative_to(Path('packet').resolve())
  dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
r=dict(rows=rows,polynomial_coefficients=cols,minimum=2,predicted=3,affinity=sorted(os.sched_getaffinity(0)),cpu_limit_s=20,address_space_MiB=512,wall_s=time.monotonic()-t,packet_members=members)
Path('independent-check.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
