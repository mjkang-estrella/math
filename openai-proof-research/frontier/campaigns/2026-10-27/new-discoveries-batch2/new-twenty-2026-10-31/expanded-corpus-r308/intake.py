import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import json,hashlib,subprocess,time,re
from pathlib import Path
P=Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
def save(n,x): (P/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
r=json.loads((P/'reservation.json').read_text()); ids=r['ids']; assert len(ids)==len(set(ids))==20
save('reservation-before.json',{'sha256':H((P/'reservation.json').read_bytes()),'expected':(P/'reservation.sha256').read_text().split()[0],'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())})
corpus=P.parents[1]/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus'
files=sorted(corpus.glob('mathdb-normalized-chunk-*.jsonl'))
out=[]; inv=[]
for f in files:
 b=f.read_bytes(); hits=[]
 for i,line in enumerate(b.splitlines(keepends=True),1):
  if not any(str(k).encode() in line for k in ids):continue
  x=json.loads(line)
  k=x.get('id',x.get('mathdb_id'))
  if int(k or 0) not in ids:continue
  (P/'literal').mkdir(exist_ok=True)
  (P/'literal'/f'{k}.jsonl').write_bytes(line)
  print('RECORD',k,json.dumps(x,ensure_ascii=False))
  statement=x.get('statement',x.get('content',''))
  out.append({'id':int(k),'original_chunk':str(f),'line_1based':i,'chunk_sha256':H(b),'raw_sha256':H(line),'raw_includes_newline':line.endswith(b'\n'),'statement_sha256':H((statement if isinstance(statement,str) else json.dumps(statement,ensure_ascii=False)).encode()),'parsed':x})
 inv.append({'path':str(f),'bytes':len(b),'sha256':H(b),'depth':'raw-line extraction; unrelated records not semantically reviewed'})
assert {x['id'] for x in out}==set(ids),(len(out),ids)
save('provenance.json',out); save('corpus-read-inventory.json',inv)
allow=json.loads((P/'historical-results-allowlist.json').read_text()); history=[]; matches=[]
terms=[str(k) for k in ids]+[x['source_url'].rsplit('/',1)[-1] for x in r['rows']]+['recovery balanced','paired coalition','unitary polar','subtraction game','Hibi','Grassmann']
for name in allow:
 f=Path(name)
 if any(z in str(f).lower() for z in ['crown','active']):continue
 if not f.is_file():history.append({'path':name,'missing':True});continue
 b=f.read_bytes(); text=b.decode(); hit=[t for t in terms if t.lower() in text.lower()]
 history.append({'path':name,'bytes':len(b),'sha256':H(b),'matched_terms':hit})
 if hit:
  for ln in text.splitlines():
   if any(t.lower() in ln.lower() for t in hit):matches.append({'path':name,'line':ln[:2400]})
save('history-read-inventory.json',history);save('history-matches.json',matches)
print('HISTORY',json.dumps(matches,ensure_ascii=False)[:15000])
