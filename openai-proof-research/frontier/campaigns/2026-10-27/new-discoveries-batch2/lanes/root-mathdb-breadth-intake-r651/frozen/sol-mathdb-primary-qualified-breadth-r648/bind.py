import pathlib,json,hashlib,re
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r647';C=L/'pi-mathdb-full-corpus-inventory-r301'
f=json.loads((P/'flat-bindings.json').read_text())
def bind(p,e=None):
 p=p.resolve();b=p.read_bytes();d={'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
 if e:assert d=={'size':e.get('size',e.get('bytes')),'sha256':e['sha256']},str(p)
 f[str(p)]=d;return b
m=json.loads(bind(C/'manifest.json'));cs=[e for e in m['files'] if e['path'].startswith('corpus/')];assert len(cs)==20 and len(m['frozen_inputs'])==8
for e in cs+m['frozen_inputs']:bind(C/e['path'],e)
r=json.loads((I/'reserved-ids-r648.json').read_text());ids=set(r['ids']);cov=json.loads((I/'coverage-delta.json').read_text());assert len(cov)==7083
seen=set()
for a in json.loads((I/'active-breadth-reservations.json').read_text()):
 s=set(a['ids']);assert len(s)==50 and not s&seen and not s&set(map(int,cov)) and not s&set(a['protected_ids']);seen|=s
assert ids=={q['mathdb_id'] for q in json.loads((I/'queue-r648.json').read_text())}
records=[]
for e in cs:
 p=C/e['path']
 for n,b in enumerate(p.open('rb'),1):
  mt=re.search(rb'"mathdb_id"\s*:\s*(\d+)',b)
  if mt and int(mt[1]) in ids:
   z=json.loads(b);records.append({'corpus_chunk':str(p.resolve()),'corpus_line':n,'record':z,'canonical_record_sha256':hashlib.sha256(json.dumps(z,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(records)==50
for p in [L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json']:
 bind(p)
(P/'flat-bindings.json').write_text(json.dumps(f,indent=2)+'\n');(P/'literal-records.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
for x in records:
 z=x['record'];print('\nID',z['mathdb_id'],json.dumps(z,ensure_ascii=False))
