import json,hashlib,pathlib
D=pathlib.Path(__file__).resolve().parent; L=D.parent; B=L.parent; I=L/'root-mathdb-breadth-intake-r599'; R=L/'pi-mathdb-full-corpus-inventory-r301'
def desc(p):
 b=p.read_bytes();return {'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def check(p,e):
 a=desc(p);assert a['size']==e.get('size',e.get('bytes')) and a['sha256']==e['sha256'],str(p);return a
out=[]
for p in I.glob('*.json'):out.append(desc(p))
for p in I.glob('*.md'):out.append(desc(p))
m=json.loads((I/'manifest.json').read_text());assert set(x['path'] for x in m['files'])=={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])
for e in m['files']:out.append(check(I/e['path'],e))
for e in json.loads((I/'bindings.json').read_text()):
 for k in ['original','copy']:out.append(check(pathlib.Path(e[k]),e))
rm=json.loads((R/'manifest.json').read_text()); chunks=[e for e in rm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(rm['frozen_inputs'])==8
for e in chunks+rm['frozen_inputs']:out.append(check(R/e['path'],e))
for p in [B/'ledger.json',B/'prior-campaign-context.json',L/'root-mathdb-accepted-exclusions-r304/accepted-exclusions.json',L/'root-mathdb-accepted-exclusions-r304/historical-dispositions.json',L/'root-mathdb-cayley-review-intake-r363/DECISION.md',L/'sol-mathdb-primary-qualified-breadth-r578/failures.json',L/'sol-mathdb-primary-qualified-breadth-r542/failures.md',L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:out.append(desc(p))
(D/'flat-bindings.json').write_text(json.dumps(list({e['path']:e for e in out}.values()),indent=2)+'\n')
q=json.loads((I/'queue.json').read_text());res=json.loads((I/'reserved-ids.json').read_text());ids=set(res['ids']);assert len(ids)==50 and ids=={e['mathdb_id'] for e in q}
cov=json.loads((I/'coverage-delta.json').read_text());assert len(cov)==5933
protected={337963,338290,339564,372627,372628,368940,404067,364119,366370,365437,365439}; used=set(map(int,cov))|protected
for s in json.loads((I/'active-breadth-reservations.json').read_text()):
 if s['lane']==D.name:assert set(s['ids'])==ids;continue
 a=set(s['ids']);assert len(a)==50 and not a&used;used|=a
assert not ids&used
records=[]
for e in chunks:
 p=R/e['path']
 for n,line in enumerate(p.open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:records.append({'mathdb_id':r['mathdb_id'],'corpus_path':str(p),'line':n,'record':r,'statement_utf8_sha256':hashlib.sha256(r['statement'].encode()).hexdigest(),'canonical_record_sha256':hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()})
assert len(records)==50
(D/'literal-records.json').write_text(json.dumps(records,ensure_ascii=False,indent=2)+'\n')
print('PASS intake exact payload, direct pairs, 20 chunks, 8 frozen inputs; 5933 coverage, reservation disjointness; extracted 50')
