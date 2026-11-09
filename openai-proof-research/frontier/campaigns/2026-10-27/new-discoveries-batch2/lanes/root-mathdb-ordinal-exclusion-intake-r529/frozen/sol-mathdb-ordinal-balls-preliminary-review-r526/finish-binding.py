from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent;L=D.parent;P=L/'sol-mathdb-primary-qualified-breadth-r522'
r=json.loads((D/'flatbindings.json').read_text())
def bind(p):
 b=p.read_bytes();e=dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest());r.append(e);return e
# Bind actual original corpus chunk before reading line; no copy of corpus.
x=next(x for x in json.loads((P/'records.json').read_text()) if x['mathdb_id']==366370)
p=Path(x['corpus_chunk']);bind(p)
rec=json.loads(p.read_text().splitlines()[x['corpus_line']-1]);assert rec==x['record']
assert hashlib.sha256(x['statement'].encode()).hexdigest()==x['statement_utf8_sha256']
assert hashlib.sha256(json.dumps(rec,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()==x['canonical_record_sha256']
(D/'target-record.json').write_text(json.dumps(x,indent=2)+'\n')
# Final bind relevant flat originals, including history/exclusion snapshots as bytes only.
for e in json.loads((P/'flat-bindings.json').read_text()):
 if any(k in e['path'] for k in ('root-mathdb-accepted-exclusions-r304/','root-mathdb-cayley-review-intake-r363/')):
  z=bind(Path(e['path']));assert all(z[k]==e[k] for k in ('sha256','size'))
(D/'flatbindings.json').write_text(json.dumps(r,indent=2)+'\n')
# Bind figure derivative now; timing deviation explicitly disclosed in review.
bind(D/'figure2-page.png')
(D/'figure-binding.json').write_text(json.dumps(r[-1],indent=2)+'\n')
print('Original corpus line and canonical hash PASS; direct bindings',len(r)-1)
