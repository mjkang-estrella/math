from pathlib import Path
import hashlib,json,datetime
D=Path(__file__).resolve().parent; B=D.parent.parent; L=B/'lanes'; I=L/'root-mathdb-candidate-intake-r525'; P=L/'sol-mathdb-primary-qualified-breadth-r522'
out=[]
def bind(p, expected=None):
 p=Path(p); b=p.read_bytes(); r=dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
 if expected: assert all(r[k]==expected[k] for k in ('size','sha256')),str(p)
 out.append(r); return r
bind(I/'manifest.json'); m=json.loads((I/'manifest.json').read_text()); expected={x['path'] for x in m['files']}; actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(m['excluded_exact_paths']); assert expected==actual
for e in m['files']: bind(I/e['path'],e)
for e in json.loads((I/'bindings.json').read_text()):
 bind(e['original'],e); bind(e['copy'],e)
# Flat direct references only; no recursive manifest execution or history traversal.
for e in json.loads((P/'flat-bindings.json').read_text()):
 if any(t in e['path'] for t in ('r304/','r363/','records.json','source-provenance','derivative-bindings')): bind(e['path'],e)
for lane in ('root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363'):
 for p in (L/lane).iterdir():
  if p.is_file():bind(p)
for p in (B/'ledger.json', B/'prior-campaign-context.json'):bind(p)
(D/'flatbindings.json').write_text(json.dumps(out,indent=2)+'\n'); (D/'binding-receipt.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),intake_files=len(expected),bound=len(out),exact_payload=True,original_copy=True,upstream_executed=False),indent=2)+'\n')
print((D/'binding-receipt.json').read_text())
