from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parent; L=R.parent; I=L/'root-mathdb-breadth-intake-r395'; C=L/'pi-mathdb-full-corpus-inventory-r301'
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def check(p,e):assert p.stat().st_size==e.get('size',e.get('bytes')) and digest(p)==e['sha256'],str(p)
paths=set()
for e in json.loads((I/'manifest.json').read_text())['files']:
 p=I/e['path'];check(p,e);paths.add(p)
paths.add(I/'manifest.json');paths.add(I/'verification-receipt.json')
for e in json.loads((I/'bindings.json').read_text()):
 p=Path(e['original']);check(p,e);paths.add(p)
for e in json.loads((L/'sol-mathdb-primary-qualified-breadth-r392/input-bindings.json').read_text())['refs']:
 p=Path(e['path']);check(p,e);paths.add(p)
chunks=[e for e in json.loads((C/'manifest.json').read_text())['files'] if e['path'].startswith('corpus/')]
assert len(chunks)==20
for e in chunks:p=C/e['path'];check(p,e);paths.add(p)
paths.add(C/'manifest.json')
for n in ['root-mathdb-accepted-exclusions-r304','root-mathdb-cayley-review-intake-r363']:
 D=L/n
 for p in D.iterdir():
  if p.is_file():paths.add(p)
 if (D/'bindings.json').exists():
  for e in json.loads((D/'bindings.json').read_text()):
   p=Path(e['original']);paths.add(p)
base=L.parent
for p in [base/'AGENTS.md',base/'ledger.json',base/'prior-campaign-context.json']:paths.add(p)
refs=[{'path':str(p),'size':p.stat().st_size,'sha256':digest(p)} for p in sorted(paths)]
reservation=json.loads((I/'reserved-ids.json').read_text());coverage=json.loads((I/'coverage-delta.json').read_text());queue=json.loads((I/'queue.json').read_text())
a=set(map(str,reservation['ids']));b=set(map(str,reservation['other_active_reservations']))
assert reservation['lane']==R.name and len(a)==len(b)==50 and len(coverage)==1283
assert not a&b and not a&set(coverage) and not a&{'372627','372628','368940'}
assert a==set(str(x['mathdb_id']) for x in queue)
out=R/'input-bindings.json';assert not out.exists()
out.write_text(json.dumps({'frozen_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'mode':'flat immutable references, originals in place; no corpus/history copies','root_manifest_read_only_verified':True,'corpus_chunks_verified_before_content':20,'refs':refs},indent=2)+'\n');out.chmod(0o444)
print('FROZEN',len(refs),'refs; 20 chunks verified; 50 assigned, disjoint from 1283 reviewed, 50 active and focused IDs')
