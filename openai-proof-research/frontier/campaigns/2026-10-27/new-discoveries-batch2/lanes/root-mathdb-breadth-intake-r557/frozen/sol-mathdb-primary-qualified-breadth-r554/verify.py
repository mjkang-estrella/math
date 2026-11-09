#!/usr/bin/env python3
"""Read-only verification; run through the fixed helper guard. Nonzero on mismatch."""
import pathlib,json,hashlib,sys
P=pathlib.Path(sys.argv[1]).resolve() if len(sys.argv)>1 else pathlib.Path(__file__).resolve().parent
L=pathlib.Path(__file__).resolve().parent.parent;I=L/'root-mathdb-breadth-intake-r553';R=L/'pi-mathdb-full-corpus-inventory-r301'
def sha(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 p=pathlib.Path(p);assert not p.is_symlink(),f'symlink {p}'
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size mismatch {p}';assert sha(b)==e['sha256'],f'hash mismatch {p}'
def payload(root,manifest,excluded):
 assert manifest['excluded_exact_paths']==excluded,'exclusions'
 entries=manifest['files'];assert len(entries)==len({e['path'] for e in entries}),'duplicate payload entry'
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 assert actual=={e['path'] for e in entries}|set(excluded),f'exact payload mismatch {root}'
 for e in entries:check(root/e['path'],e)
payload(P,json.loads((P/'manifest.json').read_text()),['manifest.json','final-verification-receipt.json'])
refs=json.loads((P/'flat-bindings.json').read_text());assert len(refs)==len({e['path'] for e in refs})
for e in refs:check(e['path'],e)
payload(I,json.loads((I/'manifest.json').read_text()),['manifest.json','verification-receipt.json'])
for e in json.loads((I/'bindings.json').read_text()):check(e['original'],e);check(e['copy'],e)
rm=json.loads((R/'manifest.json').read_text());chunks=[e for e in rm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20
assert sha((R/'manifest.json').read_bytes())==sha((I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json').read_bytes())
for e in chunks:check(R/e['path'],e)
assert len(rm['frozen_inputs'])==8
for e in rm['frozen_inputs']:
 p=pathlib.Path(e.get('path',e.get('original')));check(p if p.is_absolute() else R/p,e)
coverage=json.loads((I/'coverage-delta.json').read_text());assert len(coverage)==4783
reserved=json.loads((I/'reserved-ids.json').read_text());queue=json.loads((I/'queue.json').read_text());ids=set(reserved['ids'])
assert len(reserved['ids'])==len(ids)==50 and ids=={e['mathdb_id'] for e in queue}
assert reserved['lane']=='sol-mathdb-primary-qualified-breadth-r554'
protected=set(reserved['protected_ids']);seen=set();sets=json.loads((I/'active-breadth-reservations.json').read_text())
for s in sets:
 a=set(s['ids']);assert len(a)==len(s['ids'])==50;assert not a&seen;assert not a&protected;assert not a&set(map(int,coverage));seen|=a
assert ids<=seen and not ids&set(reserved['other_active_reservations']) and not ids&protected
rows=json.loads((P/'assigned-records.json').read_text());ds=json.loads((P/'dispositions.json').read_text());assert len(rows)==len(ds)==50
assert {d['mathdb_id'] for d in ds}==ids and len({d['mathdb_id'] for d in ds})==50
found={}
for e in chunks:
 for lineno,line in enumerate((R/e['path']).open(),1):
  r=json.loads(line)
  if r['mathdb_id'] in ids:
   assert r['mathdb_id'] not in found;found[r['mathdb_id']]=(str(R/e['path']),lineno,r)
for d in ds:
 path,line,r=found[d['mathdb_id']];assert path==d['corpus_chunk'] and line==d['corpus_line'];assert r['statement']==d['statement'];assert sha(r['statement'].encode())==d['statement_utf8_sha256'];assert sha(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())==d['canonical_record_sha256'];assert d['accepted_credit']==0 and not d['current_registry_cleared']
for x in rows:assert found[x['record']['mathdb_id']]==(x['chunk'],x['line'],x['record'])
assert len(json.loads((P/'proposals.json').read_text()))<=3
for name in ['retrieval-bindings.json','derivative-bindings.json']:
 for e in json.loads((P/name).read_text()):
  if 'path' in e:check(P/e['path'],e)
for e in json.loads((P/'selected-passages.json').read_text()):assert (P/e['file']).read_text()[e['start']:e['start']+len(e['passage'])]==e['passage']
print(json.dumps({'integrity':'PASS','literal_reviews':50,'baseline':4783,'original_chunks':20,'frozen_inputs':8,'proposals':len(json.loads((P/'proposals.json').read_text())),'math_novelty':'NOT CLEARED','registry':'HOLD'}))
