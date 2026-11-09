"""Independent read-only verifier. No imports or execution of upstream helper code."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r713';C=L/'pi-mathdb-full-corpus-inventory-r301'
def j(p):return json.loads(p.read_bytes())
def digest(b):return hashlib.sha256(b).hexdigest()
def check(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'SIZE {p}';assert digest(b)==e['sha256'],f'HASH {p}'
def main():
 m=j(P/'manifest.json');excluded={'manifest.json','final-verification-receipt.json'};assert set(m['excluded_exact_paths'])==excluded
 entries={e['path']:e for e in m['files']};assert len(entries)==len(m['files'])
 actual={str(p.relative_to(P)):p.read_bytes() for p in P.rglob('*') if p.is_file() and str(p.relative_to(P)) not in excluded}
 inject=sys.argv[2] if len(sys.argv)==3 and sys.argv[1]=='--inject' else None
 if inject=='hash':
  b=actual['SUMMARY.md'];actual['SUMMARY.md']=bytes([b[0]^1])+b[1:]
 elif inject=='size':actual['SUMMARY.md']+=b'!'
 elif inject=='extra':actual['UNMANIFESTED.test']=b'fault'
 assert set(actual)==set(entries),'EXTRA/MISSING payload'
 for n,b in actual.items():
  assert len(b)==entries[n]['size'],f'SIZE {n}'
  assert digest(b)==entries[n]['sha256'],f'HASH {n}'
 refs=j(P/'flat-bindings.json')
 for e in refs:check(pathlib.Path(e['path']),e)
 im=j(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={e['path'] for e in im['files']}|set(im['excluded_exact_paths'])
 for e in im['files']:check(I/e['path'],e)
 pairs=j(I/'bindings.json')
 for e in pairs:
  check(pathlib.Path(e['original']),e);check(pathlib.Path(e['copy']),e)
 cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];assert len(chunks)==20 and len(cm['frozen_inputs'])==8
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');assert len(cov)==8733
 reservations=j(I/'active-breadth-reservations.json');assert len(reservations)==3
 assert {r['lane'] for r in reservations}=={'claude-mathdb-primary-qualified-breadth-r628','sol-mathdb-primary-qualified-breadth-r712',P.name}
 seen=set()
 for r in reservations:
  ids=set(r['ids']);assert len(ids)==50 and not ids&seen and not ids&set(map(int,cov)) and not ids&set(r['protected_ids']);seen|=ids
 mine=next(r for r in reservations if r['lane']==P.name);res=j(I/'reserved-ids-r714.json');assert all(res[k]==mine[k] for k in ['ids','protected_ids','coverage_baseline','active_hypothesis_ids','lane','status'])
 q=j(I/'queue-r714.json');ids=[x['mathdb_id'] for x in q];assert len(ids)==50 and ids==res['ids']
 records=j(P/'literal-records.json');dispositions=j(P/'dispositions.json');assert len(records)==len(dispositions)==50
 assert {x['id'] for x in records}=={d['mathdb_id'] for d in dispositions}==set(ids)
 found={}
 for e in chunks:
  with (C/e['path']).open('rb') as f:
   for line_no,b in enumerate(f,1):
    r=json.loads(b)
    if r.get('mathdb_id') in ids:
     k=r['mathdb_id'];assert k not in found;found[k]=(e['path'],line_no,b,r)
 assert set(found)==set(ids)
 for x in records:
  chunk,line,b,r=found[x['id']];assert x['record']==r and x['chunk']==chunk and x['line']==line
  canonical=digest(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
  assert x['canonical_sha256']==canonical and x['literal_line_sha256']==digest(b)
  d=next(d for d in dispositions if d['mathdb_id']==x['id'])
  assert d['statement']==r['statement'] and d['statement_utf8_sha256']==digest(r['statement'].encode())
  assert d['canonical_record_sha256']==canonical and d['literal_line_sha256']==digest(b) and d['corpus_chunk']==chunk and d['corpus_line']==line
  assert d['classification'] in ['complete','definition-dependent','scope-ambiguous','incomplete']
  for field in ['classification_reason','quantifiers','technical_assessment','disposition','remaining_obligations']:assert d[field]
  assert d['accepted_credit']==0 and d['novelty_cleared'] is False
 assert len(j(P/'proposals.json'))<=3
 for e in j(P/'source-provenance.json'):
  for suffix,key in [('pdf','pdf'),('txt','text')]:check(P/(e['version']+'.'+suffix),dict(sha256=e[key+'_sha256'],size=e[key+'_size']))
 print(json.dumps(dict(integrity='PASS',intake_exact_payload=True,intake_direct_pairs=len(pairs),flat_original_bindings=len(refs),original_chunks=20,frozen_inputs=8,baseline=8733,literal_reviews=50,reservation_disjointness=True,payload_files=len(entries),proposals=len(j(P/'proposals.json')),scientific_acceptance=False)))
try:main()
except Exception as e:
 __import__('traceback').print_exc();sys.exit(1)
