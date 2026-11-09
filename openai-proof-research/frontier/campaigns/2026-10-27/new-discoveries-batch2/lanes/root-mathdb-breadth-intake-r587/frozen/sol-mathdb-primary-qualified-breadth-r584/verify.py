#!/usr/bin/env python3
"""Independent read-only verifier. Run under the fixed helper_guard.py."""
from pathlib import Path
import hashlib,json,itertools,sys
J=lambda p:json.loads(p.read_text())
def binding(p,e):
 b=p.read_bytes();assert len(b)==e.get('size',e.get('bytes')),f'size mismatch: {p}'
 assert hashlib.sha256(b).hexdigest()==e['sha256'],f'hash mismatch: {p}'
def payload(d,m):
 excluded=m['excluded_exact_paths'];assert excluded==['manifest.json','final-verification-receipt.json']
 names=[x['path'] for x in m['files']];assert len(names)==len(set(names))
 assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in names)
 actual={str(p.relative_to(d)) for p in d.rglob('*') if p.is_file()}-set(excluded)
 assert actual==set(names),f'exact payload mismatch: {actual^set(names)}'
 for x in m['files']:binding(d/x['path'],x)
def main():
 D=Path(__file__).resolve().parent
 if len(sys.argv)>1:
  assert sys.argv[1]=='--payload-only';d=Path(sys.argv[2]);payload(d,J(d/'manifest.json'));return {'fixture':'PASS'}
 payload(D,J(D/'manifest.json')); L=D.parent; I=L/'root-mathdb-breadth-intake-r583';R=L/'pi-mathdb-full-corpus-inventory-r301'
 refs=J(D/'flat-bindings.json');refsmap={v['path']:v for v in refs};assert len(refsmap)==len(refs)
 for x in refs:binding(Path(x['path']),x)
 assert hashlib.sha256((I/'manifest.json').read_bytes()).hexdigest()=='bb48ce18c88c4dd882abfab1a66d83404fd238840ad71055b9f1d44f9cadd359'
 im=J(I/'manifest.json'); actual={str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(im['excluded_exact_paths']);assert actual=={v['path'] for v in im['files']}
 for x in im['files']:binding(I/x['path'],x)
 pairs=J(I/'bindings.json')
 for x in pairs:
  p=Path(x['original']);q=Path(x['copy']);binding(p,x);binding(q,x);assert p.read_bytes()==q.read_bytes()
 inventory=J(R/'manifest.json'); chunks=[x for x in inventory['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(inventory['frozen_inputs'])==8
 for x in chunks+inventory['frozen_inputs']:binding(R/x['path'],x)
 cov=J(I/'coverage-delta.json');assert len(cov)==5533;covids=set(map(int,cov));reserved=J(I/'reserved-ids.json');active=J(I/'active-breadth-reservations.json');sets=[set(r['ids']) for r in active];assert len(sets)==3
 for s in sets:assert len(s)==50 and not s&covids and not s&set(reserved['protected_ids'])
 for a,b in itertools.combinations(sets,2):assert not a&b
 own=set(reserved['ids']);assert len(own)==50 and own in sets
 assert set(reserved['other_active_reservations'])==set.union(*[s for s in sets if s!=own])
 assert {344924,386396,387650}<=covids
 assert next(x for x in active if 'r504' in x['lane'])['status']=='rate_limited_reserved_unreviewed'
 assert set(r['mathdb_id'] for r in J(I/'queue.json'))==own
 literal=J(D/'literal-records.json');ds=J(D/'dispositions.json');assert len(literal)==len(ds)==50;assert {r['mathdb_id'] for r in ds}==own;assert len(J(D/'proposals.json'))<=3
 by={r['mathdb_id']:r for r in ds};lit={r['id']:r for r in literal};seen=set()
 for x in chunks:
  p=R/x['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line);i=r['mathdb_id']
   if i not in own:continue
   assert i not in seen;seen.add(i);d=by[i];a=lit[i]
   assert a['record']==r and a['line']==d['corpus_line']==n and a['chunk']==d['corpus_chunk']==str(p)
   canonical=hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
   assert canonical==d['canonical_record_sha256']==a['canonical_record_sha256']
   s=r['statement'].encode();assert d['statement_utf8']==r['statement'] and d['statement_utf8_size']==len(s) and d['statement_utf8_sha256']==hashlib.sha256(s).hexdigest()
   f=d['scope_flags'];assert f['literal_full_record_statement_read'] is True and f['accepted_credit']==0 and not f['current_registry_cleared'] and not f['novelty_cleared']
 assert seen==own
 for x in J(D/'source-provenance.json')+J(D/'derivative-bindings.json'):
  if 'path' in x:binding(Path(x['path']),x)
 return {'integrity':'PASS','intake_exact_payload_files':len(im['files']),'original_copy_pairs':len(pairs),'original_chunks_in_place':20,'frozen_inputs':8,'baseline_records':5533,'assigned_dispositions':50,'proposals':len(J(D/'proposals.json')),'reservation_sets_disjoint':True,'literal_and_canonical_hashes':'PASS','math_novelty':'NOT CERTIFIED; HOLD','read_only':True}
if __name__=='__main__':
 try:print(json.dumps(main(),indent=2))
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
