"""Independent read-only verification; run through fixed helper_guard.py, python3 -B."""
import pathlib,json,hashlib,sys
P=pathlib.Path(__file__).resolve().parent
L=P.parent;I=L/'root-mathdb-breadth-intake-r589';C=L/'pi-mathdb-full-corpus-inventory-r301'
def sha(b):return hashlib.sha256(b).hexdigest()
def load(p):return json.loads(p.read_text())
def check_bytes(b,e):
 if len(b)!=e.get('size',e.get('bytes')):raise ValueError('size mismatch: '+str(e.get('path')))
 if sha(b)!=e['sha256']:raise ValueError('hash mismatch: '+str(e.get('path')))
def check_names(actual,expected):
 if set(actual)!=set(expected):raise ValueError('missing/extra payload: '+repr(set(actual)^set(expected)))
def verify_manifest(root,m):
 excludes=m['excluded_exact_paths']
 assert excludes==['manifest.json','final-verification-receipt.json'] if root==P else excludes==['manifest.json','verification-receipt.json']
 paths=[e['path'] for e in m['files']];assert len(paths)==len(set(paths))
 check_names([str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()],paths+excludes)
 for e in m['files']:check_bytes((root/e['path']).read_bytes(),e)
def main():
 m=load(P/'manifest.json');verify_manifest(P,m)
 refs=load(P/'flat-bindings.json');assert len(refs)==137
 for e in refs:check_bytes(pathlib.Path(e['path']).read_bytes(),e)
 # Fixed trusted intake anchor independent of its mutable manifest.
 check_bytes((I/'manifest.json').read_bytes(),dict(path=str(I/'manifest.json'),sha256='f113bfb809c174de3bf97a7101fde67845574bcfcfb4f8d70b4f75d40300ecbd',size=10560))
 verify_manifest(I,load(I/'manifest.json'))
 pairs=load(I/'bindings.json');assert len(pairs)==44
 for e in pairs:
  a=pathlib.Path(e['original']).read_bytes();b=pathlib.Path(e['copy']).read_bytes()
  check_bytes(a,e);check_bytes(b,e);assert a==b
 inv=load(C/'manifest.json');chunks=[e for e in inv['files'] if e['path'].startswith('corpus/')]
 assert len(chunks)==20 and len(inv['frozen_inputs'])==8
 for e in chunks+inv['frozen_inputs']:check_bytes((C/e['path']).read_bytes(),e)
 r=load(I/'reserved-ids.json');assigned=set(r['ids']);assert len(assigned)==50
 assert r['lane']==P.name and assigned=={x['mathdb_id'] for x in load(I/'queue.json')}
 covered=load(I/'coverage-delta.json');assert len(covered)==5683
 active=load(I/'active-breadth-reservations.json')
 own=[x for x in active if set(x['ids'])==assigned];assert len(own)==1
 others=[set(x['ids']) for x in active if set(x['ids'])!=assigned];sets=others+[assigned]
 protected={337963,338290,339564,372627,372628,368940,404067,364119,366370,365437,365439}
 assert protected==set(r['protected_ids'])
 for j,s in enumerate(sets):
  assert len(s)==50 and not s&set(map(int,covered)) and not s&protected
  for t in sets[:j]:assert not s&t
 assert set(r['other_active_reservations'])==set().union(*others)
 literal=load(P/'literal-records.json');ds=load(P/'dispositions.json')
 assert len(ds)==len(literal)==50 and {x['mathdb_id'] for x in ds}==assigned
 assert len(load(P/'proposals.json'))==0
 ds={x['mathdb_id']:x for x in ds};lit={x['record']['mathdb_id']:x for x in literal};seen=set()
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   o=json.loads(line);i=o['mathdb_id']
   if i not in assigned:continue
   assert i not in seen;seen.add(i)
   x=lit[i];d=ds[i];s=o['statement']
   canonical=sha(json.dumps(o,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode())
   assert x['record']==o and x['line']==n and x['chunk']==str(p)
   assert d['corpus_line']==n and d['corpus_chunk']==str(p)
   assert d['statement']==s and d['statement_utf8_sha256']==sha(s.encode())
   assert d['canonical_record_sha256']==x['canonical_record_sha256']==canonical
   assert d['accepted_credit']==0 and not d['proposal']
   f=d['scope_flags'];assert f['literal_record_statement_read_in_full']
   assert not f['current_registry_cleared'] and not f['novelty_cleared'] and not f['full_scope_resolution_claimed']
 assert seen==assigned
 for file in ['source-provenance.json','derivative-bindings.json','pdf-bindings.json','pdf-derivative-bindings.json']:
  for e in load(P/file):check_bytes((P/e['path']).read_bytes(),e)
 report=dict(integrity='PASS',scientific_acceptance=False,novelty='HOLD',assigned_literal_record_reviews=50,baseline_record_reviews=5683,primary_passage_rows=7,proposals=0,intake_exact_payload=True,original_copy_pairs=44,original_chunks_in_place=20,frozen_inputs_in_place=8,all_reservations_disjoint=True,payload_files=len(m['files']),manifest_sha256=sha((P/'manifest.json').read_bytes()),manifest_size=(P/'manifest.json').stat().st_size)
 print(json.dumps(report,sort_keys=True))
if __name__=='__main__':
 try:main()
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
