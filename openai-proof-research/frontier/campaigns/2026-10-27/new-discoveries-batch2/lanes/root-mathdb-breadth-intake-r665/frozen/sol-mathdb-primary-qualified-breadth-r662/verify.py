"""Independent read-only checker; execute only through the fixed guard."""
import pathlib,json,hashlib,sys,collections
O=pathlib.Path(__file__).resolve().parent
EX={'manifest.json','final-verification-receipt.json'}
def load(p):return json.loads(p.read_text())
def check(p,h,s):
 d=p.read_bytes()
 if len(d)!=s:raise ValueError('size mismatch: '+str(p))
 if hashlib.sha256(d).hexdigest()!=h:raise ValueError('hash mismatch: '+str(p))
def payload(root):
 m=load(root/'manifest.json')
 assert set(m['excluded_exact_paths'])==EX
 names=[f['path'] for f in m['files']];assert len(names)==len(set(names))
 actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
 assert actual-EX==set(names),('exact payload mismatch',actual-EX-set(names),set(names)-actual)
 for f in m['files']:check(root/f['path'],f['sha256'],f['size'])
 return len(names)
def main():
 if len(sys.argv)>1:
  assert sys.argv[1]=='--payload-only';print(json.dumps({'payload_files':payload(pathlib.Path(sys.argv[2]))}));return
 n=payload(O);L=O.parent;I=L/'root-mathdb-breadth-intake-r661';R=L/'pi-mathdb-full-corpus-inventory-r301'
 for f in load(O/'initial-bindings.json')+load(O/'flat-bindings.json'):check(pathlib.Path(f['path']),f['sha256'],f['size'])
 im=load(I/'manifest.json');assert set(im['excluded_exact_paths'])=={'manifest.json','verification-receipt.json'}
 assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}=={f['path'] for f in im['files']}|set(im['excluded_exact_paths'])
 for f in im['files']:check(I/f['path'],f['sha256'],f['size'])
 pairs=load(I/'bindings.json');assert len(pairs)==38
 for f in pairs:
  for key in ['original','copy']:check(pathlib.Path(f[key]),f['sha256'],f['bytes'])
 inv=load(R/'manifest.json');chunks=[f for f in inv['files'] if f['path'].startswith('corpus/')];assert len(chunks)==20 and len(inv['frozen_inputs'])==8
 for f in chunks+inv['frozen_inputs']:check(R/f['path'],f['sha256'],f['bytes'])
 coverage=load(I/'coverage-delta.json');assert len(coverage)==7433
 reservations=load(I/'active-breadth-reservations.json');assert len(reservations)==3
 seen=set();protected=set(load(I/'reserved-ids-r662.json')['protected_ids'])
 for r in reservations:
  ids=set(r['ids']);assert len(ids)==50 and len(r['ids'])==50
  assert not ids & seen and not ids & set(map(int,coverage)) and not ids & protected
  seen|=ids
 reservation=load(I/'reserved-ids-r662.json');queue=load(I/'queue-r662.json');ids=reservation['ids']
 assert reservation['lane']==O.name and len(ids)==50 and len(set(ids))==50 and reservation['coverage_baseline']==7433
 assert ids==[r['mathdb_id'] for r in queue]
 assert any(r['lane']==O.name and r['ids']==ids for r in reservations)
 records=load(O/'literal-records.json');disps=load(O/'dispositions.json');assert len(records)==len(disps)==50
 assert [x['record']['mathdb_id'] for x in records]==ids==[d['mathdb_id'] for d in disps]
 for z,d,q in zip(records,disps,queue):
  path=pathlib.Path(z['chunk']);assert str(path.relative_to(R)) in {f['path'] for f in chunks}
  with path.open() as f:
   for line_no,line in enumerate(f,1):
    if line_no==z['line']:original=json.loads(line);break
   else:raise ValueError('missing original line')
  assert original==z['record']
  canon=hashlib.sha256(json.dumps(original,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
  assert canon==z['canonical_record_sha256']==d['canonical_record_sha256']
  assert d['exact_utf8_statement']==original['statement']
  assert hashlib.sha256(original['statement'].encode()).hexdigest()==d['statement_utf8_sha256']
  assert d['chunk']==z['chunk'] and d['line']==z['line']
  assert all(original[k]==q[k] for k in ['mathdb_id','title','canonical_url'])
  assert d['completeness_classification'] in {'complete','definition-dependent','scope-ambiguous','incomplete'}
  assert d['completeness_reason'] and d['quantifiers'] and d['technical_assessment'] and d['accepted_credit']==0
 assert load(O/'proposals.json')==[]
 for f in load(O/'source-provenance.json')+load(O/'derivative-bindings.json'):[check(pathlib.Path(f['path']),f['sha256'],f['size'])]
 f=load(O/'literal-binding.json');check(pathlib.Path(f['path']),f['sha256'],f['size'])
 print(json.dumps({'integrity':'PASS','payload_files':n,'intake_pairs':38,'original_chunks':20,'separate_frozen_inputs':8,'coverage_baseline':7433,'disjoint_reserved_sets':3,'literal_reviews':50,'classifications':dict(collections.Counter(d['completeness_classification'] for d in disps)),'proposals':0,'mathematical_or_novelty_pass':False}))
if __name__=='__main__':
 try:main()
 except Exception as e:
  print('FAIL '+repr(e),file=sys.stderr);sys.exit(1)
