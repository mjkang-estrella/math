#!/usr/bin/env python3
"""Independent read-only verifier. Never invokes an upstream verifier."""
import pathlib,json,hashlib,sys,copy,datetime
L=pathlib.Path(__file__).resolve().parent;I=L.parent/'root-mathdb-breadth-intake-r685';R=L.parent/'pi-mathdb-full-corpus-inventory-r301'
def load(p):return json.loads(p.read_text())
def h(b):return hashlib.sha256(b).hexdigest()
def check_bytes(b,row):
 assert len(b)==row.get('size',row.get('bytes')),'size mismatch'
 assert h(b)==row['sha256'],'hash mismatch'
def check_file(p,row):check_bytes(p.read_bytes(),row)
def payload(base,m,override=None,extra=None):
 expected={r['path'] for r in m['files']};actual={str(p.relative_to(base)) for p in base.rglob('*') if p.is_file()}-set(m['excluded_exact_paths'])
 assert len(expected)==len(m['files']),'duplicate manifest paths'
 assert actual|set(extra or [])==expected,'exact payload mismatch'
 for row in m['files']:
  assert not pathlib.Path(row['path']).is_absolute() and '..' not in pathlib.Path(row['path']).parts
  check_bytes((override or {}).get(row['path'],(base/row['path']).read_bytes()),row)
def main():
 m=load(L/'manifest.json');assert set(m['excluded_exact_paths'])=={'manifest.json','final-verification-receipt.json'};payload(L,m)
 for r in load(L/'flat-bindings.json'):check_file(pathlib.Path(r['path']),r)
 im=load(I/'manifest.json');payload(I,im)
 pairs=load(I/'bindings.json')
 for r in pairs:
  for k in ['original','copy']:check_file(pathlib.Path(r[k]),r)
 assert (R/'manifest.json').read_bytes()==(I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json').read_bytes()
 inv=load(R/'manifest.json');chunks=[r for r in inv['files'] if r['path'].startswith('corpus/')]
 assert len(chunks)==20 and len(inv['frozen_inputs'])==8
 for r in chunks+inv['frozen_inputs']:check_file(R/r['path'],r)
 q=load(I/'queue-r686.json');res=load(I/'reserved-ids-r686.json');ids=set(res['ids']);assert len(ids)==len(q)==50;assert ids=={r['mathdb_id'] for r in q}
 coverage=load(I/'coverage-delta.json');assert len(coverage)==8033
 reservations=load(I/'active-breadth-reservations.json');assert len(reservations)==3
 seen=set();protected=set(res['protected_ids'])
 for a in reservations:
  s=set(a['ids']);assert len(s)==50;assert not s&seen;assert not s&protected;assert not set(map(str,s))&set(coverage);seen|=s
 assert ids<=seen
 assert {r['lane'] for r in reservations}=={'claude-mathdb-primary-qualified-breadth-r628','sol-mathdb-primary-qualified-breadth-r684',L.name}
 literal=load(L/'literal-records.json');d=load(L/'dispositions.json');assert len(literal)==len(d)==50
 assert {x['record']['mathdb_id'] for x in literal}=={x['mathdb_id'] for x in d}==ids
 byid={r['mathdb_id']:r for r in d};found={}
 # Stream originals; never display adjacent records.
 for c in chunks:
  for n,b in enumerate((R/c['path']).open('rb'),1):
   r=json.loads(b)
   if r.get('mathdb_id') in ids:found[r['mathdb_id']]=(r,str(R/c['path']),n)
 assert set(found)==ids
 for x in literal:
  r=x['record'];id=r['mathdb_id'];orig,p,n=found[id];assert orig==r and p==x['chunk'] and n==x['line']
  canon=h(json.dumps(orig,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode());assert canon==x['canonical_sha256']==byid[id]['canonical_record_sha256']
  v=byid[id];assert v['statement_utf8']==orig['statement'];assert h(orig['statement'].encode())==v['statement_sha256'];assert v['chunk']==p and v['line']==n
  assert v['classification'] in ['complete','definition-dependent','scope-ambiguous','incomplete'];assert all(v[k] for k in ['classification_reason','quantifiers','technical_disposition']);assert v['accepted_credit']==0
 assert load(L/'proposals.json')==[]
 for r in load(L/'source-provenance.json'):
  if 'path' in r:check_file(L/r['path'],r)
 neg=[]
 target=next(r for r in m['files'] if r['path']=='proposals.json');b=(L/target['path']).read_bytes()
 for label,ov,extra in [('hash', {target['path']:bytes([b[0]^1])+b[1:]},None),('size',{target['path']:b+b' '},None),('extra',None,['__bounded_negative_extra__'])]:
  try:payload(L,m,ov,extra)
  except AssertionError as e:neg.append({'test':label,'rejected':True,'reason':str(e)})
  else:raise AssertionError('negative accepted '+label)
 print(json.dumps({'integrity':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':h((L/'manifest.json').read_bytes()),'manifest_size':(L/'manifest.json').stat().st_size,'payload_files':len(m['files']),'original_copy_pairs':len(pairs),'chunks':20,'frozen_inputs':8,'literal_reviews':50,'coverage_baseline':8033,'reservations':'3 x 50 disjoint from baseline, each other, protected','bounded_negatives':neg,'math':'NOT VALIDATED','novelty':'HOLD','proposals':0},indent=2))
if __name__=='__main__':
 try:main()
 except Exception as e:print('VERIFICATION FAILED: '+str(e),file=sys.stderr);sys.exit(1)
