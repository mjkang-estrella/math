"""Independent read-only verifier. Execute using verify.sh and the fixed guard."""
import pathlib,json,hashlib,sys,collections,datetime
O=pathlib.Path(__file__).resolve().parent;L=O.parent;I=L/'root-mathdb-breadth-intake-r665'
def read(p):return json.loads(pathlib.Path(p).read_text())
def check(p,h,s):
 d=pathlib.Path(p).read_bytes()
 assert len(d)==s, 'size mismatch: '+str(p)
 assert hashlib.sha256(d).hexdigest()==h,'hash mismatch: '+str(p)
def canon(r):return hashlib.sha256(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def main():
 mode=sys.argv[2] if len(sys.argv)==3 and sys.argv[1]=='--negative' else None
 assert len(sys.argv)==1 or mode in ['hash','size','extra'],'invalid arguments'
 m=read(O/'manifest.json');excluded={'manifest.json','final-verification-receipt.json'}
 assert set(m['excluded_exact_paths'])==excluded
 files={x['path']:x for x in m['files']};actual={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file()}-excluded
 if mode=='extra':actual.add('NEGATIVE-INJECTED-EXTRA')
 assert actual==set(files),'extra/missing payload file'
 for n,x in files.items():
  h=x['sha256'];s=x['size']
  if n=='SUMMARY.md' and mode=='hash':h='0'*64
  if n=='SUMMARY.md' and mode=='size':s+=1
  check(O/n,h,s)
 initial=read(O/'initial-bindings.json')
 assert next(x for x in initial if x['path']==str(I/'manifest.json'))['sha256']=='6bb63e007401d8ab4a694f53a93a3e0cd1c738c347f2778d0c39183ab61679a8'
 for x in initial:check(x['path'],x['sha256'],x['size'])
 im=read(I/'manifest.json');assert {str(p.relative_to(I)) for p in I.rglob('*') if p.is_file()}-set(im['excluded_exact_paths'])=={x['path'] for x in im['files']}
 for x in im['files']:check(I/x['path'],x['sha256'],x['size'])
 pairs=read(I/'bindings.json')
 for x in pairs:
  check(x['original'],x['sha256'],x['bytes']);check(x['copy'],x['sha256'],x['bytes'])
 for x in read(O/'flat-bindings.json'):check(x['path'],x['sha256'],x['size'])
 for n in ['source-provenance.json','derivative-bindings.json','image-bindings.json']:
  for x in read(O/n):
   if 'path' in x:check(x['path'],x['sha256'],x['size'])
 inv=L/'pi-mathdb-full-corpus-inventory-r301';check(inv/'manifest.json','4da10b6dcd6d56a34399195f26abe9ff13f8c3fd67e88b672fc35db2a2a71e15',22047)
 inventory=read(inv/'manifest.json');chunks=[x for x in inventory['files'] if x['path'].startswith('corpus/')];assert len(chunks)==20 and len(inventory['frozen_inputs'])==8
 for x in chunks+inventory['frozen_inputs']:check(inv/x['path'],x['sha256'],x['bytes'])
 q=read(I/'queue-r666.json');res=read(I/'reserved-ids-r666.json');ids={x['mathdb_id'] for x in q};assert len(q)==len(ids)==50 and ids==set(res['ids']) and res['coverage_baseline']==7533
 coverage=read(I/'coverage-delta.json');assert len(coverage)==7533;covered=set(map(int,coverage))
 rs=read(I/'active-breadth-reservations.json');sets=[set(x['ids']) for x in rs];assert len(sets)==3 and ids in sets
 protected=set(res['protected_ids']);assert {337963,338290,338366,338408,339564,372627}<=protected
 for a in sets:assert len(a)==50 and not a&covered and not a&protected
 assert all(not a&b for i,a in enumerate(sets) for b in sets[i+1:])
 lb=read(O/'literal-binding.json');check(lb['path'],lb['sha256'],lb['size']);literals=read(O/'literal-records.json');disp=read(O/'dispositions.json')
 assert len(disp)==len(literals)==50 and {x['mathdb_id'] for x in disp}==ids
 assert len({x['mathdb_id'] for x in disp})==50
 wanted=collections.defaultdict(dict)
 for x in literals:
  assert x['mathdb_id'] in ids and x['canonical_record_sha256']==canon(x['record']);wanted[x['chunk']][x['line']]=x
 checked=0
 for p,lines in wanted.items():
  assert p in {str((inv/x['path']).resolve()) for x in chunks}
  with open(p) as f:
   for n,line in enumerate(f,1):
    if n in lines:
     x=lines[n];r=json.loads(line);assert r==x['record'] and r['mathdb_id']==x['mathdb_id'] and canon(r)==x['canonical_record_sha256'];checked+=1
 assert checked==50
 byid={x['mathdb_id']:x for x in literals}
 for d in disp:
  x=byid[d['mathdb_id']];assert d['statement']==x['record']['statement'];assert d['canonical_record_sha256']==x['canonical_record_sha256'];assert d['chunk']==x['chunk'] and d['line']==x['line'];assert hashlib.sha256(d['statement'].encode()).hexdigest()==d['statement_utf8_sha256']
  assert d['classification'] in ['complete','definition-dependent','scope-ambiguous','incomplete'] and d['classification_reason'] and d['technical_assessment'] and d['credit']==0
 assert read(O/'proposals.json')==[]
 counts=collections.Counter(d['classification'] for d in disp);assert dict(counts)==read(O/'screening-counts.json')['classifications']
 return dict(status='PASS_INTEGRITY_ONLY',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),intake_payload_files=len(im['files']),original_copy_pairs=len(pairs),original_chunks=20,frozen_inputs=8,covered_ids=7533,reservation_sets=3,literal_reviews=50,classifications=dict(counts),proposals=0,math_novelty='NOT PASS; registry unavailable HOLD; six public-source exclusions',procedure='Boundary deviation retained in failures.json')
if __name__=='__main__':
 try:print(json.dumps(main(),sort_keys=True))
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
