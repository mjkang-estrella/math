from pathlib import Path
import hashlib, json, sys
from datetime import datetime, timezone
R=Path(__file__).resolve().parent; L=R.parent; F=R/'frozen'; I=L/'pi-mathdb-full-corpus-inventory-r301'
def read(p): return json.loads(p.read_text())
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def check(p,r):
 assert p.is_file() and p.stat().st_size==r.get('size',r.get('bytes')) and sha(p)==r['sha256'],str(p)
def names(p,exc):return {str(x.relative_to(p)) for x in p.rglob('*') if x.is_file()}-set(exc)
def put(n,x):(R/n).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
bindings=read(R/'bindings.json')
for r in bindings:check(Path(r['original']),r);check(Path(r['copy']),r)
configs=[('claude-mathdb-primary-qualified-breadth-r480','root-mathdb-breadth-intake-r479','final-receipt.json',153),('sol-mathdb-primary-qualified-breadth-r490','root-mathdb-breadth-intake-r489','final-receipt.json',176),('sol-mathdb-primary-qualified-breadth-r492','root-mathdb-breadth-intake-r491','verification-receipt.json',54)]
coverage=read(F/'root-mathdb-breadth-intake-r491/coverage-delta.json');assert len(coverage)==3533
allrows={};counts={};refcount=0
for name,assignment,receipt_name,count in configs:
 C=F/name;m=read(C/'manifest.json');exc={'manifest.json',receipt_name}
 assert len(m['files'])==count and len({r['path'] for r in m['files']})==count
 assert names(C,exc)=={r['path'] for r in m['files']}==names(L/name,exc)
 for r in m['files']:check(C/r['path'],r)
 if name.startswith('claude'):
  refs=read(C/'bindings.json')['bindings']
  for r in refs:check(Path(r['original']),r)
  sources=read(C/'retained-sources.json');assert len(sources)==48
  for src in sources:
   for k in ['pdf','text']:check(C/src[k+'_path'],{'sha256':src[k+'_sha256'],'size':src[k+'_bytes']})
  rec=read(C/receipt_name);assert rec['integrity_pass_is_not_math_or_novelty_pass'] is True
  for key,code in [('run_1_with_in_memory_negative_tests',0),('run_2_on_disk_stray_file_expect_nonzero',1),('run_3_after_removal_expect_zero',0)]:
   result,end=json.JSONDecoder().raw_decode(rec[key]);guard,unused=json.JSONDecoder().raw_decode(rec[key][end:].lstrip());assert guard['guard_exit']==code and ('EXIT='+str(code)) in rec[key]
   assert (result['checks_failed']==0)==(code==0)
 else:
  refs=[]
  for file in (['initial-flat-bindings.json','flat-bindings.json','pinned-admin-bindings.json'] if 'r490' in name else ['flat-bindings.json']):refs.extend(read(C/file))
  for r in refs:check(Path(r['path']),r)
  rec=read(C/receipt_name);assert rec['status']=='PASS'
  if 'r490' in name:
   assert rec['exit']==0 and rec['manifest_sha256']==sha(C/'manifest.json')
   assert json.loads(rec['stderr'])['guard_exit']==0 and all(x['exit']!=0 for x in rec['negative_tests'])
   for src in read(C/'source-bindings.json'):
    for k in ['pdf','text']:check(Path(src[k]['path']),src[k])
  else:assert rec['mathematics_novelty_compliance_pass'] is False and rec['accepted_credit']==0
 refcount+=len(refs);counts[name]=count
 rows=read(C/'dispositions.json');ids={str(r['mathdb_id']) for r in rows}
 assert len(rows)==len(ids)==50 and ids==set(map(str,read(F/assignment/'reserved-ids.json')['ids']))
 assert not ids&set(coverage) and not ids&set(allrows)
 for r in rows:assert r['accepted_credit']==0;allrows[str(r['mathdb_id'])]=(name,r)
 proposals=read(C/'proposals.json')
 if name.startswith('claude'):
  briefs=proposals['qualified_briefs'];assert {p['mathdb_id'] for p in briefs}=={338290,339564,337963} and proposals['accepted_credit']==0
 else:assert proposals==[] or proposals['qualified_briefs']==[]
im=read(F/'pi-mathdb-full-corpus-inventory-r301/manifest.json');assert im==read(I/'manifest.json')
chunks=[r for r in im['files'] if r['path'].startswith('corpus/')];assert len(chunks)==20 and len(im['frozen_inputs'])==8
for r in chunks+im['frozen_inputs']:check(I/r['path'],r)
found={}
for entry in chunks:
 p=I/entry['path']
 with p.open() as f:
  for line,s in enumerate(f,1):
   x=json.loads(s);n=str(x['mathdb_id'])
   if n in allrows:assert n not in found;found[n]=(p,line,x)
assert set(found)==set(allrows) and len(found)==150
for n,(name,r) in allrows.items():
 p,line,x=found[n];assert r['literal_statement']==x['statement'] and (I/r['original_chunk']).resolve()==p.resolve() and r['original_line']==line
 assert r['statement_utf8_sha256']==hashlib.sha256(x['statement'].encode()).hexdigest()
 assert r['canonical_record_sha256']==hashlib.sha256(json.dumps(x,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode()).hexdigest()
 evidence=r.get('evidence_levels',{k:r.get(k) for k in ['source_evidence_level','proof_evidence_level','prior_evidence_level','dependency_audit']})
 coverage[n]={'disposition':r['disposition'],'report':name+'/dispositions.json','record_statement_review':'delegate_reported_complete','evidence_level_reported':evidence,'source_scope_cleared':False,'prior_cleared':False,'accepted_credit':0,'proof_dependency_scope_reported':'no_complete_dependency_audit','scope_discipline_limit':'Root integrity reconciliation only; source/successor/proof gates and disclosed process deviations retained. Screening briefs are not accepted results.'}
assert len(coverage)==3683
routes=[{'mathdb_id':338290,'lane':'claude-mathdb-banzhaf-source-prior-review-r494','status':'assigned_source_first_review'},{'mathdb_id':339564,'lane':'sol-mathdb-abelianisation-source-prior-review-r496','status':'assigned_source_first_review'},{'mathdb_id':337963,'lane':'sol-mathdb-linear-two-tree-source-prior-review-r498','status':'assigned_source_first_review'}]
outputs={'coverage-delta.json':coverage,'hypothesis-queue.json':routes,'adjudications.json':read(F/'root-mathdb-breadth-intake-r491/adjudications.json'),'active-breadth-reservations.json':[]}
exc={'manifest.json','verification-receipt.json'}
if sys.argv[1:] == ['build']:
 for n,x in outputs.items():put(n,x)
 put('manifest.json',{'files':[{'path':s,'size':(R/s).stat().st_size,'sha256':sha(R/s)} for s in sorted(names(R,exc))],'excluded_exact_paths':sorted(exc)})
elif sys.argv[1:] == ['verify']:
 for n,x in outputs.items():assert read(R/n)==x
 own=read(R/'manifest.json')['files'];assert names(R,exc)=={r['path'] for r in own}
 for r in own:check(R/r['path'],r)
 put('verification-receipt.json',{'status':'PASS','utc':datetime.now(timezone.utc).isoformat(),'root_bindings':len(bindings),'child_payloads':counts,'flat_reference_entries':refcount,'corpus_chunks':20,'separate_frozen_inputs':8,'reported_statement_reviews':len(coverage),'new_literal_hashes':150,'hypothesis_reviews_assigned':3,'accepted_counts':[9,39,40],'mathematical_replay':False})
else:raise SystemExit('build or verify')
print('PASS',sys.argv[1],len(coverage),'reported reviews',refcount,'reference entries')
