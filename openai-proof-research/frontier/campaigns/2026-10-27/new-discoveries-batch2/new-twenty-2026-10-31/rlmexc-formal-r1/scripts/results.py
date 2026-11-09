import pathlib,json,re,hashlib,datetime
root=pathlib.Path('.')
mods=root.joinpath('module-order.txt').read_text().split()
rows=[]
for m in mods:
 row={'module':m}
 for kind,prefix in [('compile',''),('leanchecker','check-')]:
  p=root/'replay/logs'/f'{prefix}{m}.log';s=p.read_text()
  status=re.search(r'Exit status: (\d+)',s)
  rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',s)
  elapsed=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)',s)
  row[kind]={'exit_code':int(status[1]) if status else None,'max_rss_kib':int(rss[1]) if rss else None,'elapsed':elapsed[1] if elapsed else None,'log':str(p)}
 rows.append(row)
assert all(r[k]['exit_code']==0 for r in rows for k in ['compile','leanchecker'])
assert all(root.joinpath(m+'.lean').read_bytes()==root.joinpath('replay',m+'.lean').read_bytes() for m in mods)
audit=root.joinpath('replay/logs/Audit.log').read_text()
assert '168 declarations' in audit
assert 'sorryAx' not in audit
assert root.joinpath('logs/source-scan.log').stat().st_size==0
out={'status':'IMPLEMENTED_REPLAYED_NOT_ACCEPTED','endpoint':'AK350721.conjecture_refuted : ¬ VoRConj ∧ ¬ MathDBConj','witness':{'n':9,'k':3,'R_1based':[1,5,7,8],'E_1based':[2,3,4,6,9],'coefficient':-1},'residual_hypotheses':[],'control':'AK350721.nonvacuity_control : InNat (F 3 3)','lean':'4.34.1','mathlib':'d13f23b723b8a846827a245b89c10fc7d3f11612','axioms':['propext','Classical.choice','Quot.sound'],'metadata_declarations':168,'source_scan':'PASS','fresh_extraction':'replay','source_archive_sha256':hashlib.sha256(root.joinpath('source.zip').read_bytes()).hexdigest(),'modules':rows,'acceptance':'root only','optional_8_3':False,'infinite_family_formalized':False,'development_deviations':['Two capped tiny source-generation Python calls issued while prior Lean tool sessions were pending; final capped wrapper now serializes via flock.','Early failure logs overwritten during iteration; complete final replay logs retained.']}
root.joinpath('results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'all_modules_passed':len(rows),'max_rss_kib':max(r[k]['max_rss_kib'] for r in rows for k in ['compile','leanchecker']),'archive_sha256':out['source_archive_sha256']}))
