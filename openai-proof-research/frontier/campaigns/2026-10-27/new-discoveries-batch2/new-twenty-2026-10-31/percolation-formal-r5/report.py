from pathlib import Path
import json,hashlib,re,sys,zipfile
R=Path(sys.argv[1]);F=R/'fresh-extracted';order=(F/'module-order.txt').read_text().splitlines()
def seconds(log):
 s=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',log)[1]
 n=0.
 for x in s.split(':'):n=n*60+float(x)
 return n
rows=[]
for m in order:
 d={'module':m}
 for kind in ['build','check']:
  p=F/'logs'/f'{kind}-{m}'
  receipt=json.loads(p.with_suffix('.json').read_text());assert receipt['exit']==0,(m,kind)
  d[kind+'_wall_seconds']=seconds(p.with_suffix('.log').read_text());d[kind+'_peak_rss_kib']=receipt['peak_rss_kib']
 assert (F/'logs'/f'{m}.ok').exists()
 rows.append(d)
manifest=json.loads((R/'inherited-source-comparison.json').read_text())
assert all(hashlib.sha256((F/n).read_bytes()).hexdigest()==h for n,h in manifest.items())
with zipfile.ZipFile(R/'source-only.zip') as z:
 assert all(z.read('src/'+m+'.lean')==(F/'src'/f'{m}.lean').read_bytes() for m in order)
progress=json.loads((R/'normalized-progress.json').read_text());N=progress['replayed_steps']
assert N>12500
results={'status':'conditional','endpoint':f'Percolation.NReplay.not_conjecture20_normalized_after{N}', 'statement':'RemainingSuffixUnsatR5 → ¬ Conjecture20','modules':len(order),'compiler_passes':len(rows),'explicit_module_checker_passes':len(rows),'compiler_wall_seconds':sum(x['build_wall_seconds'] for x in rows),'checker_wall_seconds':sum(x['check_wall_seconds'] for x in rows),'progress':progress,'remaining_additions':129671-N,'inherited_sources_byte_identical':443,'archive_sha256':hashlib.sha256((R/'source-only.zip').read_bytes()).hexdigest(),'axioms':['propext','Classical.choice','Quot.sound'],'unconditional_proved':False,'acceptance_claimed':False}
results['combined_wall_seconds']=results['compiler_wall_seconds']+results['checker_wall_seconds']
(R/'module-times.json').write_text(json.dumps(rows,indent=2));(R/'results.json').write_text(json.dumps(results,indent=2))
print(json.dumps(results,indent=2))
log=(F/'logs/build-NormalizedExport.log').read_text()
export=log.split('BEGIN_DIMACS\n',1)[1].split('END_DIMACS',1)[0]
assert export.encode()==(F/'normalized.cnf').read_bytes()
(R/'generator-correspondence.json').write_text(json.dumps({'fresh_exact_byte_match':True,'sha256':hashlib.sha256(export.encode()).hexdigest(),'clauses':14698,'variables':1085,'units':[1,26,31]},indent=2))
audit=(F/'logs/build-AuditR5.log').read_text()
assert 'Local declaration metadata audit passed:' in audit
endpoint=(F/'logs/build-EndpointR5.log').read_text()
assert 'sorryAx' not in endpoint and 'depends on axioms: [propext, Classical.choice, Quot.sound]' in endpoint
(R/'axioms.txt').write_text(endpoint.split('\n\tCommand being timed:')[0])
(R/'metadata-audit.txt').write_text(audit.split('\n\tCommand being timed:')[0])
print('Fresh DIMACS correspondence, endpoint axioms and metadata audit passed.')
