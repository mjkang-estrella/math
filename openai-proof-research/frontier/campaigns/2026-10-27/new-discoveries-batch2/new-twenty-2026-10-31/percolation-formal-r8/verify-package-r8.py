from pathlib import Path
import json,zipfile,hashlib,re
r=Path(__file__).resolve().parent;strict=r/'strict-final';p=r/'packet'
res=json.loads((r/'results.json').read_text());res['pre_scaling_measurements']=json.loads((r/'scaling-measurements.json').read_text())['windows'];res['scaling_failure']={'module':'R8Chain106561','reason':'fixed -M3500 import-memory threshold','exit':134,'compiler_seconds':6.47,'peak_rss_kib':3587232};res['earlier_unshared_memory_failure']=res.pop('scaling_failure');res['optimized_pre_scaling_measurements']=json.loads((r/'optimized-scaling-measurements.json').read_text())['windows'];res['memory_optimization']='Named reducible mask constants introduced by MaskChainBuildR8; original 303 modules unchanged';res['fresh_replay_archive']='strict-final, safely extracted and manifest checked before any compilation'
(r/'results.json').write_text(json.dumps(res,indent=2))
for name,log in [('axioms.txt','build-EndpointR8.log'),('metadata-audit.txt','build-AuditR8.log')]:
 t=(strict/'logs'/log).read_text().split('\tCommand being timed:')[0];(r/name).write_text(t)
assert re.search(r'Metadata audit passed: [0-9]+ declarations', (r/'metadata-audit.txt').read_text())
t=(r/'axioms.txt').read_text();assert 'depends on axioms: [propext, Classical.choice, Quot.sound]' in t
comp={}
with zipfile.ZipFile(r/'source-only.zip') as z:
 for n in z.namelist():
  if n.endswith('.lean') or n in ['replay.sh','guard.sh','scan.py']:
   a=z.read(n);b=(strict/n).read_bytes();assert a==b;comp[n]=hashlib.sha256(a).hexdigest()
(r/'fresh-source-comparison.json').write_text(json.dumps(comp,indent=2))
for mod in (r/'module-order.txt').read_text().splitlines():
 assert (strict/'logs'/f'{mod}.ok').exists()
 assert (strict/'build'/f'{mod}.olean').exists()
(r/'certificate-sha256.json').write_text(json.dumps({n:hashlib.sha256((r/n).read_bytes()).hexdigest() for n in ['normalized.cnf','normalized-trimmed.json','r7-source.zip','inherited.zip']},indent=2))
with zipfile.ZipFile(r/'full-logs.zip','w',zipfile.ZIP_DEFLATED,compresslevel=1) as z:
 for base in [r/'logs',strict/'logs',r/'fresh-extracted/logs',r/'unshared-logs',r/'optimized-extracted/logs']:
  for f in base.rglob('*'):
   if f.is_file():z.write(f,str(f.relative_to(r)))
 for n in ['fresh-replay.log','strict-replay.log','final-strict-replay.log','incident.txt','scaling-measurements.json','development-progress.json','optimized-replay.log','optimized-scaling-measurements.json']:
  z.write(r/n,n)
print('Verified',len(comp),'proof/driver sources; every ordered strict success verified; metadata, axioms and full logs archived.')
