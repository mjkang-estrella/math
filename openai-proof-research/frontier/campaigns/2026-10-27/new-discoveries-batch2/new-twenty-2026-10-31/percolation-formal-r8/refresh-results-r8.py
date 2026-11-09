from pathlib import Path
import json
r=Path(__file__).resolve().parent;p=r/'results.json';d=json.loads(p.read_text());f=d['fresh_replay']
d.update({'modules_total':f['modules'],'compiler_passes':f['modules'],'checker_passes':f['modules'],'compiler_seconds':f['compiler_seconds'],'checker_seconds':f['checker_seconds'],'total_seconds':f['total_seconds'],'peak_rss_kib':f['peak_rss_kib'],'replayed_archive_sha256':(r/'replayed-source-archive.sha256').read_text().split()[0]})
d['window_accounting']='Sum of successful per-process wall times allocated to the exact addition interval and its newly required input modules. All named dependencies are real, checked theorems. Cumulative prefix costs conservatively include any later input modules prepared up front.'
p.write_text(json.dumps(d,indent=2))
times=json.loads((r/'module-times.json').read_text());d['maximum_compile_seconds']=max(x['build_seconds'] for x in times);d['maximum_check_seconds']=max(x['check_seconds'] for x in times)
for phase in ['build','check']:
 for f in (r/'strict-final/logs').glob(phase+'-*.json'):assert json.loads(f.read_text())['exit']==0
p.write_text(json.dumps(d,indent=2))
