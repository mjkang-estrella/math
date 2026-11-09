from pathlib import Path
import json, hashlib, subprocess
p=Path(__file__).resolve().parent
h=lambda q: hashlib.sha256(q.read_bytes()).hexdigest()
rs=[(q,json.loads(q.read_text())) for q in sorted((p/'receipt').glob('*.json'))]
records=[]
for s in sorted((p/'src').glob('*.lean')):
 m=s.stem
 records.append(dict(module=m,source_sha256=h(s),olean_sha256=h(p/'build'/(m+'.olean')) if (p/'build'/(m+'.olean')).exists() else None,runs=[dict(receipt=str(q.relative_to(p)),receipt_sha256=h(q),exit=r['exit'],log=r['log'],log_sha256=r['log_sha256'],group_members_left=r['group_members_left']) for q,r in rs if r.get('label') in ('lean_'+m,'leanchecker_'+m)]))
d=dict(mathdb_id=324571,status='PARTIAL_NOT_ENDPOINT',credit=0,campaign='55/60 beyond39',paid_new=['isolated event equals exact iid finite cylinder','isolated_probability exact p_i squared times complement power; strict+checker green'],unpaid=json.loads((p/'inputs/previous/results/CHECKPOINT.json').read_text())['unpaid'],records=records,deviations=['Initial receipt and log displayed by uncapped direct Python read; preserved transcript. Subsequent display runs use exact runner CLI with logged output mirrored to parent shell stdout.','Initial mandatory dumps materially truncated; semantic fields/source passages recovered; bulk metadata not fully displayed.'],process_limits='per-group sampled, not cgroup')
subprocess.run(['python3','-I','-B',str(p/'write_lane.py'),'results/CHECKPOINT.json'],input=json.dumps(d,indent=2),text=True,check=True)
