#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,re
r=Path(__file__).resolve().parent.parent
e=r/'extracted-replay'
hashfile=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((r/'MANIFEST.json').read_text())
for name,h in m['files'].items():
 assert hashfile(r/name)==h,name
 assert hashfile(e/name)==h,name
assert hashfile(r/'MANIFEST.json')==hashfile(e/'MANIFEST.json')
steps=json.loads((e/'replay-results.json').read_text());assert len(steps)==26 and all(x['exit']==0 for x in steps)
reject=json.loads((e/'rejection-results.json').read_text());assert len(reject)==3 and all(x['expected_rejection'] for x in reject)
audit=[];resources=[]
for log in (e/'replay-logs').glob('*.log'):
 for line in log.read_text().splitlines():
  if line.startswith('{'):
   try:x=json.loads(line)
   except json.JSONDecodeError:continue
   if 'module' in x and 'axioms' in x:audit.append(x)
   if 'peak_rss_bytes' in x:resources.append(x)
assert len(audit)==123
assert len({x['name'] for x in audit})==len(audit)
assert all(x['value_present'] and not x['unsafe'] and not x['partial'] and set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in audit)
assert len(resources)==29
assert all(x['peak_rss_bytes']<=6*1024**3 and x['wall_seconds']<=140 and x['kill_reason'] is None for x in resources)
inputs=json.loads((r/'receipts/inputs-before.json').read_text())
for name,h in inputs.items():assert hashfile(Path('/home/mj-kang/Documents/Dev/math')/name)==h,name
receipt={
 'status':'PASS','fresh_extraction':str(e),'archive_sha256':hashfile(r/'proof-packet.zip'),
 'manifest_sha256':hashfile(r/'MANIFEST.json'),'manifest_files':len(m['files']),
 'all_archived_files_match_manifest_before_and_after_replay':True,
 'strict_build_and_checker_steps':steps,'negative_rejections':reject,
 'audited_declarations':len(audit),'audit_modules':sorted({x['module'] for x in audit}),
 'audit_sha256':hashfile(e/'replay-logs/audit.log'),
 'axioms':['propext','Classical.choice','Quot.sound'],
 'resource_subprocesses':len(resources),'max_sampled_rss_bytes':max(x['peak_rss_bytes'] for x in resources),
 'max_wall_seconds':max(x['wall_seconds'] for x in resources),
 'resource_receipts':resources,
 'frozen_inputs_unchanged':True,
 'logs':{str(p.relative_to(e)):hashfile(p) for p in sorted((e/'replay-logs').glob('*.log'))},
 'credit':0,'acceptance':'root alone; not claimed'}
(r/'receipts/extracted-replay.json').write_text(json.dumps(receipt,indent=2)+'\n')
(r/'receipts/declarations.json').write_text(json.dumps(audit,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k not in ['resource_receipts','strict_build_and_checker_steps','logs','negative_rejections']},indent=2))
