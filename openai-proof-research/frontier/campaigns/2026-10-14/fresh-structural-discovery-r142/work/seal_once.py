"""One final discovery-packet seal. Refuses an existing final envelope.
This is integrity packaging, not a release or a mathematical gate.
"""
from pathlib import Path
import hashlib,json,datetime,subprocess,sys,os
R=Path(__file__).resolve().parents[1]
envelopes={'MANIFEST.json','FINAL.json','outsideREPORT.md','ANCHORS.json'}
for name in envelopes-{'outsideREPORT.md'}:
 if (R/name).exists():raise RuntimeError('Refusing to reseal '+name)
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for p in sorted(R.rglob('*')):
 if p.is_symlink():raise RuntimeError('Symlink')
 if p.is_file():
  name=p.relative_to(R).as_posix()
  if name not in envelopes:rows.append(dict(path=name,bytes=p.stat().st_size,sha256=h(p)))
(R/'MANIFEST.json').write_text(json.dumps(dict(schema='r142-exact-file-inventory-v1',files=rows),indent=2)+'\n')
final=dict(status='PREFREEZE/no nominee',frozen_statement=False,mathematical_gates_assigned=False,
 runner='Codex / GPT-6 Astra / high / default service tier',
 pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',
 sealed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 manifest_sha256=h(R/'MANIFEST.json'),outside_report_sha256=h(R/'outsideREPORT.md'),
 verifier_path='packet/public/verify_packet.py',verifier_sha256=h(R/'packet/public/verify_packet.py'),
 payload_files=len(rows),handoff='packet/public/handoff.md')
(R/'FINAL.json').write_text(json.dumps(final,indent=2)+'\n')
a={x:h(R/x) for x in ['MANIFEST.json','FINAL.json','outsideREPORT.md']}
(R/'ANCHORS.json').write_text(json.dumps(a,indent=2)+'\n')
cmd=[sys.executable,str(R/'packet/public/verify_packet.py'),str(R),'--manifest-sha256',a['MANIFEST.json'],'--final-sha256',a['FINAL.json'],'--report-sha256',a['outsideREPORT.md']]
p=subprocess.run(cmd,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'},capture_output=True,text=True)
print(p.stdout,end='')
if p.returncode:raise RuntimeError(p.stderr)
print(json.dumps(a,indent=2))
