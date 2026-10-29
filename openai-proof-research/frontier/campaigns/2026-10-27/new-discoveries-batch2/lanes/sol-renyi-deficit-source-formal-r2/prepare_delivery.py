import hashlib,json,shutil
from pathlib import Path
r=Path(__file__).resolve().parent
new=['Deficit','Baseline','Endpoint']
mods=['Pointwise','Majorant','Tail','Density','LogConcavity','InputMoment','Profile','Result']+new
frozen=json.loads((r/'frozen-before.json').read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in frozen['files'].items():
 assert sha(Path(frozen['root'])/n)==h,n
 if n.startswith('formal/') or n in ['guard.py','helper_guard.py','replay_guard.py','pins.json']:
  assert sha(r/n)==h,n
audit=(r/'formal/OriginAudit.lean').read_text()
audit=audit.replace('import all Result\n','import all Result\n'+''.join('import all '+n+'\n' for n in new))
audit=audit.replace('`Profile, `Result]', '`Profile, `Result, '+', '.join('`'+n for n in new)+']')
(r/'formal/FullAudit.lean').write_text(audit)
for name in ['replay.py','package.py']:
 p=r/name;s=p.read_text()
 s=s.replace("'Profile','Result']", "'Profile','Result','Deficit','Baseline','Endpoint']")
 s=s.replace("['OriginAudit']", "['FullAudit']").replace("m!='OriginAudit'", "m!='FullAudit'")
 s=s.replace('logs/OriginAudit.log','logs/FullAudit.log')
 s=s.replace('PARTIAL_COMPONENT_SOURCE_ONLY_REPLAY_PASS','FULL_DENSITY_ENDPOINT_SOURCE_ONLY_REPLAY_PASS')
 s=s.replace("'full_target_proved':False", "'full_target_proved':True").replace("'source_claim_pass':False", "'source_claim_pass':True")
 s=s.replace('PARTIAL COMPONENT REPLAY PASS','FULL DENSITY ENDPOINT REPLAY PASS')
 if name=='package.py':
  s=s.replace("'SUMMARY.md','verify_inputs.py'", "'SUMMARY.md','frozen-before.json','verify_frozen.py','verify_inputs.py'")
  s=s.replace("files+=['inputs/PROOF.md'", "files+=['formal/OriginAudit.lean']\nfiles+=['inputs/PROOF.md'")
 else:
  s=s.replace("r=subprocess.run([sys.executable,str(dest/'verify_inputs.py')]", "r=subprocess.run([sys.executable,str(dest/'verify_frozen.py')],capture_output=True,text=True);assert r.returncode==0,r.stderr\nr=subprocess.run([sys.executable,str(dest/'verify_inputs.py')]")
 p.write_text(s)
