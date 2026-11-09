import pathlib,json,hashlib,subprocess,os,datetime
P=pathlib.Path(__file__).resolve().parent
files=[]
for p in sorted(P.rglob('*')):
 if p.is_file() and p.name not in {'manifest.json','final-verification-receipt.json'}:
  b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(P/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files},indent=2)+'\n')
# Already under the fixed guard; this read-only child inherits its limits/group.
r=subprocess.run(['python3','-B',str(P/'verify.py')],capture_output=True,text=True)
if r.returncode:print(r.stderr);raise SystemExit(r.returncode)
d=json.loads(r.stdout);d['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();d['guard_limits']={'AS_and_groupRSS_MiB':512,'CPU_seconds':210,'wall_seconds':230};d['verifier_exit']=r.returncode
(P/'final-verification-receipt.json').write_text(json.dumps(d,indent=2)+'\n');print(json.dumps(d))
