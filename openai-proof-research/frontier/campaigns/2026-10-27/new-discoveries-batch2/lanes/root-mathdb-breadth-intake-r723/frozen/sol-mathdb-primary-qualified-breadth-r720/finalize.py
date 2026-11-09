import pathlib,json,hashlib,subprocess,sys,datetime
P=pathlib.Path(__file__).resolve().parent
refs=json.loads((P/'flat-bindings.json').read_text())
for p in [P.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',P.parents[5]/'AGENTS.md',P.parent.parent/'AGENTS.md']:
 if p.is_file() and str(p) not in {e['path'] for e in refs}:
  b=p.read_bytes();refs.append({'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(P/'flat-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
excluded=['manifest.json','final-verification-receipt.json'];files=[]
for p in sorted(P.rglob('*')):
 if p.is_file() and str(p.relative_to(P)) not in excluded:
  b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(P/'manifest.json').write_text(json.dumps({'excluded_exact_paths':excluded,'files':files},indent=2)+'\n')
runs=[]
for arg in [None,'--negative-hash','--negative-size','--negative-extra']:
 p=subprocess.run([sys.executable,'-B',str(P/'verify.py')]+([arg] if arg else []),capture_output=True,text=True);runs.append({'case':arg or 'positive','exit_code':p.returncode,'stdout':p.stdout.strip(),'stderr':p.stderr.strip()});assert p.returncode==(1 if arg else 0),runs[-1]
b=(P/'manifest.json').read_bytes();receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'runs':runs,'negative_method':'Modify expectations in memory only: wrong hash, wrong size, and unlisted actual extra payload. Originals never mutated.','fixed_guard':'512MiB AS/groupRSS; CPU210s; wall230s; inherited unchanged','integrity_only':True}
(P/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
