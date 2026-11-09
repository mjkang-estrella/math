import pathlib,json,hashlib,subprocess,datetime
P=pathlib.Path(__file__).resolve().parent
files=[]
for p in sorted(P.rglob('*')):
 if p.is_file() and p.name not in {'manifest.json','final-verification-receipt.json'}:
  b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(P/'manifest.json').write_text(json.dumps({'files':files,'excluded_exact_paths':['manifest.json','final-verification-receipt.json']},indent=2)+'\n')
results={}
for mode in ['--negative-hash','--negative-size','--negative-extra']:
 p=subprocess.run([str(P/'verify.sh'),mode],capture_output=True,text=True);assert p.returncode!=0,(mode,p.stdout);results[mode]={'exit_code':p.returncode,'stderr':p.stderr,'stdout':p.stdout,'injection':'in-memory only; no original or payload mutation'}
p=subprocess.run([str(P/'verify.sh')],capture_output=True,text=True);assert p.returncode==0,p.stderr
b=(P/'manifest.json').read_bytes();receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'payload_files':len(files),'positive':json.loads(p.stdout),'negative_rejection_tests':results,'guard_stderr':p.stderr,'integrity_not_science':True}
(P/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
