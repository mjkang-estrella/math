import pathlib,json,hashlib,subprocess,datetime,sys
P=pathlib.Path(__file__).resolve().parent
excluded=['manifest.json','final-verification-receipt.json']
files=[]
for f in sorted(P.rglob('*')):
 if f.is_file() and str(f.relative_to(P)) not in excluded:
  b=f.read_bytes();files.append({'path':str(f.relative_to(P)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(P/'manifest.json').write_text(json.dumps({'excluded_exact_paths':excluded,'files':files},indent=2,sort_keys=True)+'\n')
results=[]
for mode in [None,'hash','size','extra']:
 cmd=[sys.executable,'-B',str(P/'verify.py')]+(['--negative',mode] if mode else [])
 r=subprocess.run(cmd,capture_output=True,text=True);assert r.returncode==(1 if mode else 0),(mode,r.stdout,r.stderr)
 results.append({'mode':mode or 'actual','exit_code':r.returncode,'stdout':r.stdout.strip(),'stderr':r.stderr.strip()})
b=(P/'manifest.json').read_bytes();receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest':{'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)},'tests':results,'integrity_only':True,'proposals':0,'credit':0}
(P/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n');print(json.dumps(receipt,indent=2))
