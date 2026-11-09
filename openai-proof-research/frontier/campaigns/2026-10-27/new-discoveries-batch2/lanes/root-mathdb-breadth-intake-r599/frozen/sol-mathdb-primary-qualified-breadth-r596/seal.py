import pathlib,json,hashlib,subprocess,sys,datetime
L=pathlib.Path(__file__).resolve().parent
files=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in {'manifest.json','final-verification-receipt.json'}:
  b=p.read_bytes();files.append({'path':str(p.relative_to(L)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(L/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files},indent=2)+'\n')
results=[]
for mode in [None,'--negative-hash','--negative-size','--negative-extra']:
 p=subprocess.run([sys.executable,'-B',str(L/'verify.py')]+([mode] if mode else []),capture_output=True,text=True,timeout=40)
 results.append({'mode':mode or 'actual','exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
 assert p.returncode==(1 if mode else 0),results[-1]
b=(L/'manifest.json').read_bytes();receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'verification':results,'guard':'unchanged fixed helper_guard.py;512MiB AS/groupRSS,CPU210s,wall230s','scope':'Integrity PASS only; math/novelty HOLD'}
(L/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
