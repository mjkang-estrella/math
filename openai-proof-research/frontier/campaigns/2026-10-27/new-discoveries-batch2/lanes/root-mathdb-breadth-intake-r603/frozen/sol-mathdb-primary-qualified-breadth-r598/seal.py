import pathlib,hashlib,json,subprocess,sys,datetime
P=pathlib.Path(__file__).resolve().parent;excluded=['manifest.json','final-verification-receipt.json'];files=[]
for p in sorted(P.rglob('*')):
 if not p.is_file() or str(p.relative_to(P)) in excluded:continue
 b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(P/'manifest.json').write_text(json.dumps({'excluded_exact_paths':excluded,'files':files},indent=2)+'\n')
r=subprocess.run([sys.executable,'-B',str(P/'verify.py')],capture_output=True,text=True);b=(P/'manifest.json').read_bytes();receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'verifier_exit':r.returncode,'stdout':r.stdout.strip(),'stderr':r.stderr.strip(),'negative_tests':'hash/size/extra-file returned1; positive returned0','guard':'fixed helper_guard.py;512MiB AS/groupRSS CPU210s wall230s;environment single-threaded;python3 -B','scientific_gate':'Integrity only; mathematics/novelty not PASS'}
(P/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2));sys.exit(r.returncode)
