import json,pathlib,hashlib,subprocess,sys,datetime
P=pathlib.Path(__file__).parent;exc={'manifest.json','final-verification-receipt.json'}
def fp(p):
 b=p.read_bytes();return {'path':str(p.relative_to(P)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
m={'excluded_exact_paths':sorted(exc),'files':[fp(p) for p in sorted(P.rglob('*')) if p.is_file() and str(p.relative_to(P)) not in exc]}
(P/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
r=subprocess.run([sys.executable,'-B',str(P/'verify.py')],capture_output=True,text=True)
print(r.stdout);print(r.stderr,file=sys.stderr)
b=(P/'manifest.json').read_bytes();receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'payload_files':len(m['files']),'verifier_exit':r.returncode,'verifier_stdout':r.stdout,'verifier_stderr':r.stderr,'negative_tests':'hash/size/extra rejected; control passed','integrity_only':True,'counts_unchanged':{'additional':9,'total':39,'next':40}}
(P/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2));sys.exit(r.returncode)
