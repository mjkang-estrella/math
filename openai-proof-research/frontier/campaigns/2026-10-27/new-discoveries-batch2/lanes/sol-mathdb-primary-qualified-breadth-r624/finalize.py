from pathlib import Path
import json,hashlib,datetime,subprocess,sys
D=Path(__file__).resolve().parent
# Add the original institutional source provenance, with no refetch.
p=D.parent/'sol-mathdb-primary-qualified-breadth-r400/source-provenance.json'
log=json.loads((D/'source-provenance.json').read_text())
log=[x for x in log if x.get('kind')!='reused_snapshot']
x=json.loads(p.read_text())[0];log.append({'kind':'reused_snapshot','original_provenance_path':str(p),'original':x,'coverage':'Selected review theorem/problem passages only; no whole-body/dependency/registry clearance.'})
(D/'source-provenance.json').write_text(json.dumps(log,indent=2)+'\n')
files=[]
for p in sorted(D.rglob('*')):
 if not p.is_file() or p.name in ['manifest.json','final-verification-receipt.json']:continue
 b=p.read_bytes();files.append({'path':str(p.relative_to(D)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(D/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files},indent=2)+'\n')
r=subprocess.run([sys.executable,'-B',str(D/'verify.py')],capture_output=True,text=True)
b=(D/'manifest.json').read_bytes();receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'verifier_exit':r.returncode,'verifier_output':r.stdout.strip(),'verifier_stderr':r.stderr.strip(),'limits':'512MiB AS/groupRSS; CPU210s; wall230s unchanged; enclosing fixed helper guard','integrity_only':True}
(D/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));sys.exit(r.returncode)
