import pathlib,json,hashlib,subprocess,datetime
P=pathlib.Path(__file__).resolve().parent
excluded=['manifest.json','final-verification-receipt.json']
files=[]
for p in sorted(P.rglob('*')):
 if p.is_file() and str(p.relative_to(P)) not in excluded:
  b=p.read_bytes();files.append(dict(path=str(p.relative_to(P)),sha256=hashlib.sha256(b).hexdigest(),size=len(b)))
(P/'manifest.json').write_text(json.dumps(dict(excluded_exact_paths=excluded,files=files),indent=2)+'\n')
def run(*args):return subprocess.run(['python3','-B',str(P/'verify.py'),*args],capture_output=True,text=True,timeout=60)
r=run();assert r.returncode==0,r.stderr
negative=[]
for mode in ['hash','size','extra']:
 t=run('--inject',mode);assert t.returncode!=0,mode
 negative.append(dict(injected_fault=mode,exit_code=t.returncode,stderr=t.stderr.strip(),originals_mutated=False))
b=(P/'manifest.json').read_bytes();receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=hashlib.sha256(b).hexdigest(),manifest_size=len(b),verification=json.loads(r.stdout),negative_tests=negative,integrity_only=True,mathematics_or_novelty_pass=False)
(P/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
r=run();assert r.returncode==0,r.stderr
print(json.dumps(receipt,indent=2))
