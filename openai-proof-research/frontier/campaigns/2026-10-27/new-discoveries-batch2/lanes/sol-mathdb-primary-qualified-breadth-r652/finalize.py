import pathlib,json,hashlib,subprocess,sys
L=pathlib.Path(__file__).resolve().parent
assert not (L/'final-verification-receipt.json').exists(),'Do not overwrite existing receipt'
excluded={'manifest.json','final-verification-receipt.json'}
files=[]
for p in sorted(L.rglob('*')):
    if p.is_file() and str(p.relative_to(L)) not in excluded:
        z=p.read_bytes();files.append(dict(path=str(p.relative_to(L)),size=len(z),sha256=hashlib.sha256(z).hexdigest()))
(L/'manifest.json').write_text(json.dumps(dict(excluded_exact_paths=sorted(excluded),files=files),indent=2)+'\n')
def verify(*flags):return subprocess.run([sys.executable,'-B',str(L/'verify.py'),*flags],capture_output=True,text=True)
p=verify();print(p.stdout,p.stderr);assert p.returncode==0
receipt=json.loads(p.stdout);neg=[]
for kind in ['hash','size','extra']:
    r=verify('--negative-'+kind);assert r.returncode!=0,(kind,r.stdout,r.stderr)
    neg.append(dict(test=kind,exit_code=r.returncode,stderr=r.stderr.strip(),method='virtual damaged bytes/file-set passed through actual verifier branch; no file mutation'))
receipt['subprocess_negative_tests']=neg
(L/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
r=verify();print(r.stdout,r.stderr);assert r.returncode==0
