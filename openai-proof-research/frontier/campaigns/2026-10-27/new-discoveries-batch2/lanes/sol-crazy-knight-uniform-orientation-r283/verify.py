import pathlib,hashlib,json,datetime,subprocess,sys
L=pathlib.Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
manifest=json.loads((L/'MANIFEST.json').read_text())
assert not any(x['path'] in ['MANIFEST.json','verification-receipt.json'] for x in manifest)
expected={x['path'] for x in manifest}
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']}
assert expected==actual
def verify_manifest():
 for x in manifest:
  b=(L/x['path']).read_bytes();assert len(b)==x['bytes'] and H(b)==x['sha256'],x['path']
verify_manifest()
refs=json.loads((L/'bindings.json').read_text())+json.loads((L/'screen-bindings.json').read_text())
for b in refs:assert H(pathlib.Path(b['original']).read_bytes())==b['sha256'],b['original']
for x in json.loads((L/'local-source-bindings.json').read_text()):assert H((L/x['copy']).read_bytes())==x['sha256']
replays=[]
for script in ['checks.py','mixed.py']:
 p=subprocess.run([sys.executable,str(L/script)],capture_output=True,text=True,timeout=60)
 assert p.returncode==0,p.stderr
 replays.append(dict(script=script,exit=p.returncode,stdout_sha256=H(p.stdout.encode())))
verify_manifest()
assert not (L/'PROOF.md').exists()
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=H((L/'MANIFEST.json').read_bytes()),manifest_files=len(manifest),source_references_verified=len(refs),replays=replays,separate_guarded_invocation=True,limits='512MiB AS/groupRSS, CPU210s, wall230s; inherited unchanged',scope='Integrity and deterministic diagnostic replay only; not proof of Conjecture 2.3')
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
