"""Fail-nonzero final verifier; no network, no writes. Run under the fixed guard."""
from pathlib import Path
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent
h=lambda b:hashlib.sha256(b).hexdigest()
def check(path,e):
 b=path.read_bytes();assert len(b)==e['size'] and h(b)==e['sha256'],str(path)
m=json.loads((P/'manifest.json').read_text())
actual={str(p.relative_to(P)) for p in P.rglob('*') if p.is_file() and p.name not in ('manifest.json','verification-receipt.json')}
assert actual=={e['path'] for e in m['files']}
for e in m['files']:check(P/e['path'],e)
for e in json.loads((P/'sourcebindings.json').read_text()):
 check(Path(e['original']),e);check(P/e['payload'],e)
# Verify ALL intake originals afresh, including files not scientifically consulted.
r=json.loads((P/'freeze.json').read_text()); intake=P.parent/'root-mathdb-circulant-intake-r375'
b=(intake/'manifest.json').read_bytes();assert h(b)==r['intake_manifest_sha256']
for e in json.loads(b)['files']:check(intake/e['path'],e)
# Re-extract retained PDF in memory; verify exact extraction used in the argument.
text=subprocess.check_output(['pdftotext','-layout',str(P/'inputs/01_body'),'-'])
assert text==(P/'source.txt').read_bytes()
for script,args in [('checker.py',['verify']),('upper.py',[])]:
 r=subprocess.run([sys.executable,'-B',str(P/script),*args],capture_output=True,text=True)
 assert r.returncode==0,(script,r.stdout,r.stderr)
 print(r.stdout.strip())
# Corrupt parity in memory; the scientific checker must reject it.
r=subprocess.run([sys.executable,'-B',str(P/'checker.py'),'negative'],capture_output=True,text=True)
assert r.returncode!=0 and 'AssertionError' in r.stderr
print(json.dumps(dict(status='PASS',payloads=len(m['files']),source_bindings=len(json.loads((P/'sourcebindings.json').read_text())),intake_originals=len(json.loads(b)['files']),negative_parity_test='rejected')))
