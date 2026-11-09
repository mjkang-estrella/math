from pathlib import Path
import hashlib,json,subprocess,sys,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'manifest.json').read_text())
assert 'manifest.json' not in manifest and 'verification-receipt.json' not in manifest
assert set(manifest)=={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in ['manifest.json','verification-receipt.json']}
def check():
 for name,digest in manifest.items():assert h(L/name)==digest,name
 for r in json.loads((L/'freeze.json').read_text()):assert h(Path(r['original']))==h(L/r['copy'])==r['before']==r['after']
check()
# Independent implementation replay. Deterministic output must preserve manifest hash.
subprocess.run([sys.executable,str(L/'independent_check.py')],check=True)
check()
receipt=dict(passed=True,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=h(L/'manifest.json'),files_verified=len(manifest),independent_coefficients=241,exact_strict_inequalities=True,scientific_originals_and_copies_before_after=True,candidate_manifest=json.loads((L/'candidate-manifest-audit.json').read_text()),acceptance=False,counts_unchanged=[9,39,40])
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt))
