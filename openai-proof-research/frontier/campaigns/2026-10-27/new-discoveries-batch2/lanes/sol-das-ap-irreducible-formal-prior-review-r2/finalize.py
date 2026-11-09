from pathlib import Path
import json,hashlib,subprocess,sys
B=Path(__file__).resolve().parent;R=B/'replay'
p=subprocess.run([sys.executable,str(R/'verify_pins.py')],cwd=R,capture_output=True,text=True,check=True)
pins=json.loads(p.stdout); mf=Path(json.loads((R/'pins.json').read_text())['manifest_original'])
paths=[x.name for x in (mf.parent/'.lake/packages').iterdir() if (x/'.lake/build/lib/lean').is_dir()]
assert set(paths)<=set(pins['package_heads'])
pins['available_package_build_paths']=paths
(B/'pins-verification.json').write_text(json.dumps(pins,indent=2))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest={str(p.relative_to(B)):sha(p) for p in sorted(B.rglob('*')) if p.is_file() and p.name not in ['manifest.json','receipt.json']}
(B/'manifest.json').write_text(json.dumps(manifest,indent=2))
print(dict(manifest_files=len(manifest)))
