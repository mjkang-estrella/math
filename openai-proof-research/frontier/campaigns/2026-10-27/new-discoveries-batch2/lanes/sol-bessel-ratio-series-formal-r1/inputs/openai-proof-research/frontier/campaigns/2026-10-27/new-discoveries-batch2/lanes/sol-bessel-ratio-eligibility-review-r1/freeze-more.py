from pathlib import Path
import hashlib,json
O=Path(__file__).parent; C=O.parent.parent; paths=[C/'candidates'/n/'PROOF.md' for n in ['arcsinh-positive','gamma-level-convexity']]; records=json.loads((O/'input-freeze.json').read_text())
for p in paths:
 h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
 before=h(p); dest=O/'inputs'/p.relative_to(Path.cwd()) if p.is_absolute() else O/'inputs'/p
 dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(p.read_bytes()); records.append(dict(path=str(p.resolve()),copy=str(dest.relative_to(O)),sha256_before=before,sha256_copy=h(dest),sha256_after=h(p),match=before==h(dest)==h(p)))
(O/'input-freeze.json').write_text(json.dumps(records,indent=2))
for p in paths:print((O/'inputs'/p).read_text())
