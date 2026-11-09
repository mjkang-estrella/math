import hashlib, json
from pathlib import Path

R = Path(__file__).resolve().parent.parent
EXCLUDE = {"manifest.json", "verification-receipt.json"}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

files = sorted(str(p.relative_to(R)) for p in R.rglob("*") if p.is_file() and str(p.relative_to(R)) not in EXCLUDE)
manifest = {"lane": R.name, "files": [{"path": f, "sha256": sha(R / f), "size": (R / f).stat().st_size} for f in files]}
(R / "manifest.json").write_text(json.dumps(manifest, indent=1) + "\n")
print("manifest written:", len(files), "payloads")
