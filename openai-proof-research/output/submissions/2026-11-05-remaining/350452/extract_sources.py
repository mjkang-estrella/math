import json, base64, gzip
from pathlib import Path
data = json.loads(Path(__file__).with_name("proof-sources.json").read_text())
out = Path("extracted-proof-sources")
out.mkdir(exist_ok=False)
for name, encoded in data["files"].items():
    rel = Path(name)
    assert not rel.is_absolute() and ".." not in rel.parts
    target = out / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(gzip.decompress(base64.b64decode(encoded)))
print(out.resolve())
