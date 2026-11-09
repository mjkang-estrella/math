"""Extract the accompanying proof-sources.json into a new directory."""
import json
from pathlib import Path
p=Path(__file__).with_name("proof-sources.json")
out=Path("extracted-proof-sources")
out.mkdir(exist_ok=False)
for name, text in json.loads(p.read_text())["files"].items():
    q=Path(name)
    assert not q.is_absolute() and ".." not in q.parts
    target=out/q
    target.parent.mkdir(parents=True,exist_ok=True)
    target.write_text(text)
print(out.resolve())
