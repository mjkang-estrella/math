"""Development entry point; final replay executes identical source in memory."""
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
AUTH = ROOT / "frontier/sources/i172_prescribed_square_switch/i171-authentication.json"
authenticated = json.loads(AUTH.read_bytes())
bindings = {e["path"]: e for entries in authenticated["checks"].values() for e in entries}
cache = {}


def load(path):
    if path not in cache:
        entry = bindings[path]
        data = (ROOT / path).read_bytes()
        assert len(data) == entry["size"]
        assert hashlib.sha256(data).hexdigest() == entry["sha256"]
        cache[path] = data
    return json.loads(cache[path])


namespace = dict(load=load, __name__="i172")
for name in ("toolkit.py", "research.py", "attacks.py"):
    path = HERE / name
    exec(compile(path.read_bytes(), str(path), "exec"), namespace)
result = namespace[sys.argv[1]]()
print(json.dumps(result, sort_keys=True, separators=(",", ":")))
