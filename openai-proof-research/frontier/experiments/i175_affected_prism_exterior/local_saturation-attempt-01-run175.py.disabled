"""Preserve every mathematical source stage and all captures, including failures."""
import hashlib
import json
from pathlib import Path
import sys
import time
import traceback
from types import MappingProxyType

EXP = Path(__file__).resolve().parent
ROOT = EXP.parents[2]
SRC = ROOT / "frontier/sources/i175_affected_prism_exterior"
stage = sys.argv[1]
attempt = 1
while (EXP / f"{stage}-attempt-{attempt:02d}-receipt.json").exists():
    attempt += 1
prefix = f"{stage}-attempt-{attempt:02d}"
source = {}
for name in ("authenticate.py", "math175.py", "research175.py", "run175.py"):
    b = (EXP / name).read_bytes()
    source[name] = b
    with (EXP / f"{prefix}-{name}.disabled").open("xb") as f:
        f.write(b)
receipt = json.loads((SRC / "authentication.json").read_bytes())
memory = {}
for item in receipt["bindings"]:
    b = (ROOT / item["path"]).read_bytes()
    assert len(b) == item["size"] and hashlib.sha256(b).hexdigest() == item["sha256"], item["path"]
    memory[item["path"]] = b
ns = {"INPUT": MappingProxyType(memory)}
start = time.perf_counter()
payload, error, status = b"", b"", "FAIL"
try:
    for name in ("math175.py", "research175.py"):
        exec(compile(source[name], str(EXP / name), "exec"), ns)
    # Prerequisites precede every later diagnostic.
    mandatory = ns["mandatory"]()
    result = mandatory if stage == "mandatory" else ns[stage]()
    payload = (json.dumps(result, sort_keys=True, indent=2)+"\n").encode()
    status = "PASS"
except BaseException:
    error = traceback.format_exc().encode()
for suffix, b in [(".json", payload), ("-stderr.txt", error)]:
    with (EXP / (prefix+suffix)).open("xb") as f:
        f.write(b)
record = {"stage": stage, "attempt": attempt, "status": status,
          "seconds": time.perf_counter()-start, "payload_sha256": hashlib.sha256(payload).hexdigest()}
with (EXP / (prefix+"-receipt.json")).open("x") as f:
    json.dump(record, f, sort_keys=True, indent=2)
    f.write("\n")
print(json.dumps(record))
if error:
    print(error.decode(), file=sys.stderr)
    sys.exit(1)
