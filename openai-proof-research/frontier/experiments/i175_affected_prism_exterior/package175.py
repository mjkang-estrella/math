"""Finalize inventory first, prevalidate, and exclusively seal once."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

EXP = Path(__file__).resolve().parent
ROOT = EXP.parents[2]
PREFIX = "frontier/experiments/i175_affected_prism_exterior/"
SPREFIX = "frontier/sources/i175_affected_prism_exterior/"
REPORT = "frontier/iterations/i175-affected-prism-exterior.md"
CONTROLS = [PREFIX+x for x in ("inventory.json", "prevalidation.json", "seal.json")]


def sha(b):
    return hashlib.sha256(b).hexdigest()


def encoded(obj):
    return (json.dumps(obj, sort_keys=True, indent=2)+"\n").encode()


def exclusive(path, content):
    with path.open("xb") as f:
        f.write(content)


assert not (EXP / "seal.json").exists(), "Never reseal"
assert not (EXP / "prevalidation.json").exists(), "Successful prevalidation already exists"
assert not (EXP / "inventory.json").exists(), "Preserve any failed inventory before another build"
authentication = json.loads((ROOT / (SPREFIX+"authentication.json")).read_bytes())
extra = json.loads((ROOT / (SPREFIX+"additional-inputs.json")).read_bytes())
external = {x["path"]: x for x in authentication["bindings"]}
for x in extra:
    assert x["path"] not in external or external[x["path"]] == x
    external[x["path"]] = x
for x in external.values():
    b = (ROOT / x["path"]).read_bytes()
    assert sha(b) == x["sha256"] and len(b) == x["size"], x["path"]
context = []
for x in authentication["context"]:
    b = (ROOT / x["path"]).read_bytes()
    assert sha(b) == x["actual"], "No late parent-document/context transition allowed"
    context.append({"path": x["path"], "sha256": sha(b), "size": len(b),
                    "I174_inherited": x["current"]})
owned_names = {REPORT}
for prefix in (PREFIX, SPREFIX):
    for p in (ROOT / prefix).rglob("*"):
        assert not p.is_symlink()
        if p.is_file():
            owned_names.add(str(p.relative_to(ROOT)))
owned = []
for name in sorted(owned_names-set(CONTROLS)):
    b = (ROOT / name).read_bytes()
    owned.append({"path": name, "sha256": sha(b), "size": len(b)})
replays = []
for stage in ("mandatory", "historical", "experiment", "boundary", "local_saturation"):
    attempts = sorted(EXP.glob(stage+"-attempt-*-receipt.json"))
    latest = json.loads(attempts[-1].read_bytes())
    assert latest["status"] == "PASS"
    payload = str(attempts[-1].relative_to(ROOT)).replace("-receipt.json", ".json")
    assert sha((ROOT / payload).read_bytes()) == latest["payload_sha256"]
    replays.append({"function": stage, "payload": payload})
inv = {"iteration": 175, "controls": CONTROLS, "owned": owned,
       "external": [external[p] for p in sorted(external)], "context": context,
       "replays": replays, "policy": "Immutable-first; only four named contexts; no ancestor execution"}
exclusive(EXP / "inventory.json", encoded(inv))
run = subprocess.run([sys.executable, "-I", "-B", str(EXP / "verify175.py"), "--prevalidate"],
                     stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
if run.returncode or run.stderr:
    # The failed inventory and all source stages must survive. These captures
    # will need inclusion in a fresh, still-unsealed complete inventory.
    stamp = time.time_ns()
    for suffix, b in [("stdout.txt", run.stdout), ("stderr.txt", run.stderr),
                      ("inventory.json.disabled", encoded(inv))]:
        exclusive(EXP / f"prevalidation-failure-{stamp}-{suffix}", b)
    for name in ("verify175.py", "package175.py", "math175.py", "research175.py"):
        exclusive(EXP / f"prevalidation-failure-{stamp}-{name}.disabled", (EXP / name).read_bytes())
    raise AssertionError(("Prevalidation failed; preserve inventory before rebuilding", run.stderr.decode()))
pre = json.loads(run.stdout)
assert pre["status"] == "PASS"
pre["stderr"] = "empty"
exclusive(EXP / "prevalidation.json", encoded(pre))
seal = {"iteration": 175, "inventory_sha256": sha((EXP / "inventory.json").read_bytes()),
        "prevalidation_sha256": sha((EXP / "prevalidation.json").read_bytes()),
        "report_sha256": sha((ROOT / REPORT).read_bytes()),
        "verifier_sha256": sha((EXP / "verify175.py").read_bytes()),
        "creation": "Exclusive single seal after successful prevalidation; never reseal"}
exclusive(EXP / "seal.json", encoded(seal))
print(json.dumps({"status": "SEALED", "owned": len(owned), "external": len(external),
                  "contexts": len(context), "prevalidation_seconds": pre["runtime_seconds"],
                  "seal_sha256": sha((EXP / "seal.json").read_bytes()), **seal}, sort_keys=True))
