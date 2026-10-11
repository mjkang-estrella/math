"""Freeze the subsequently available parent receipt without changing inputs.json."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
HERE = Path(__file__).resolve().parent
path = "frontier/experiments/i178-parent-integration.json"
data = (ROOT / path).read_bytes()
receipt = json.loads(data)
assert receipt["status"] == "PASS" and receipt["scope_count"] == 100
assert receipt["retained_whitespace_warnings"] == []
replay = receipt["post_integration_replay"]
assert replay["status"] == "PASS" and len(replay["comparisons"]) == 2
assert all(x["byte_identical"] for x in replay["comparisons"])
assert len(replay["probes"]) == 8 and all(x["blocked"] for x in replay["probes"])
assert receipt["post_integration_stderr"] == "empty"
archive = json.loads((ROOT / "frontier/iterations/iteration179-path-recombination-factory-astra-task.json").read_bytes())
out = dict(
    strict=[dict(path=path, size=len(data), sha256=hashlib.sha256(data).hexdigest())],
    original_inputs_sha256=hashlib.sha256((HERE / "inputs.json").read_bytes()).hexdigest(),
    policy="Additive immutable supplement, before final diagnostics; no replacement of original freeze.",
    status="PASS", parent_final_integration_runtime=replay["runtime_seconds"],
    parent_dispatch_preflight=archive["prior_validation"]["post_integration_preflight"],
    note="27.945083369966596 initial parent replay, 28.125623729079962 dispatch preflight, "
         "27.958043999038637 final integration replay are distinct historical runs.")
with (HERE / "supplement.json").open("x") as f:
    json.dump(out, f, indent=2, sort_keys=True)
    f.write("\n")
print(json.dumps(out, indent=2))
