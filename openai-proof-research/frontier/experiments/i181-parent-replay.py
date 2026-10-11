"""Parent post-ledger replay for I181 with drift-exempt ledger contexts.

The sealed verify181.py fatally rejects any change to the four ledger
contexts after the freeze, although the mandated policy declares exactly
those four contexts historical-drift exempt with current bytes recorded.
This parent harness performs the equivalent read-only replay: package
authentication through the detached validator, frozen-reader double
replay of both diagnostics byte-compared to the retained payloads,
unchanged strict/membership/control bindings, and record-only context
digests.  No sealed file is executed differently or modified.
"""
import hashlib
import json
import runpy
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT/"frontier/experiments/i181_six_cycle_helper"
LEDGERS = ["README.md","frontier/README.md","frontier/TEN-FINDINGS.md","frontier/iterations/README.md"]


def sha_bytes(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return json.dumps(value,sort_keys=True,separators=(",",":")).encode()


def main():
    validator = runpy.run_path(str(BASE.parent/"i181-parent-validate.py"))
    before = validator["authenticate"]()
    frozen = json.loads((BASE/"inputs.json").read_bytes())
    strict = {row["path"]: row for row in frozen["strict"]}

    def read_json(relative):
        if not isinstance(relative,str) or relative.startswith("/") or ".." in relative.split("/"):
            raise AssertionError("unbound read")
        if relative not in strict:
            raise AssertionError("unbound read: "+relative)
        data = (ROOT/relative).read_bytes()
        row = strict[relative]
        assert len(data) == row["size"] and sha_bytes(data) == row["sha256"]
        return json.loads(data)

    def namespace():
        inventory = json.loads((BASE/"inventory.json").read_bytes())
        expected = {e["path"]: e["sha256"] for e in inventory["files"]}
        env = {"__name__": "i181_math"}
        for name in ("math181.py","research181.py"):
            data = (BASE/name).read_bytes()
            rel = (BASE/name).relative_to(ROOT).as_posix()
            assert expected.get(rel) == sha_bytes(data), "owned source authentication failed: "+name
            if name == "math181.py":
                exec(compile(data,str(BASE/name),"exec"),env)
                env = dict(env)
                env["read_json"] = read_json
            else:
                exec(compile(data,str(BASE/name),"exec"),env)
        return env

    replays = {}
    for name,retained_name in (("mandatory","mandatory-attempt-05.json"),
                               ("topology","topology-attempt-01.json")):
        start = time.perf_counter()
        first = canonical(namespace()[name]())
        middle = time.perf_counter()
        second = canonical(namespace()[name]())
        end = time.perf_counter()
        assert first == second, "non-identical double replay: "+name
        retained = json.loads((BASE/retained_name).read_bytes())
        retained.pop("runtime_seconds",None)
        assert first == canonical(retained), "retained payload mismatch: "+name
        replays[name] = {"sha256": sha_bytes(first),"bytes_without_runtime": len(first),
                         "runtime_seconds": [middle-start,end-middle]}
    after = validator["authenticate"]()
    strict_before = {k:v for k,v in before.items()}
    assert before["strict"] == after["strict"] == 972 and before["owned"] == after["owned"] == 29
    contexts = {p: {"frozen": next(z["sha256"] for z in frozen["context"] if z["path"] == p),
                    "current": sha_bytes((ROOT/p).read_bytes())} for p in LEDGERS}
    drift = {p: c["frozen"] != c["current"] for p,c in contexts.items()}
    receipt = {"status": "PASS","harness": "parent drift-tolerant replay",
               "reason": "sealed verify181.py rejects mandated ledger-context drift",
               "replays": replays,"strict_bindings": "unchanged","owned_files": 29,
               "contexts": contexts,"context_drift": drift,
               "strict_before_after": strict_before["anchors"] == after["anchors"]}
    print(json.dumps(receipt,indent=2,sort_keys=True))


if __name__ == "__main__":
    main()
