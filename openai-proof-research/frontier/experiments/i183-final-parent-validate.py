"""Detached byte/control authentication and read-only I183 final replay.

No child implementation is loaded before authentication. Historical
contexts may drift; their current bytes must remain stable during replay.
"""
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = "frontier/experiments/i183_cptp_finalization"
SOURCE = "frontier/sources/i183_cptp_finalization"
REPORT = "frontier/iterations/i183-cptp-finalization.md"
CONTEXT = ("README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md")
ANCHORS = {
    REPORT: "be011c8f9ae99899ad6c2ae4fa2cd4c1b882e6750e07b4c7ad4dc859527abd35",
    BASE + "/seal.json": "b3450f344ef4e173cd5bae916f5ead7bf066675698033080b6386b73d8f057f8",
    BASE + "/verify.py": "9f0781077de3699a891a5e1bc843d7bfa14cf51071919509d6e50352405d883d",
}
ORDER = [0, 520, 522, 524, 527, 528, 530, 533, 534, 536, 539, 431,
         "C171", "G6/G10", "first_P8", "I176_k6", "I177_child_absorption",
         "I178_relations_completion", "I179_lock", "parent_helper",
         "I180_helpergraph", "I181_patch_reattachment", "I182_reduction_finite"]


def path(name):
    p = Path(name)
    assert not p.is_absolute() and ".." not in p.parts
    full = ROOT / p
    assert full.resolve().is_relative_to(ROOT) and not full.is_symlink()
    return full


def row(name):
    data = path(name).read_bytes()
    return {"path": name, "size": len(data),
            "sha256": hashlib.sha256(data).hexdigest()}


def load(name):
    return json.loads(path(name).read_bytes())


def members(directories, extra=()):
    found = set(extra)
    for directory in directories:
        for p in path(directory).rglob("*"):
            assert not p.is_symlink()
            if p.is_file():
                found.add(p.relative_to(ROOT).as_posix())
    return sorted(found)


def authenticate():
    for name, sha in ANCHORS.items():
        assert row(name)["sha256"] == sha, name
    inventory = load(BASE + "/inventory.json")
    frozen = load(BASE + "/inputs.json")
    seal = load(BASE + "/seal.json")
    pre = load(BASE + "/prevalidation.json")
    owned, strict = inventory["owned"], frozen["strict"]
    assert (len(owned), len(strict)) == (562, 1153)
    assert inventory["controls"] == [
        BASE + "/" + n for n in ("inventory.json", "prevalidation.json",
                                "prevalidation.stderr", "seal.json")]
    assert inventory["status"] == "I183_BOUNDED_FINALIZATION"
    for population in (owned, strict):
        assert len({x["path"] for x in population}) == len(population)
        for item in population:
            assert row(item["path"]) == item, item["path"]
    assert members((BASE, SOURCE), (REPORT,)) == sorted(
        [x["path"] for x in owned] + inventory["controls"])
    strict_paths = {x["path"] for x in strict}
    assert not strict_paths.intersection(CONTEXT)
    assert {x["path"] for x in frozen["context"]} == set(CONTEXT)
    for chain in frozen["parent_membership"] + [frozen["checkpoint_membership"]]:
        assert members(chain["directories"], chain["extra"]) == chain["members"]
        assert set(chain["members"]) <= strict_paths
    for name, sha in frozen["anchors"].items():
        assert row(name)["sha256"] == sha
    for key, name in (
            ("inventory_sha256", BASE + "/inventory.json"),
            ("prevalidation_sha256", BASE + "/prevalidation.json"),
            ("prevalidation_stderr_sha256", BASE + "/prevalidation.stderr"),
            ("report_sha256", REPORT), ("verifier_sha256", BASE + "/verify.py"),
            ("mandatory_payload_sha256", BASE + "/mandatory-01.json")):
        assert seal[key] == row(name)["sha256"]
        if key in pre:
            assert pre[key] == seal[key]
    assert pre["status"] == "PASS_PREVALIDATION_23_STAGES"
    assert pre["full_mandatory_replay"] and pre["order"] == ORDER
    assert pre["seal_link_pretests"] == 5
    assert path(BASE + "/prevalidation.stderr").read_bytes() == b""
    # Final preparation snapshots must all equal the finalized scripts.
    snapshots = 0
    for invocation in path(BASE).glob("*-invocation.json"):
        obj = json.loads(invocation.read_bytes())
        for item in obj["sources"]:
            assert row(item["path"]) == item
            snapshots += 1
            if invocation.name in {
                    "inventory-invocation.json", "prevalidation-invocation.json",
                    "seal-invocation.json", "final-replay-invocation.json"}:
                assert path(item["path"]).read_bytes() == (
                    path(BASE) / Path(item["path"]).name).read_bytes()
    mandatory = load(BASE + "/mandatory-01.json")
    assert mandatory["status"] == "PASS_23_BOUNDED_STAGES"
    assert mandatory["order"] == ORDER and mandatory["E183"] == "UNRESOLVED"
    reduction = mandatory["results"]["reduction"]
    assert reduction["reduction_checks"] == 626 and len(reduction["instances"]) == 6
    return {"owned": len(owned), "strict": len(strict), "snapshot_rows": snapshots,
            "current_context": [row(p) for p in CONTEXT],
            "context_drift": [x["path"] for x in frozen["context"] if row(x["path"]) != x],
            "anchors": ANCHORS}


def replay():
    before = authenticate()
    start = time.monotonic()
    proc = subprocess.run([sys.executable, "-I", "-B", str(path(BASE + "/verify.py"))],
                          cwd=ROOT, capture_output=True, timeout=180)
    result = {"returncode": proc.returncode, "elapsed_seconds": time.monotonic() - start}
    assert proc.returncode == 0 and proc.stderr == b"", proc.stderr.decode()
    data = json.loads(proc.stdout)
    assert data["status"] == "PASS_SEALED_23_STAGES"
    assert data["sealed"] and data["full_mandatory_replay"] and data["order"] == ORDER
    assert data["owned"] == 562 and data["strict"] == 1153
    assert data["forgery_positive_control"]
    assert {p["probe"] for p in data["eight_live_probes"]} == {
        "write", "mutation", "network", "subprocess", "unbound-read",
        "outside-compile", "outside-exec", "forged-owned-source"}
    assert all(p["status"] == "BLOCKED" for p in data["eight_live_probes"])
    assert authenticate() == before
    result.update(status="PASS", authentication=before, replay=data,
                  scope="All bounded controls, not a universal E183 verdict")
    return result, proc


if __name__ == "__main__":
    assert sys.flags.isolated and sys.dont_write_bytecode
    assert sys.argv[1:] == []
    result, process = replay()
    prefix = "frontier/experiments/i183-final-parent-replay"
    for suffix, data in ((".stdout", process.stdout), (".stderr", process.stderr)):
        with path(prefix + suffix).open("xb") as out:
            out.write(data)
    with path(prefix + ".json").open("x") as out:
        json.dump(result, out, sort_keys=True, indent=2)
        out.write("\n")
    print(json.dumps({k: result[k] for k in ("status", "elapsed_seconds", "scope")}))
