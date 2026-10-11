"""Detached parent authentication and sealed replay. Never reseals evidence."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "frontier/experiments/i173_brace_high_loss_octagons"
SOURCES = ROOT / "frontier/sources/i173_brace_high_loss_octagons"
REPORT = ROOT / "frontier/iterations/i173-brace-high-loss-octagons.md"
OUT = BASE.parent
ANCHORS = {
    REPORT: "e06169dc4b72c42da7a26797eb73f8368222dc9e7d87290c909af7c243c52fc2",
    BASE / "seal.json": "6b824bffc72019f3c75dee02c70c1f0173b557cffc4275177f35bcb76356e609",
    BASE / "verify.py": "0d3db09c92da4b5c59a164a97daf05039660c16702096b95a9c8bf43e7f4778a",
}
CONTEXT = {"README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(name):
    return json.loads((BASE / name).read_bytes())


def save(name, value):
    with (OUT / name).open("x") as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write("\n")


def authenticate():
    for path, expected in ANCHORS.items():
        assert digest(path) == expected, str(path)
    inv, seal, pv = read("inventory.json"), read("seal.json"), read("prevalidation.json")
    assert seal["inventory_sha256"] == digest(BASE / "inventory.json")
    assert seal["prevalidation_sha256"] == digest(BASE / "prevalidation.json")
    assert pv["status"] == "PASS" and pv["prevalidation"] is True
    for field in ("inventory_sha256", "report_sha256", "verifier_sha256"):
        assert pv[field] == seal[field]
    assert seal["report_sha256"] == ANCHORS[REPORT]
    assert seal["verifier_sha256"] == ANCHORS[BASE / "verify.py"]
    controls = {BASE / n for n in ("inventory.json", "prevalidation.json", "seal.json")}
    actual = {REPORT} | {p for d in (BASE, SOURCES) for p in d.rglob("*") if p.is_file()}
    listed = {ROOT / z["path"] for z in inv["owned"]}
    assert len(listed) == len(inv["owned"]) and listed == actual - controls
    assert {z["path"] for z in inv["context"]} == CONTEXT
    assert len(inv["context"]) == 4
    assert not CONTEXT & {z["path"] for z in inv["owned"] + inv["external"]}
    for z in inv["owned"] + inv["external"]:
        path = ROOT / z["path"]
        assert path.resolve().is_relative_to(ROOT) and not path.is_symlink()
        assert digest(path) == z["sha256"] and path.stat().st_size == z["size"], z["path"]
    contexts = [dict(path=z["path"], expected=z["sha256"],
                     actual=digest(ROOT / z["path"]),
                     drift=digest(ROOT / z["path"]) != z["sha256"])
                for z in inv["context"]]
    assert len(inv["owned"]) == 62 and len(inv["external"]) == 205
    return dict(status="PASS", owned=62, non_context_external=205, external_total=209,
                contexts=contexts, anchors={str(p.relative_to(ROOT)): v for p, v in ANCHORS.items()},
                inventory_sha256=digest(BASE / "inventory.json"))


def main():
    before = authenticate()
    save("i173-parent-precheck.json", before)
    print("Parent precheck PASS: 62 owned, 205 non-context external, four contexts", flush=True)
    stdout, stderr = OUT / "i173-parent-replay-stdout.json", OUT / "i173-parent-replay-stderr.txt"
    with stdout.open("xb") as out, stderr.open("xb") as err:
        run = subprocess.run([sys.executable, "-I", "-B", str(BASE / "verify.py")],
                             cwd=ROOT, stdout=out, stderr=err, timeout=1200, check=False)
    assert run.returncode == 0, run.returncode
    result = json.loads(stdout.read_bytes())
    assert result["status"] == "PASS" and not result["prevalidation"]
    assert result["seal_sha256"] == ANCHORS[BASE / "seal.json"]
    assert len(result["comparisons"]) == 6 and all(z["byte_identical"] for z in result["comparisons"])
    assert len(result["probes"]) == 8 and all(z["blocked"] for z in result["probes"])
    assert stderr.read_bytes() == b""
    after = authenticate()
    assert before == after, "Bindings or contexts changed during parent replay"
    save("i173-parent-verification.json", dict(
        status="PASS", replay=result, postcheck=after, stderr="empty",
        limits="Authenticated in-memory replay, not OS sandboxing; clean-clone reconstruction not tested."))
    print("Parent sealed replay PASS", result["runtime_seconds"], flush=True)


if __name__ == "__main__":
    main()
