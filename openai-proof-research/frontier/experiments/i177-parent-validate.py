"""Detached I177 authentication and exclusive parent replay receipts."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "frontier/experiments/i177_adjacent_port_surgery"
REPORT = ROOT / "frontier/iterations/i177-adjacent-port-surgery.md"
ANCHORS = {
    REPORT: "4c37997b83da3238793a9850742fb4daac188442cbeeaf4a864a3af2cc01d8a3",
    BASE / "seal.json": "1ffbf11ad4970094ac4cffb75519c4b5267b72430cb27f2009e79db98abcbd9f",
    BASE / "verify177.py": "15c8c3be562d4723e1c1a33befb646042ac17271a224c217025789b6d25f3c5c",
}
CONTEXT = {"README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_bytes())


def save(name, value):
    with (BASE.parent / ("i177-parent-"+name+".json")).open("x") as out:
        json.dump(value, out, indent=2, sort_keys=True)
        out.write("\n")


def authenticate():
    for p, h in ANCHORS.items():
        assert sha(p) == h, p
    inv, seal, pre = (read(BASE / name) for name in ("inventory.json", "seal.json", "prevalidation.json"))
    for name in ("inventory", "prevalidation"):
        assert sha(BASE / (name+".json")) == seal[name+"_sha256"]
    assert pre["status"] == "PASS" and pre["stderr_empty"] and pre["prevalidation"]
    for field in ("inventory_sha256", "report_sha256", "verifier_sha256"):
        assert pre[field] == seal[field]
    assert seal["report_sha256"] == ANCHORS[REPORT]
    assert seal["verifier_sha256"] == ANCHORS[BASE / "verify177.py"]
    controls = {BASE / n for n in ("inventory.json", "prevalidation.json", "seal.json")}
    assert {ROOT / n for n in inv["controls"]} == controls
    actual = {REPORT}
    for d in (BASE, ROOT / "frontier/sources/i177_adjacent_port_surgery"):
        actual |= {p for p in d.rglob("*") if p.is_file()}
    assert actual - controls == {ROOT / z["path"] for z in inv["owned"]}
    entries = inv["owned"] + inv["external"]
    assert len(entries) == len({z["path"] for z in entries})
    assert len(inv["context"]) == 4 and {z["path"] for z in inv["context"]} == CONTEXT
    assert not CONTEXT & {z["path"] for z in entries}
    for z in entries:
        p = ROOT / z["path"]
        assert p.resolve().is_relative_to(ROOT) and not p.is_symlink()
        assert sha(p) == z["sha256"] and p.stat().st_size == z["size"], z["path"]
    contexts = [dict(path=z["path"], actual=sha(ROOT / z["path"]),
                     inventory=z["sha256"], inherited=z["I176_historical"])
                for z in inv["context"]]
    for replay in inv["replays"]:
        assert any(r["function"] == replay["function"] and r["byte_identical"]
                   and r["sha256"] == sha(ROOT / replay["payload"]) for r in pre["comparisons"])
    assert len(pre["probes"]) == 8 and all(p["blocked"] for p in pre["probes"])
    assert len(inv["owned"]) == 78 and len(inv["external"]) == 585
    return dict(status="PASS", owned=78, non_context_external=585, external_context_total=589,
                contexts=contexts, anchors={str(p.relative_to(ROOT)): h for p, h in ANCHORS.items()})


def main():
    before = authenticate()
    save("precheck", before)
    stdout, stderr = (BASE.parent / ("i177-parent-replay-"+n) for n in ("stdout.json", "stderr.txt"))
    with stdout.open("xb") as out, stderr.open("xb") as err:
        run = subprocess.run([sys.executable, "-I", "-B", str(BASE / "verify177.py")],
                             cwd=ROOT, stdout=out, stderr=err, timeout=1200)
    assert run.returncode == 0 and not stderr.read_bytes()
    result = read(stdout)
    assert result["status"] == "PASS" and not result["prevalidation"]
    assert result["seal_sha256"] == ANCHORS[BASE / "seal.json"]
    assert len(result["comparisons"]) == 3 and all(z["byte_identical"] for z in result["comparisons"])
    assert len(result["probes"]) == 8 and all(z["blocked"] for z in result["probes"])
    after = authenticate()
    assert before == after
    save("verification", dict(status="PASS", replay=result, postcheck=after, stderr="empty",
         context_policy="Historical context drift permitted; current bytes frozen during execution.",
         clean_clone_reconstruction="not tested"))
    print("Parent replay PASS", result["runtime_seconds"], "seconds; 78 owned, 585 external, four contexts")


if __name__ == "__main__":
    main()
