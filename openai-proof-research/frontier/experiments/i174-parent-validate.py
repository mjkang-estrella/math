"""Detached parent authentication, transition verification and sealed replay."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "frontier/experiments/i174_prism_gadget_survival"
SOURCE = ROOT / "frontier/sources/i174_prism_gadget_survival"
REPORT = ROOT / "frontier/iterations/i174-prism-gadget-survival.md"
ANCHORS = {
    REPORT: "5690d67776a455018d1906ba778ce6b4e3afd8258cbbaeb8b2e1f7e66bff8cca",
    BASE / "seal.json": "b63e358e0506567a2098d61dfe164a2f2b4db721488105d16dd238cdc06886ef",
    BASE / "verify.py": "2a9df59029ea699daab69d4355e8934faf2791c230a6775102fb2e8e00aa4e83",
}
CONTEXT = {"README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_bytes())


def save(name, value):
    with (BASE.parent / name).open("x") as out:
        json.dump(value, out, indent=2, sort_keys=True)
        out.write("\n")


def authenticate():
    for p, h in ANCHORS.items():
        assert sha(p) == h, str(p)
    inv, seal, pre = (read(BASE / name) for name in ("inventory.json", "seal.json", "prevalidation.json"))
    assert sha(BASE / "inventory.json") == seal["inventory_sha256"]
    assert sha(BASE / "prevalidation.json") == seal["prevalidation_sha256"]
    assert pre["status"] == "PASS" and pre["stderr"] == ""
    assert pre["result"]["status"] == "PASS" and pre["result"]["prevalidation"]
    for field in ("inventory_sha256", "report_sha256", "verifier_sha256"):
        assert seal[field] == pre["result"][field]
    assert seal["report_sha256"] == ANCHORS[REPORT] and seal["verifier_sha256"] == ANCHORS[BASE / "verify.py"]
    controls = {BASE / name for name in ("inventory.json", "prevalidation.json", "seal.json")}
    actual = {REPORT} | {p for d in (BASE, SOURCE) for p in d.rglob("*") if p.is_file()}
    assert actual - controls == {ROOT / z["path"] for z in inv["owned"]}
    entries = inv["owned"] + inv["external"]
    assert len({z["path"] for z in entries}) == len(entries)
    assert {z["path"] for z in inv["context"]} == CONTEXT and len(inv["context"]) == 4
    assert not CONTEXT & {z["path"] for z in entries}
    for z in entries:
        p = ROOT / z["path"]
        assert p.resolve().is_relative_to(ROOT) and not p.is_symlink()
        assert sha(p) == z["sha256"] and p.stat().st_size == z["size"], z["path"]
    transition = read(SOURCE / "parent-disposition-transition.json")
    old, new, note = (ROOT / transition[k] for k in ("old_snapshot", "new_snapshot", "inserted_note"))
    assert sha(old) == transition["old_sha256"] and sha(new) == transition["new_sha256"]
    assert old.stat().st_size == 6035 and new.stat().st_size == 6539 and note.stat().st_size == 504
    assert new.read_bytes().count(note.read_bytes()) == 1
    assert new.read_bytes().replace(note.read_bytes(), b"", 1) == old.read_bytes()
    assert (ROOT / transition["path"]).read_bytes() == new.read_bytes()
    contexts = [dict(path=z["path"], inherited=z["inherited"], inventory_current=z["current"],
                     actual=sha(ROOT / z["path"])) for z in inv["context"]]
    assert len(inv["owned"]) == 107 and len(inv["external"]) == 277
    return dict(status="PASS", owned=107, non_context_external=277, external_context_total=281,
                contexts=contexts, transition="exact 504-byte parent whitespace note, both versions bound",
                anchors={str(p.relative_to(ROOT)): h for p, h in ANCHORS.items()})


def main():
    before = authenticate()
    save("i174-parent-precheck.json", before)
    outpath, errpath = (BASE.parent / ("i174-parent-replay-" + s) for s in ("stdout.json", "stderr.txt"))
    with outpath.open("xb") as out, errpath.open("xb") as err:
        run = subprocess.run([sys.executable, "-I", "-B", str(BASE / "verify.py")],
                             cwd=ROOT, stdout=out, stderr=err, timeout=1200)
    assert run.returncode == 0 and not errpath.read_bytes()
    result = read(outpath)
    assert result["status"] == "PASS" and not result["prevalidation"]
    assert result["seal_sha256"] == ANCHORS[BASE / "seal.json"]
    assert len(result["comparisons"]) == 4 and all(z["byte_identical"] for z in result["comparisons"])
    assert len(result["probes"]) == 8 and all(z["blocked"] for z in result["probes"])
    after = authenticate()
    assert before == after
    save("i174-parent-verification.json", dict(status="PASS", replay=result, postcheck=after,
                                              stderr="empty", clean_clone_reconstruction="not tested"))
    print("Parent replay PASS", result["runtime_seconds"], "seconds; 107 owned, 277 external, four contexts")


if __name__ == "__main__":
    main()
