"""Detached authentication and pre-integration sealed replay; never reseals."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "frontier/experiments/i175_affected_prism_exterior"
SOURCE = ROOT / "frontier/sources/i175_affected_prism_exterior"
REPORT = ROOT / "frontier/iterations/i175-affected-prism-exterior.md"
ANCHORS = {
    REPORT: "7df9e04e808e5f537eef1291b9f323ffd27dfb25c6edd4b76b34d8f23e198ff9",
    BASE / "seal.json": "42636ad1d8a669c8bee23332d7059e0ba957c3467a343ea2b563fdf346905c31",
    BASE / "verify175.py": "e09a4daaa655b9482cb3ac5686fce7e0555eb7d857b8d0ce77b063d184be101a",
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
        assert sha(p) == h, p
    inv, seal, pre = (read(BASE / name) for name in ("inventory.json", "seal.json", "prevalidation.json"))
    for name in ("inventory", "prevalidation"):
        assert sha(BASE / (name+".json")) == seal[name+"_sha256"]
    assert pre["status"] == "PASS" and pre["stderr"] == "empty" and pre["prevalidation"]
    for field in ("inventory_sha256", "report_sha256", "verifier_sha256"):
        assert pre[field] == seal[field]
    assert seal["report_sha256"] == ANCHORS[REPORT] and seal["verifier_sha256"] == ANCHORS[BASE / "verify175.py"]
    controls = {BASE / n for n in ("inventory.json", "prevalidation.json", "seal.json")}
    actual = {REPORT} | {p for d in (BASE, SOURCE) for p in d.rglob("*") if p.is_file()}
    assert actual - controls == {ROOT / z["path"] for z in inv["owned"]}
    entries = inv["owned"] + inv["external"]
    assert len(entries) == len({z["path"] for z in entries})
    assert len(inv["context"]) == 4 and {z["path"] for z in inv["context"]} == CONTEXT
    assert not CONTEXT & {z["path"] for z in entries}
    for z in entries:
        p = ROOT / z["path"]
        assert p.resolve().is_relative_to(ROOT) and not p.is_symlink()
        assert sha(p) == z["sha256"] and p.stat().st_size == z["size"], z["path"]
    contexts = []
    for z in inv["context"]:
        p = ROOT / z["path"]
        assert sha(p) == z["sha256"] and p.stat().st_size == z["size"]
        contexts.append(dict(path=z["path"], actual=sha(p), inherited=z["I174_inherited"],
                             inherited_drift=sha(p) != z["I174_inherited"]))
    assert len(inv["owned"]) == 94 and len(inv["external"]) == 399
    return dict(status="PASS", owned=94, non_context_external=399, external_context_total=403,
                contexts=contexts, anchors={str(p.relative_to(ROOT)): h for p, h in ANCHORS.items()})


def main():
    before = authenticate()
    save("i175-parent-precheck.json", before)
    stdout, stderr = (BASE.parent / ("i175-parent-replay-"+n) for n in ("stdout.json", "stderr.txt"))
    with stdout.open("xb") as out, stderr.open("xb") as err:
        run = subprocess.run([sys.executable, "-I", "-B", str(BASE / "verify175.py")],
                             cwd=ROOT, stdout=out, stderr=err, timeout=1200)
    assert run.returncode == 0 and not stderr.read_bytes()
    result = read(stdout)
    assert result["status"] == "PASS" and not result["prevalidation"]
    assert result["seal_sha256"] == ANCHORS[BASE / "seal.json"]
    assert len(result["comparisons"]) == 5 and all(z["byte_identical"] for z in result["comparisons"])
    assert len(result["probes"]) == 8 and all(z["blocked"] for z in result["probes"])
    after = authenticate()
    assert before == after
    save("i175-parent-verification.json", dict(
        status="PASS", replay=result, postcheck=after, stderr="empty",
        context_replay_limit="Sealed verifier requires exact inventory-current context hashes. This replay predates integration ledger edits. Later direct replay needs those historical contexts restored in a separate reconstruction.",
        clean_clone_reconstruction="not tested"))
    print("Parent replay PASS", result["runtime_seconds"], "seconds; 94 owned, 399 external, four contexts")


if __name__ == "__main__":
    main()
