"""Parent-only detached authentication and replay. Never modifies sealed files."""
import hashlib
import json
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "frontier/experiments/i171_square_switch_weight"
SOURCES = ROOT / "frontier/sources/i171_square_switch_weight"
REPORT = ROOT / "frontier/iterations/i171-square-switch-weight.md"
OUT = BASE.parent
ANCHORS = {
    REPORT: "d9c61b5d49e778d80e376d39ee6ffee83ad11590fa68861d5bf66c25bfa7e5a6",
    BASE / "seal.json": "0cd340b50cfd23a041bdab7baf827e1d8c26e279e9a7705caecd49a7d2eefedf",
    BASE / "verify.py": "a5c8a04f3e0f49b28151fb3d7c8c1fe127104e6e5b4373a5da810c7d1a3c2b45",
}
CONTEXT = {"README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(name):
    return json.loads((BASE / name).read_bytes())


def save(name, data):
    with (OUT / name).open("x") as stream:
        json.dump(data, stream, indent=2, sort_keys=True)
        stream.write("\n")


def authenticate():
    for path, expected in ANCHORS.items():
        assert digest(path) == expected, str(path)
    inv, seal, pv = read("inventory.json"), read("seal.json"), read("prevalidation.json")
    for field, name in [("inventory_sha256", "inventory.json"),
                        ("prevalidation_sha256", "prevalidation.json")]:
        assert seal[field] == digest(BASE / name)
    assert pv["status"] == "PASS"
    assert pv["inventory_sha256"] == seal["inventory_sha256"]
    assert seal["report_sha256"] == pv["report_sha256"] == ANCHORS[REPORT]
    assert seal["verifier_sha256"] == pv["verifier_sha256"] == ANCHORS[BASE / "verify.py"]
    controls = {BASE / n for n in ("inventory.json", "prevalidation.json", "seal.json")}
    actual = {REPORT} | {p for d in (BASE, SOURCES) for p in d.rglob("*") if p.is_file()}
    listed = {ROOT / z["path"] for z in inv["files"]}
    assert len(listed) == len(inv["files"]) and listed == actual - controls
    assert {z["path"] for z in inv["external"] if z.get("role") == "context-only"} == CONTEXT
    drift = []
    for z in inv["files"] + inv["external"]:
        path = ROOT / z["path"]
        assert path.resolve().is_relative_to(ROOT)
        if z.get("role") == "context-only":
            drift.append({"path": z["path"], "expected": z["sha256"],
                          "actual": digest(path), "drift": digest(path) != z["sha256"]})
        else:
            assert digest(path) == z["sha256"] and path.stat().st_size == z["size"], z["path"]
    return {"status": "PASS", "owned_files": len(inv["files"]),
            "external_files": len(inv["external"]), "non_context_external": len(inv["external"]) - 4,
            "context": drift, "anchors": {str(p.relative_to(ROOT)): v for p, v in ANCHORS.items()}}


def payload_checks():
    first = [0, 520, 522, 524, 527, 528, 530, 533, 534, 536, 539, 431]
    for spec in read("inventory.json")["replays"]:
        data = json.loads((ROOT / spec["payload"]).read_bytes())
        assert [r["index"] for r in data["first"]] == first
    audit = read("audit-attempt-02.json")
    assert len(audit["rows"]) == 636 and audit["short_gap"] == 580 and audit["hexagons"] == 282
    old = read("coefficient-audit-attempt-02.json")
    weights = read("weights-attempt-01.json")
    assert old["steps"] == 914 and sum(old["histogram"].values()) == 610
    assert weights["steps"] == 806 and weights["parents"] == 38
    assert weights["alpha_histogram"] == {"-13/14": 464}
    assert not weights["counterexamples"] and not weights["shape_failures"]
    octagons, targeted = read("octagons-attempt-01.json"), read("targeted-attempt-01.json")
    assert octagons["steps"] == 624 and targeted["steps"] == 96
    assert octagons["histogram"] == {"(0, 0, 0)": 356, "(1, 0, 1)": 202, "(1, 1, 0)": 66}
    assert targeted["histogram"] == {"(1, 0, 1)": 63, "(1, 1, 0)": 33}
    assert targeted["levels"] == [1, 8, 64, 24]
    assert not octagons["counterexamples"] and not targeted["counterexamples"]
    cert = read("brace-certificate-attempt-01.json")
    edges = {tuple(e) for e in cert["graph"]["edges"]}
    vertices = {v for e in edges for v in e}
    all_pairs = {tuple(sorted((a, b))) for a in edges for b in edges if not set(a) & set(b)}
    seen = set()
    for z in cert["extensions"]:
        pair = tuple(sorted(tuple(e) for e in z["pair"]))
        matching = {tuple(e) for e in z["matching"]}
        assert matching <= edges and set(pair) <= matching
        assert Counter(v for e in matching for v in e) == Counter(vertices)
        seen.add(pair)
    assert seen == all_pairs and len(seen) == cert["pairs"] == 1032
    assert cert["perfect_matchings"] == 1007
    return {"status": "PASS", "walks_steps": old["steps"] + weights["steps"],
            "walks_equality_cases": 610 + 464, "brace_edge_pairs": len(seen),
            "octagonal_steps": [624, 96], "mandatory_order": first}


def main():
    before = authenticate()
    before["payload_checks"] = payload_checks()
    save("i171-parent-precheck.json", before)
    print("Parent precheck PASS", flush=True)
    stdout = OUT / "i171-parent-replay-stdout.json"
    stderr = OUT / "i171-parent-replay-stderr.txt"
    with stdout.open("xb") as out, stderr.open("xb") as err:
        run = subprocess.run([sys.executable, "-I", "-B", str(BASE / "verify.py")],
                             cwd=ROOT, stdout=out, stderr=err, timeout=1200, check=False)
    assert run.returncode == 0, run.returncode
    result = json.loads(stdout.read_bytes())
    assert result["status"] == "PASS" and result["seal_sha256"] == ANCHORS[BASE / "seal.json"]
    assert len(result["comparisons"]) == 11 and all(z["match"] for z in result["comparisons"])
    assert len(result["guard_probes"]) == 8 and all(z["blocked"] for z in result["guard_probes"])
    lines = stderr.read_text().splitlines()
    assert len(lines) == 22
    for spec, start, finish in zip(read("inventory.json")["replays"], lines[::2], lines[1::2]):
        assert start == "I171 replay START " + spec["payload"]
        assert re.fullmatch("I171 replay PASS " + re.escape(spec["payload"]) + r" [0-9.]+s", finish)
    after = authenticate()
    assert before["context"] == after["context"], "Ledgers changed during replay"
    save("i171-parent-verification.json", {
        "status": "PASS", "replay": result, "postcheck": after,
        "stderr": {"lines": 22, "only_declared_progress": True},
        "limits": "Endpoint hash checks supplement the child's initial binding; not an OS sandbox or a clean-clone test.",
    })
    print("Parent sealed replay PASS", result["runtime_seconds"], flush=True)


if __name__ == "__main__":
    main()
