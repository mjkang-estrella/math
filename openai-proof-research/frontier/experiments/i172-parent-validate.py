"""Detached parent authentication and replay, without modifying sealed evidence."""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "frontier/experiments/i172_prescribed_square_switch"
SOURCES = ROOT / "frontier/sources/i172_prescribed_square_switch"
REPORT = ROOT / "frontier/iterations/i172-prescribed-square-switch.md"
OUT = BASE.parent
ANCHORS = {
    REPORT: "030e71d1fe49909ed5dc98eb2a3250045cc3f7d8068f701cf844e676473accbe",
    BASE / "seal.json": "8abdc63ae868fbbda7778e422da34194d918be99e15fc29b784cc6468140c972",
    BASE / "verify.py": "c7a8c1af8d767573ce16fcafa28a18e28fb373f403536d6bd93c30893b9cbe28",
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
    assert {z["path"] for z in inv["external"] if z.get("role") == "context-only"} == CONTEXT
    contexts = []
    for z in inv["owned"] + inv["external"]:
        path = ROOT / z["path"]
        assert path.resolve().is_relative_to(ROOT)
        if z.get("role") == "context-only":
            contexts.append({"path": z["path"], "expected": z["sha256"],
                             "actual": digest(path), "drift": digest(path) != z["sha256"]})
        else:
            assert digest(path) == z["sha256"] and path.stat().st_size == z["size"], z["path"]
    return {"status": "PASS", "owned": len(inv["owned"]),
            "external_total": len(inv["external"]), "non_context_external": len(inv["external"]) - 4,
            "contexts": contexts, "anchors": {str(p.relative_to(ROOT)): v for p, v in ANCHORS.items()}}


def payload_checks():
    first = read("mandatory-attempt-01.json")
    assert first["order"] == [0, 520, 522, 524, 527, 528, 530, 533, 534, 536, 539, 431]
    pop = read("populations-attempt-01.json")
    assert len(pop["square_rows"]) == 806 and pop["equality_count"] == 464
    assert len(pop["octagon_rows"]) == 624 and len(pop["targeted"]) == 96
    assert pop["generation_levels"] == [1, 8, 64, 24]
    assert len(pop["independently_enumerated_graphs"]) == 201
    remote = read("remote-splices-attempt-01.json")
    assert remote["cases"] == len(remote["rows"]) == 12
    caps = read("cap-transport-attempt-01.json")
    assert caps["steps"] == 29 and not caps["high_loss"]
    assert caps["histogram"] == {"(0, 0, 0)": 20, "(1, 1, 0)": 9}
    octs = read("cut-octagons-attempt-01.json")
    assert octs["steps"] == 4 and octs["high_loss_cases"] == 3
    for z in octs["records"]:
        m, row = z["L"], z["row"]
        assert row["n"] == 2*m + 12 and row["arcs"] == [3, 3]
        assert [row[k] for k in ("ell", "t", "eta")] == [m-3, m-4, 1]
        assert [row[k] for k in ("delta_V", "delta_R", "epsilon")] == [m-4, m-4, 1]
        assert len(z["cycles"]) == 4*(m+2)
        assert all(c["good_count"] == 0 for c in row["classes"].values())
    return {"status": "PASS", "populations": [806, 624, 96], "remote_splices": 12,
            "failed_cap_transports": 29, "cut_octagons": [4, 6, 8, 10]}


def main():
    before = authenticate()
    before["payload_checks"] = payload_checks()
    save("i172-parent-precheck.json", before)
    print("Parent precheck PASS", flush=True)
    stdout, stderr = OUT / "i172-parent-replay-stdout.json", OUT / "i172-parent-replay-stderr.txt"
    with stdout.open("xb") as out, stderr.open("xb") as err:
        run = subprocess.run([sys.executable, "-I", "-B", str(BASE / "verify.py")],
                             cwd=ROOT, stdout=out, stderr=err, timeout=1200, check=False)
    assert run.returncode == 0, run.returncode
    result = json.loads(stdout.read_bytes())
    assert result["status"] == "PASS" and not result["prevalidation"]
    assert result["seal_sha256"] == ANCHORS[BASE / "seal.json"]
    assert len(result["comparisons"]) == 7 and all(z["match"] for z in result["comparisons"])
    assert len(result["probes"]) == 8 and all(z["blocked"] for z in result["probes"])
    assert stderr.read_text().splitlines() == [
        "I172 replay " + z["function"] for z in read("inventory.json")["replays"]]
    after = authenticate()
    assert before["contexts"] == after["contexts"], "Ledgers changed during parent replay"
    save("i172-parent-verification.json", {
        "status": "PASS", "replay": result, "postcheck": after,
        "stderr": "Only the seven declared progress lines",
        "limits": "Python audit guard and authenticated in-memory inputs; not an OS sandbox. Clean-clone reconstruction not tested.",
    })
    print("Parent sealed replay PASS", result["runtime_seconds"], flush=True)


if __name__ == "__main__":
    main()
