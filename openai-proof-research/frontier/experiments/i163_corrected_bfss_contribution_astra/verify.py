"""Offline immutable-first I163 replay. No ancestor code is imported or executed."""
from pathlib import Path
from fractions import Fraction
import ast
import hashlib
import json
import os
import re
import sys

ROOT = Path("/home/mj-kang/Documents/Dev/math/openai-proof-research")
TAG = "i163_corrected_bfss_contribution_astra"
SOURCE = Path("frontier/sources") / TAG
EXPERIMENT = Path("frontier/experiments") / TAG
REPORT = Path("frontier/reviews/i163-corrected-bfss-contribution-astra.md")
MAP = "frontier/sources/i114_quantum_information_discovery/search-domain.json"
ENVELOPE = {str(SOURCE / name) for name in [
    "inventory.json", "preseal-validation.json", "seal.json"]}
sys.dont_write_bytecode = True


class Denied(RuntimeError):
    pass


def guard(event, args):
    if event == "open":
        path, mode, flags = args
        if isinstance(path, (str, bytes)) and os.fsdecode(path).endswith((".pyc", ".pyo")):
            raise Denied("bytecode file")
        if mode and any(c in mode for c in "wax+"):
            raise Denied("write mode")
        if flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND):
            raise Denied("write flags")
    if event.startswith(("socket.", "subprocess.", "ctypes.", "pty.")):
        raise Denied(event)
    if event in {
        "os.remove", "os.rmdir", "os.mkdir", "os.rename", "os.link", "os.symlink",
        "os.chmod", "os.chown", "os.utime", "os.truncate", "os.ftruncate",
        "os.system", "os.exec", "os.fork", "os.forkpty", "os.posix_spawn",
        "os.posix_spawnp", "os.spawn", "os.kill", "os.killpg", "os.putenv",
        "os.unsetenv", "shutil.copyfile", "shutil.copymode", "shutil.copystat",
        "shutil.rmtree", "shutil.move"
    }:
        raise Denied(event)


sys.addaudithook(guard)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def safe(path):
    p = ROOT / path
    assert not p.is_symlink(), path
    assert p.resolve().is_relative_to(ROOT), path
    return p


def load(path):
    return json.loads(safe(path).read_text(encoding="utf8"))


def record(path):
    data = safe(path).read_bytes()
    return {"path": str(path), "bytes": len(data), "sha256": sha(data)}


def check(row):
    assert record(row["path"]) == row, row["path"]


def owned():
    paths = [REPORT]
    for parent in [SOURCE, EXPERIMENT]:
        for p in (ROOT / parent).rglob("*"):
            assert not p.is_symlink(), p
            if p.is_file():
                paths.append(p.relative_to(ROOT))
    return sorted(str(p) for p in paths)


def finite_checks():
    # Arithmetic diagnostics only. The report, not these samples, gives proofs.
    c, cap, threshold, fermion = 3, 1024, 3072, 6
    assert (threshold + 9) // 3 - cap == c
    assert 3080 > threshold + fermion
    assert 96**2 * 6 < cap**2
    eps = Fraction(c, 2*(c+cap))
    a = (1+eps)/4
    b = (1-eps)*c-eps*cap
    assert b == Fraction(3, 2) and a > Fraction(1, 4)
    assert a*9/(3*Fraction(1, 4)**2) > 3  # pi > 3, kappa=1/4
    metric_cases = 0
    for x in range(2, 22):
        for y in range(1, x):
            diagonal, off = x*x+y*y, -2*x*y
            assert diagonal**2-off**2 == (x*x-y*y)**2
            assert diagonal+off == (x-y)**2
            assert diagonal-off == (x+y)**2
            metric_cases += 1
    assert Fraction(1, 2)+2-Fraction(1, 4) == Fraction(9, 4)
    assert Fraction(1, 2)+1 == Fraction(3, 2)
    assert 2-Fraction(1, 2) == Fraction(3, 2)
    assert 3*(Fraction(1, 4)+Fraction(1, 2)) == Fraction(9, 4)
    assert Fraction(3, 4)*64/(96*45) == Fraction(1, 90)
    assert Fraction(1, 3)*Fraction(1, 90) == Fraction(1, 270)
    # B4 Weyl dimension of the specified type is a positive integer.
    rho = [Fraction(x, 2) for x in [7, 5, 3, 1]]
    shifted = [r+l for r, l in zip(rho, [3086, 3080, 0, 0])]
    dimension = Fraction(1)
    for i in range(4):
        dimension *= shifted[i]/rho[i]
        for j in range(i+1, 4):
            dimension *= (shifted[i]**2-shifted[j]**2)/(rho[i]**2-rho[j]**2)
    assert dimension.denominator == 1 and dimension > 0
    tests = [
        ("open", (str(ROOT / SOURCE / "_forbidden"), "w", os.O_WRONLY)),
        ("open", (str(ROOT / SOURCE / "_forbidden.pyc"), "r", os.O_RDONLY)),
        ("os.remove", (str(ROOT / SOURCE / "_forbidden"), -1)),
        ("os.mkdir", (str(ROOT / SOURCE / "_forbidden"), 0o700, -1)),
        ("os.rename", ("absent-a", "absent-b", -1, -1)),
        ("socket.__new__", (None, 2, 1, 0)),
        ("socket.connect", (None, ("127.0.0.1", 1))),
        ("subprocess.Popen", ("false", ["false"], None, None)),
        ("os.system", ("false",)),
        ("os.fork", ()),
        ("os.putenv", ("I163_TEST", "denied")),
    ]
    for event, args in tests:
        try:
            sys.audit(event, *args)
        except Denied:
            pass
        else:
            raise AssertionError("guard failed: " + event)
    return {"metric_cases": metric_cases, "normalization_and_scaling": "PASS",
            "phase_rational_prefactor": "1/270",
            "explicit_type_dimension": str(dimension.numerator),
            "guard_event_tests": len(tests),
            "scope": "Finite arithmetic and guard dispatch only; not a proof, novelty, or acceptance certificate."}


def main():
    assert sys.flags.isolated and sys.dont_write_bytecode and not sys.flags.optimize, "Use python3 -I -B without -O"
    prevalidate = sys.argv[1:] == ["--prevalidate"]
    check_only = sys.argv[1:] == ["--check"]
    assert prevalidate or check_only or not sys.argv[1:], "Unknown arguments"
    inventory_path = str(SOURCE / "inventory.json")
    seal_path = str(SOURCE / "seal.json")
    pre_path = str(SOURCE / "preseal-validation.json")
    if prevalidate or check_only:
        assert not safe(seal_path).exists(), "No prevalidation after seal"
    else:
        seal = load(seal_path)
        assert seal["schema"] == "i163-one-seal-v1"
        check(seal["inventory"])
        check(seal["prevalidation"])
        prior = load(pre_path)
        assert prior["status"] == "PASS"
        assert prior["mode"] == "prevalidate-read-only"
        assert prior["inventory"] == seal["inventory"]
    if check_only:
        assert not safe(inventory_path).exists(), "Pre-inventory development check only"
        inventory = {"envelope": sorted(ENVELOPE),
                     "payload": [record(p) for p in owned() if p not in ENVELOPE]}
    else:
        inventory = load(inventory_path)
    assert inventory["envelope"] == sorted(ENVELOPE)
    rows = inventory["payload"]
    assert rows == sorted(rows, key=lambda x: x["path"])
    expected_payload = [p for p in owned() if p not in ENVELOPE]
    assert [x["path"] for x in rows] == expected_payload, "Exact payload inventory"
    for row in rows:
        check(row)
    if not prevalidate and not check_only:
        assert set(owned()) == set(expected_payload) | ENVELOPE

    baseline = load(SOURCE / "immutable-baseline.json")
    references = load(SOURCE / "references.json")
    for row in baseline + references:
        check(row)
    assert len(baseline) == 135
    for row in rows:
        path = row["path"]
        if path.endswith(".json"):
            load(path)
        elif path.endswith(".py"):
            ast.parse(safe(path).read_text(), filename=str(ROOT / path))
    assert load("sources/upstream.json")["commit"] == "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"

    # One flat original traversal, including all 776 inherited PDF/text pairs.
    domain = load(MAP)
    tree = load("sources/preprints-tree.json")["tree"]
    blobs = {x["path"]: x for x in tree if x["type"] == "blob"}
    assert len({x["path"] for x in domain}) == len(domain) == 10373
    assert {x["path"] for x in domain} == set(blobs)
    assert len(tree) == 13223
    search = load(SOURCE / "manuscript-search.json")
    rx = re.compile(search["query"])
    hits, roots, kinds = [], set(), {}
    for row in domain:
        path, kind = row["path"], row["kind"]
        roots.add(path.split("/")[1])
        kinds[kind] = kinds.get(kind, 0)+1
        data = safe(row["original_local"]).read_bytes()
        assert sha(data) == row["original_sha256"], path
        blob = hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()
        assert blob == row["git_sha"] == blobs[path]["sha"], path
        if kind == "outside_bytes":
            continue
        text_data = data if row["local"] == row["original_local"] else safe(row["local"]).read_bytes()
        assert sha(text_data) == row["sha256"], path
        text = text_data.decode("utf8")
        for match in rx.finditer(text):
            a, b = match.span()
            hits.append({"path": path, "local": row["local"], "start": a, "end": b,
                         "match": match.group(), "line": text.count("\n", 0, a)+1,
                         "context": text[max(0, a-180):min(len(text), b+350)]})
    assert len(roots) == search["roots"] == 749
    assert kinds == search["kinds"] == {"corpus": 9340, "outside_pdf": 776, "outside_bytes": 257}
    assert hits == search["hits"] and len(hits) == 46
    for row in load(SOURCE / "pinned-passages.json"):
        data = safe(row["local"]).read_bytes()
        assert sha(data) == row["sha256"]
        assert row["git_sha"] == blobs[row["path"]]["sha"]
    for pair in load(SOURCE / "bindings.json"):
        for role in ["pdf", "text", "tex"]:
            if role in pair:
                check(pair[role])
    reading = load(SOURCE / "reading.json")
    for receipt in reading:
        data = safe(receipt["path"]).read_bytes()
        assert sha(data) == receipt["file_sha256"]
        lines = data.decode("utf8").split("\n")
        assert len(lines) == receipt["lf_split_count"]
        for part in receipt["ranges"]:
            text = "\n".join(lines[part["start"]-1:part["end"]])
            assert sha(text.encode()) == part["sha256"]
            assert len(text) == part["chars"] and text[-180:] == part["ending"]
    for view in load(SOURCE / "task-views.json"):
        task = load(view["task"])
        assert safe(view["brief"]).read_text() == task["brief"]
        assert len(task["brief"]) == view["characters"]
        assert load(view["other_fields"]) == {k: v for k, v in task.items() if k != "brief"}
    drift = []
    for ledger in load(SOURCE / "ledger-excerpts.json"):
        assert sha(ledger["text"].encode()) == ledger["excerpt_sha256"]
        if record(ledger["path"]) != ledger["observed"]:
            drift.append(ledger["path"])

    # Only after all immutable checks and reconstructions, run new finite checks.
    result = {
        "status": "PASS", "mode": "development-read-only" if check_only else (
            "prevalidate-read-only" if prevalidate else "sealed-read-only"),
        "inventory": None if check_only else record(inventory_path),
        "canonical_exact_payload_files": len(rows),
        "envelope_files": sorted(ENVELOPE),
        "immutable_baseline": len(baseline), "additional_references": len(references),
        "map_originals": len(domain), "tree_entries": len(tree), "roots": len(roots),
        "kinds": kinds, "flat_corpus_traversals": 1, "lexical_occurrences": len(hits),
        "reading_receipts": len(reading), "permitted_live_ledger_drift": drift,
        "all_immutable_checks_before_diagnostics": True,
        "ancestor_execution": "none",
        "finite_diagnostics": finite_checks(),
        "scope": "Evidence integrity/reconstruction and finite diagnostics only; no universal proof or contribution certification."
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
