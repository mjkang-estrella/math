"""Offline I161 evidence replay; never runs ancestor code or writes output files.

Use --prevalidate only before the one seal is created. Normal replay requires it.
Audit hooks are application guards, not a hostile-code operating-system sandbox.
"""
import collections
from fractions import Fraction as F
import hashlib
import json
import math
import os
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
SOURCE = "frontier/sources/i161_oracle_tolerance_contribution_astra"
EXPERIMENT = "frontier/experiments/i161_oracle_tolerance_contribution_astra"
REPORT = "frontier/reviews/i161-oracle-tolerance-contribution-astra.md"
OUT = ROOT / SOURCE
MUTATIONS = {
    "os.remove", "os.unlink", "os.rename", "os.rmdir", "os.mkdir", "os.chmod",
    "os.chown", "os.truncate", "os.utime", "os.link", "os.symlink",
    "os.setxattr", "os.removexattr", "os.chdir", "os.fchdir",
    "os.system", "os.fork", "os.forkpty", "os.exec", "os.posix_spawn",
    "os.spawn", "os.kill", "os.killpg", "os.startfile",
}


def guard(event, args):
    if event == "open":
        _, mode, flags = args
        bad_mode = isinstance(mode, str) and any(c in mode for c in "wax+")
        bad_flags = isinstance(flags, int) and flags & (
            os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND
        )
        if bad_mode or bad_flags:
            raise PermissionError("I161 replay denies file mutation")
    if event in MUTATIONS or event.startswith(("socket.", "subprocess.", "ctypes.")):
        raise PermissionError("I161 replay denies mutation/network/processes")


sys.addaudithook(guard)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def safe_path(rel):
    path = Path(rel)
    assert not path.is_absolute() and ".." not in path.parts, rel
    assert not re.search(r"(?:i|iteration)162(?:[-_/]|$)", rel), rel
    resolved = (ROOT / path).resolve()
    assert resolved.is_relative_to(ROOT), rel
    return resolved


def load(rel):
    return json.loads(safe_path(rel).read_bytes())


def check_file(row):
    raw = safe_path(row["path"]).read_bytes()
    assert sha(raw) == row["sha256"], ("hash", row["path"])
    if "bytes" in row:
        assert len(raw) == row["bytes"], ("size", row["path"])
    return raw


def diagnostics():
    """Finite rational checks only, after all immutable evidence checks."""
    counts = collections.Counter()
    # Constant induction and worst aligned forcing at finite expression depths.
    for C in [F(2), F(3), F(5)]:
        L = P = F(1)
        for _ in range(4):
            next_L = 8 * C * C * L * (1 + L)
            next_P = 8 * C * C * P * (1 + L)
            assert 2 * C * L + 2 * C * C * L * L <= next_L
            assert 2 * C * P <= next_P
            assert C * P * (2 + 2 * C * L) <= next_P
            counts["height_domination"] += 3
            L, P = next_L, next_P
    for alpha in [F(0), F(1, 5), F(1, 2)]:
        for v in [F(1, 7), F(1), F(9)]:
            E = F(0)
            for _ in range(100):
                E = v + alpha * E
                assert E <= 2 * v
                counts["feedback"] += 1
    # Exact finite shifted schedules, endpoint equality and entropy budget.
    for m in range(1, 41):
        for q in [F(1), F(2, 3), F(9, 10)]:
            a, energy = F(1), F(0)
            for j in range(m):
                theta = F(1, m - j)
                assert a == q**j * F(m-j, m)
                energy += q*q * theta*theta * a*a
                a = q * (1-theta) * a
            assert a == 0 and energy <= F(1, m)
            counts["shift_schedules"] += 1
    # Common conditional state channel preserves TV exactly. RN ratios cancel
    # algebraically, which implies the KL identity without numerical logarithms.
    for p in [F(1, 5), F(2, 5), F(4, 5)]:
        for e in [F(1, 4), F(1, 2), F(3, 4)]:
            k, ref = [p, 1-p], [e, 1-e]
            L = [[F(1, 7), F(6, 7)], [F(3, 8), F(5, 8)]]
            joint = [k[z]*L[z][s] for z in range(2) for s in range(2)]
            other = [ref[z]*L[z][s] for z in range(2) for s in range(2)]
            assert sum(abs(a-b) for a, b in zip(joint, other)) == sum(abs(a-b) for a,b in zip(k,ref))
            for z in range(2):
                for s in range(2):
                    assert joint[2*z+s]/other[2*z+s] == k[z]/ref[z]
            counts["state_channel"] += 1
    # Physical scaling: D=C*h*eta, v=h/4 gives 2*C^2*h*eta^2.
    for h in [F(1, 2), F(1, 7), F(1, 100)]:
        C, eta = F(3), F(1, 10)
        assert (C*h*eta)**2/(2*(h/4)) == 2*C*C*h*eta*eta
        m = math.ceil(1/h)
        assert 1 <= m*h <= 1+h
        counts["physical_scaling"] += 1
    # A nonzero transformed covariance, not a claim about all reserve slots.
    v, D = [F(1), F(2)], F(3)
    off_diagonal = -v[0]*v[1]/(4*D*D)
    assert off_diagonal == -F(1, 18)
    counts["internal_covariance_fail"] += 1
    # Rational slack for the actual exponent order.
    for eps in [F(1, 100), F(1, 3), F(1), F(5)]:
        e = min(F(1, 2), eps/4)
        K = math.floor(2 + 1/e) + 1
        t = F(1, 1000*(K+2))
        assert K > 2 + 1/e and e*(K-1) > F(1, 2)
        assert e*(1+t) < eps and 40*(K+2)*t < F(1, 4)
        counts["parameter_slack"] += 1
    # e^-4 < 1/40 since a finite positive Taylor sum of e^4 exceeds 40.
    assert sum(F(4**k, math.factorial(k)) for k in range(8)) > 40
    assert F(1, 40) + F(1, 40) < F(1, 10)
    counts["fallback_budget"] += 1
    return dict(sorted(counts.items()))


def main():
    assert sys.argv[1:] in ([], ["--prevalidate"])
    pre = sys.argv[1:] == ["--prevalidate"]
    inventory_raw = (OUT / "inventory.json").read_bytes()
    inventory = json.loads(inventory_raw)
    if pre:
        assert not (OUT / "seal.json").exists(), "Cannot prevalidate/reseal a sealed record"
    else:
        seal = load(SOURCE + "/seal.json")
        assert seal["inventory_sha256"] == sha(inventory_raw)
        assert seal["seal_count"] == 1 and seal["prevalidation"] == "PASS"
    rows = inventory["files"]
    assert [r["path"] for r in rows] == sorted({r["path"] for r in rows})
    actual = {REPORT}
    for folder in [SOURCE, EXPERIMENT]:
        actual.update(str(p.relative_to(ROOT)) for p in safe_path(folder).rglob("*") if p.is_file())
    expected = {r["path"] for r in rows} | {SOURCE + "/inventory.json"}
    if not pre:
        expected.add(SOURCE + "/seal.json")
    assert actual == expected, ("owned inventory", sorted(actual ^ expected))
    for row in rows:
        check_file(row)
    bindings = load(SOURCE + "/bindings.json")
    assert bindings["pin"] == "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
    for row in bindings["files"]:
        check_file(row)
    for item in load(SOURCE + "/task-fields.json"):
        task = json.loads(check_file(item))
        assert {k:v for k,v in task.items() if k != "brief"} == item["nonbrief_fields"]
        assert sha(task["brief"].encode()) == item["brief_sha256"]
        if "decoded" in item:
            assert safe_path(item["decoded"]).read_bytes() == task["brief"].encode()
    for item in load(SOURCE + "/read-log.json")["reads"]:
        lines = safe_path(item["path"]).read_text(encoding="utf-8").split("\n")
        for passage in item["passages"]:
            lo, hi = passage["first"], passage["last"]
            assert 1 <= lo <= hi <= len(lines)
            assert sha("\n".join(lines[lo-1:hi]).encode()) == passage["sha256"]

    # One flat REPLAY traversal. The only PREPARATION traversal was scan.py.
    scan = load(SOURCE + "/flat-search.json")
    assert sha(safe_path(scan["map_path"]).read_bytes()) == scan["map_sha256"]
    assert sha(safe_path(scan["tree_path"]).read_bytes()) == scan["tree_sha256"]
    mapping = load(bindings["corpus_map"])
    entries = load(mapping["tree_path"])["tree"]
    tree = {x["path"]: x for x in entries if x["type"] == "blob"}
    positions = [x["path"] for x in mapping["bindings"]]
    if positions[0] not in tree:
        tree = {"preprints/" + p: x for p,x in tree.items()}
    assert set(positions) == set(tree) and len(positions) == len(set(positions)) == 10373
    assert len(entries) == scan["tree_entries"] == 13223
    assert len({p.split("/")[1] for p in positions}) == scan["manuscripts"] == 749
    regexes = {k:re.compile(p) for k,p in scan["patterns"].items()}
    found = {k:[] for k in regexes}
    kinds = collections.Counter()
    for row in mapping["bindings"]:
        original = safe_path(row["original_local"]).read_bytes()
        raw = original if row["local"] == row["original_local"] else safe_path(row["local"]).read_bytes()
        assert sha(original) == row["original_sha256"]
        assert sha(raw) == row["sha256"]
        blob = hashlib.sha1(b"blob " + str(len(original)).encode() + b"\0" + original).hexdigest()
        assert blob == row["git_sha"] == tree[row["path"]]["sha"]
        kinds[row["kind"]] += 1
        for n,line in enumerate(raw.decode("utf-8", errors="replace").splitlines(), 1):
            for category, regex in regexes.items():
                spans = [list(m.span()) for m in regex.finditer(line)]
                if spans:
                    found[category].append({"path":row["path"],"local":row["local"],
                                            "line":n,"spans":spans,"text":line})
    assert dict(kinds) == scan["kinds"] and found == scan["results"]
    assert scan["fresh_flat_preparation_traversals"] == 1
    prior = load(SOURCE + "/prior-search.json")
    regex = re.compile(prior["pattern"])
    matches = []
    for row in prior["domain"]:
        for n,line in enumerate(check_file(row).decode().splitlines(), 1):
            spans = [list(m.span()) for m in regex.finditer(line)]
            if spans:
                matches.append({"path":row["path"],"line":n,"spans":spans,"text":line})
    assert matches == prior["matches"]
    status = load(SOURCE + "/review-status.json")
    assert status["contribution"] == "TECHNICAL ONLY"
    assert status["accepted_findings"] == 8 and not status["acceptance_edits"]
    print("IMMUTABLE EVIDENCE PASS", json.dumps({
        "owned":len(rows), "direct_bindings":len(bindings["files"]),
        "original_positions":len(positions), "manuscripts":749,
        "lexical_lines":{k:len(v) for k,v in found.items()},
        "historical_reports":len(prior["domain"])
    }, sort_keys=True))
    # Guard probes invoke audit events only. They do not open files, sockets,
    # or processes even if the guard were accidentally removed.
    for event, args in [
        ("open", (str(OUT / "FORBIDDEN"), "w", os.O_WRONLY | os.O_CREAT)),
        ("os.mkdir", (str(OUT / "FORBIDDEN"), 0o700, -1)),
        ("socket.connect", (None, ("127.0.0.1", 1))),
        ("subprocess.Popen", ("false", ["false"], None, None)),
    ]:
        try:
            sys.audit(event, *args)
        except PermissionError:
            continue
        raise AssertionError(("guard failed", event))
    print("READ-ONLY GUARDS PASS; BYTECODE DISABLED")
    print("FINITE DIAGNOSTICS PASS", json.dumps(diagnostics(), sort_keys=True))
    print("PREVALIDATION PASS; NO SEAL WRITTEN" if pre else "SEALED REPLAY PASS; NO FILES WRITTEN")
    print("Evidence is not a universal proof, contribution, acceptance, or priority certificate.")


if __name__ == "__main__":
    main()
