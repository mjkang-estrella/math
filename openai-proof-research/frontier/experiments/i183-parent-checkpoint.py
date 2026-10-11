"""Detached validation of the incomplete I183 checkpoint, not a seal.

Ancestor Python is never loaded. The reviewed child verifier is replayed
only after all detached anchors, owned bytes and strict rows pass.
"""
import hashlib
import itertools
import json
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = "frontier/experiments/i183_cptp_survival/resumed"
SOURCE = "frontier/sources/i183_cptp_survival/resumed"
REPORT = "frontier/iterations/i183-cptp-survival-resumed.md"
CONTEXT = ("README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md")
ANCHORS = {
    REPORT: "8463565efeff51bf6596848916dc16a91771b9975a385c329b18dae44c02c66c",
    BASE + "/checkpoint-inventory.json":
        "efddbadc730b1fcfc040fabc6fb2b8b957cd2689070d46ff2486f1b135801f40",
    BASE + "/verify_checkpoint.py":
        "1462c445c63b7f2aa03b269522b52d44895d6fb24ec6845459779c2747769bcd",
    "frontier/experiments/i183_cptp_survival/auth183.py":
        "1ecd104da68fb64c50e85b58351ca00430e797065603431a99e99b51b8848ba1",
    "frontier/experiments/i183_cptp_survival/inputs.json":
        "bc8e8779bbec36e373488544fe0386f47058a8b42406a31844b532341df5cc09",
    "frontier/experiments/i183_cptp_survival/math183.py":
        "ff507fbb829207e4928af17e78975e144a4e06b629fa8a8ac8223b99809e1a87",
}


def path(name):
    p = Path(name)
    assert not p.is_absolute() and ".." not in p.parts
    p = ROOT / p
    assert p.resolve().is_relative_to(ROOT) and not p.is_symlink()
    return p


def row(name):
    data = path(name).read_bytes()
    return dict(path=name, size=len(data), sha256=hashlib.sha256(data).hexdigest())


def load(name):
    return json.loads(path(name).read_bytes())


def members(dirs, extra=()):
    result = set(extra)
    for name in dirs:
        for p in path(name).rglob("*"):
            assert not p.is_symlink()
            if p.is_file():
                result.add(p.relative_to(ROOT).as_posix())
    return sorted(result)


def authenticate():
    for name, digest in ANCHORS.items():
        assert row(name)["sha256"] == digest, name
    inventory = load(BASE + "/checkpoint-inventory.json")
    assert inventory["status"] == "INCOMPLETE_UNSEALED_CHECKPOINT"
    assert inventory["controls"] == [BASE + "/checkpoint-inventory.json"]
    owned = inventory["owned"]
    frozen = load(BASE + "/inputs.json")
    assert len(frozen["strict"]) == 1067
    assert {x["path"] for x in frozen["context"]} == set(CONTEXT)
    for population in (owned, frozen["strict"]):
        assert len({x["path"] for x in population}) == len(population)
        for item in population:
            assert row(item["path"]) == item, item["path"]
    strict = {x["path"] for x in frozen["strict"]}
    assert not strict.intersection(CONTEXT)
    assert members((BASE, SOURCE), (REPORT,)) == sorted(
        [x["path"] for x in owned] + inventory["controls"])
    for chain in frozen["parent_membership"]:
        assert members(chain["directories"], chain["extra"]) == chain["members"]
        assert set(chain["members"]) <= strict
    assert [x["iteration"] for x in frozen["parent_membership"]] == list(range(175, 183))
    assert not path(BASE + "/seal.json").exists()
    assert not path(BASE + "/prevalidation.json").exists()
    return {
        "owned": len(owned), "strict": len(strict),
        "membership_counts": [len(x["members"]) for x in frozen["parent_membership"]],
        "anchors": ANCHORS, "current_context": [row(p) for p in CONTEXT],
        "historically_drifted_context": [
            x["path"] for x in frozen["context"] if row(x["path"]) != x],
    }


def formal_certificates():
    """Independent subset matching checks on proof shores, not graph tests."""
    cycle = ("x", "a", "b", "y", "d", "c")
    patch = list(zip(cycle, cycle[1:] + cycle[:1])) + [("x", "y")]

    def local_matchings(vertices, edges):
        # All vertices in the shore must be saturated once; star endpoints
        # are distinct formal cut incidences, not actual completed graphs.
        out = []
        for flags in itertools.product((0, 1), repeat=len(edges)):
            selected = [e for e, b in zip(edges, flags) if b]
            if all(sum(v in e for e in selected) == 1 for v in vertices):
                out.append(selected)
        return out

    extra_rows = []
    for chord, cut, forced in (
            (("a", "d"), ("b", "c"), ("b", "b*")),
            (("b", "c"), ("a", "d"), ("a", "a*"))):
        matches = local_matchings(cycle, patch + [chord] + [(v, v + "*") for v in cut])
        assert matches
        assert all(sum(b.endswith("*") for a, b in m) % 2 == 0 for m in matches)
        assert all(not (forced in m and ("d", "c") in m) for m in matches)
        extra_rows.append({"chord": chord, "shore_matchings": len(matches)})

    repeated_rows = []
    for repeated, outgoing in ((("a", "c"), ("b", "d", "t")),
                               (("b", "d"), ("a", "c", "t"))):
        edges = patch + [(v, "t") for v in repeated] + [(v, v + "*") for v in outgoing]
        matches = local_matchings(cycle + ("t",), edges)
        assert matches and all(sum(b.endswith("*") for a, b in m) == 1 for m in matches)
        repeated_rows.append({"repeated": repeated, "shore_matchings": len(matches)})
    partitions = {tuple(tuple(i for i, x in enumerate(word) if x == label)
                        for label in sorted(set(word)))
                  for word in itertools.product(range(3), repeat=3)}
    # Ignore block order to get the five genuine set partitions.
    partitions = {tuple(sorted(p)) for p in partitions}
    assert len(partitions) == 5
    for p in partitions:
        assert (len(p) > 1) == any(
            not any(i in block and j in block for block in p)
            for i, j in itertools.combinations(range(3), 2))
    # Four labelled intervals, preserving duplicate edge identities.
    pairings = (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2)))
    component_counts = []
    for pairing in pairings:
        edges = pairing + pairings[0]
        groups = [{i} for i in range(4)]
        for a, b in edges:
            joined = set().union(*(g for g in groups if a in g or b in g))
            groups = [g for g in groups if not (a in g or b in g)] + [joined]
        component_counts.append(len(groups))
    assert component_counts == [2, 1, 1]
    return {"internal_chords": extra_rows, "repeated_terminals": repeated_rows,
            "endpoint_partitions": 5, "attachment_components": component_counts,
            "scope": "Independent finite proof bookkeeping, not new graph tests"}


def main():
    assert sys.flags.isolated and sys.dont_write_bytecode
    assert len(sys.argv) == 2
    prefix = sys.argv[1]
    assert prefix.startswith("i183-parent-") and Path(prefix).name == prefix
    before = authenticate()
    certificates = formal_certificates()
    start = time.monotonic()
    proc = subprocess.run([sys.executable, "-I", "-B",
                           str(path(BASE + "/verify_checkpoint.py"))],
                          cwd=ROOT, capture_output=True, timeout=120)
    elapsed = time.monotonic() - start
    for suffix, data in ((".stdout", proc.stdout), (".stderr", proc.stderr)):
        with path("frontier/experiments/" + prefix + suffix).open("xb") as f:
            f.write(data)
    assert proc.returncode == 0 and proc.stderr == b"", proc.stderr.decode()
    replay = json.loads(proc.stdout)
    assert replay["status"] == "PASS_INCOMPLETE_CHECKPOINT_ONLY"
    assert not replay["sealed"] and not replay["prevalidated_for_seal"]
    assert not replay["full_mandatory_replay"]
    assert replay["mandatory_stage_prefix_recomputed"] == 12
    assert replay["mandatory_stages_required"] == 23
    assert len(replay["remaining_stages"]) == 11
    assert replay["forgery_positive_control"] is True
    probes = replay["eight_live_probes"]
    assert {p["probe"] for p in probes} == {
        "write", "mutation", "network", "subprocess", "unbound-read",
        "outside-compile", "outside-exec", "forged-owned-source"}
    assert all(p["status"] == "BLOCKED" for p in probes)
    assert authenticate() == before
    receipt = dict(status="PASS_PARTIAL_CHECKPOINT", authentication=before,
                   independent_formal_certificates=certificates, replay=replay,
                   elapsed_seconds=elapsed, universal_E183="UNRESOLVED",
                   full_mandatory_replay=False, sealed=False)
    with path("frontier/experiments/" + prefix + ".json").open("x") as f:
        json.dump(receipt, f, indent=2, sort_keys=True)
        f.write("\n")
    print(json.dumps({"status": receipt["status"], "owned": before["owned"],
                      "strict": before["strict"], "elapsed_seconds": elapsed,
                      "sealed": False, "mandatory_stages": "12/23"}))


if __name__ == "__main__":
    main()
