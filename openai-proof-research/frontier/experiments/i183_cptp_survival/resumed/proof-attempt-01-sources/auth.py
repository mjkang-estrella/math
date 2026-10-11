"""Continuation byte authentication. No ancestor code is executed.

Schemas and anchor values come from the preserved same-I183 auth183.py,
but the context policy and membership checks below are new.
"""
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
BASE = "frontier/experiments/i183_cptp_survival/resumed"
SOURCES = "frontier/sources/i183_cptp_survival/resumed"
REPORT = "frontier/iterations/i183-cptp-survival-resumed.md"
OLD = "frontier/experiments/i183_cptp_survival"
PARENT = "frontier/experiments/i182_controlled_extension"
CONTEXT = ("README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
           "frontier/iterations/README.md")
ANCHORS = {
    OLD + "/auth183.py":
        "1ecd104da68fb64c50e85b58351ca00430e797065603431a99e99b51b8848ba1",
    OLD + "/inputs.json":
        "bc8e8779bbec36e373488544fe0386f47058a8b42406a31844b532341df5cc09",
    OLD + "/math183.py":
        "ff507fbb829207e4928af17e78975e144a4e06b629fa8a8ac8223b99809e1a87",
    "frontier/iterations/i182-controlled-extension.md":
        "6035bffd8b69ba08bf6a148fdd314bd704824e6bdd1942469afb0d343596ebc6",
    PARENT + "/seal.json":
        "6fcbd83ab618636826cb2c9d7f71d18d22a316fcc12772501dc6fbac7668667c",
    PARENT + "/verify182.py":
        "314696445a3e77ad2a6bde12e0cc4826454b70bc7e0529dfd33d9e00c00f2889",
}
RECOVERY = (
    "frontier/iterations/iteration183-cptp-survival-resume-brief.md",
    "frontier/iterations/i183-provider-failure-recovery.md",
    "frontier/iterations/iteration183-cptp-survival-resume-factory-astra-task.json",
    "frontier/experiments/i183-parent-recovery-check.py",
    "frontier/experiments/i183-parent-recovery-check.json",
)


def safe(path):
    p = Path(path)
    assert not p.is_absolute() and ".." not in p.parts, path
    assert (ROOT / p).resolve().is_relative_to(ROOT), path
    return ROOT / p


def row(path):
    data = safe(path).read_bytes()
    return {"path": path, "size": len(data),
            "sha256": hashlib.sha256(data).hexdigest()}


def load(path):
    return json.loads(safe(path).read_bytes())


def check_rows(rows):
    for item in rows:
        assert row(item["path"]) == item, item["path"]


def members(directories, extra=()):
    result = set(extra)
    for directory in directories:
        for p in safe(directory).rglob("*"):
            assert not p.is_symlink(), str(p.relative_to(ROOT))
            if p.is_file():
                result.add(p.relative_to(ROOT).as_posix())
    return sorted(result)


def parent_memberships():
    """Check complete I175--I182 membership, not just listed-file hashes."""
    old = load(OLD + "/inputs.json")
    inventories = sorted({x["path"] for x in old["strict"]
                          if x["path"].endswith("/inventory.json")} |
                         {PARENT + "/inventory.json",
                          "frontier/experiments/i181_six_cycle_helper/inventory.json"})
    records = []
    for path in inventories:
        obj = load(path)
        iteration = obj.get("iteration")
        if obj.get("package") == "I181":
            iteration = 181
        if iteration not in range(175, 183):
            continue
        directory = Path(path).parent.as_posix()
        if iteration == 182:
            owned = []
            for x in obj["files"]:
                # The old inventory has relative names containing ../..
                name = (safe(directory) / x["name"]).resolve()
                assert name.is_relative_to(ROOT)
                item = row(name.relative_to(ROOT).as_posix())
                assert item["sha256"] == x["sha256"]["sha256"]
                assert item["size"] == x["bytes"] == x["sha256"]["size"]
                owned.append(item)
            controls = [directory + "/" + s for s in
                        ("inventory.json", "prevalidation.json", "seal.json")]
            # I182 kept its report and literature outside owned_files.
            extra = ["frontier/iterations/i182-controlled-extension.md",
                     "frontier/sources/i182_controlled_extension/literature.md"]
        else:
            owned = obj["files"] if iteration == 181 else obj["owned"]
            check_rows(owned)
            controls = ([directory + "/" + s for s in
                         ("inventory.json", "prevalidation.json", "seal.json")]
                        if iteration == 181 else obj["controls"])
            extra = []
        report_paths = [x["path"] for x in owned
                        if x["path"].startswith("frontier/iterations/")]
        declared = sorted({x["path"] for x in owned} | set(controls) | set(extra))
        dirs = [directory, directory.replace("/experiments/", "/sources/")]
        actual = members(dirs, report_paths + [
            x for x in extra if x.startswith("frontier/iterations/")])
        assert actual == declared, (path, sorted(set(actual) ^ set(declared)))
        records.append({"iteration": iteration, "directories": dirs,
                        "extra": report_paths + [
                            x for x in extra if x.startswith("frontier/iterations/")],
                        "members": actual, "owned": len(owned)})
    assert [x["iteration"] for x in records] == list(range(175, 183))
    assert [x["owned"] for x in records] == [94, 59, 78, 81, 122, 44, 29, 25]
    return records


def authenticate():
    for path, digest in ANCHORS.items():
        assert row(path)["sha256"] == digest, path
    old = load(OLD + "/inputs.json")
    assert len(old["strict"]) == 1053
    assert {x["path"] for x in old["context"]} == set(CONTEXT)
    check_rows(old["strict"])
    assert len(old["parent_evidence"]) == 16
    chains = parent_memberships()
    return old, chains


def freeze():
    old, chains = authenticate()
    paths = {x["path"] for x in old["strict"]} | set(ANCHORS) | set(RECOVERY)
    paths.update(p for chain in chains for p in chain["members"])
    assert not paths.intersection(CONTEXT)
    data = {
        "iteration": "183-resumed", "status": "AUTHENTICATED_ONLY",
        "strict": [row(p) for p in sorted(paths)],
        "anchors": ANCHORS, "parent_membership": chains,
        "context": [row(p) for p in CONTEXT],
        "recovery": list(RECOVERY),
        "policy": "Only four contexts tolerate historical drift; record current "
                  "bytes and require before/after equality during each replay.",
        "dispatch": "Resume dispatch arrived before this exclusive freeze.",
    }
    check_rows(data["strict"])
    with safe(BASE + "/inputs.json").open("x") as f:
        json.dump(data, f, indent=2, sort_keys=True)
        f.write("\n")
    return {"status": "PASS", "strict": len(paths), "contexts": 4,
            "memberships": [x["owned"] for x in chains]}


def check():
    frozen = load(BASE + "/inputs.json")
    check_rows(frozen["strict"])
    assert set(frozen["anchors"]) == set(ANCHORS)
    for path, digest in ANCHORS.items():
        assert row(path)["sha256"] == frozen["anchors"][path] == digest
    for item in frozen["parent_membership"]:
        assert members(item["directories"], item["extra"]) == item["members"]
    return [row(p) for p in CONTEXT]


if __name__ == "__main__":
    assert sys.flags.isolated and sys.dont_write_bytecode
    if sys.argv[1:] == ["freeze"]:
        print(json.dumps(freeze(), sort_keys=True))
    elif sys.argv[1:] == ["check"]:
        print(json.dumps({"status": "PASS", "current_context": check()},
                         sort_keys=True))
    else:
        raise SystemExit("Use freeze or check")
