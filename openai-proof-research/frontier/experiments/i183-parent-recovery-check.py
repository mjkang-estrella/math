"""Preserve and authenticate interrupted I183 work, without mathematical execution."""
import ast
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "frontier/experiments/i183_cptp_survival"
OUT = BASE.parent / "i183-parent-recovery-check.json"
SAVED = {
    "auth183.py": "1ecd104da68fb64c50e85b58351ca00430e797065603431a99e99b51b8848ba1",
    "inputs.json": "bc8e8779bbec36e373488544fe0386f47058a8b42406a31844b532341df5cc09",
    "math183.py": "ff507fbb829207e4928af17e78975e144a4e06b629fa8a8ac8223b99809e1a87",
}
CONTEXTS = {"README.md", "frontier/README.md", "frontier/TEN-FINDINGS.md",
            "frontier/iterations/README.md"}


def record(path):
    assert path.resolve().is_relative_to(ROOT) and not path.is_symlink(), path
    data = path.read_bytes()
    return {"path": path.relative_to(ROOT).as_posix(), "size": len(data),
            "sha256": hashlib.sha256(data).hexdigest()}


def check_row(row):
    assert record(ROOT / row["path"]) == row, row["path"]


def check():
    saved = []
    for name, digest in SAVED.items():
        path = BASE / name
        row = record(path)
        assert row["sha256"] == digest, name
        if path.suffix == ".py":
            ast.parse(path.read_bytes(), filename=str(path))
        saved.append(row)
    frozen = json.loads((BASE / "inputs.json").read_bytes())
    rows = frozen["strict"]
    assert len(rows) == len({r["path"] for r in rows}) == 1053
    assert {r["path"] for r in frozen["context"]} == CONTEXTS
    assert len(frozen["context"]) == 4
    assert not CONTEXTS & {r["path"] for r in rows}
    for row in rows:
        check_row(row)
    for path, digest in frozen["anchors"].items():
        assert record(ROOT / path)["sha256"] == digest
    # Independently check every I182 package byte, including nested digest records.
    parent = ROOT / "frontier/experiments/i182_controlled_extension"
    inv = json.loads((parent / "inventory.json").read_bytes())
    seal = json.loads((parent / "seal.json").read_bytes())
    assert inv["owned_sha256"] == seal["inventory_sha256"]
    for entry in inv["files"]:
        now = record(parent / entry["name"])
        assert now["sha256"] == entry["sha256"]["sha256"]
        assert now["size"] == entry["bytes"] == entry["sha256"]["size"]
    assert len(inv["files"]) == 25
    assert {p.name for p in parent.iterdir() if p.is_file()} == (
        {e["name"] for e in inv["files"]} |
        {"inventory.json", "prevalidation.json", "seal.json"})
    # Negative authentication check without changing any file.
    forged = dict(saved[0], sha256="0" * 64)
    try:
        check_row(forged)
    except AssertionError:
        pass
    else:
        raise AssertionError("forged digest was not rejected")
    contexts = [dict(record(ROOT / r["path"]), historical_sha256=r["sha256"])
                for r in frozen["context"]]
    return {"status": "PASS", "scope": "Preservation, byte checks and syntax only",
            "partial_files": saved, "strict_bindings_checked": 1053,
            "i182_owned_bytes_checked": 25, "contexts": contexts,
            "syntax_parsed": ["auth183.py", "math183.py"],
            "negative_digest_check": "rejected",
            "math_execution": "not run", "mathematical_verdict": "none"}


def main():
    assert sys.argv[1:] in ([], ["--capture"])
    result = check()
    if sys.argv[1:] == ["--capture"]:
        assert {p.name for p in BASE.iterdir()} == set(SAVED)
        assert not (ROOT / "frontier/iterations/i183-cptp-survival.md").exists()
        assert not any(p.is_file() for p in (
            ROOT / "frontier/sources/i183_cptp_survival").rglob("*"))
        result["initial_deliverables"] = "No report, diagnostics, verifier or seal"
        with OUT.open("x") as out:
            json.dump(result, out, indent=2, sort_keys=True)
            out.write("\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
