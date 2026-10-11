"""Create exactly one I167 seal from a current successful prevalidation."""
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE = ROOT / "frontier/sources/i167_exchange_step_braces"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    assert sys.flags.isolated and sys.dont_write_bytecode
    assert not (HERE / "seal.json").exists(), "refusing reseal"
    receipt = json.loads((HERE / "prevalidation.json").read_text())
    assert receipt["status"] == "PASS" and receipt["mode"] == "prevalidation"
    assert receipt["read_only"] and not receipt["ancestor_execution"]
    current = {
        "inventory_sha256": digest(HERE / "owned-files.json"),
        "external_bindings_sha256": digest(SOURCE / "external-bindings.json"),
        "policy_sha256": digest(SOURCE / "replay-policy.json"),
        "report_sha256": digest(ROOT / "frontier/iterations/i167-exchange-step-braces.md")
    }
    assert receipt["bindings"] == current
    inv = json.loads((HERE / "owned-files.json").read_text())
    bound = {ROOT / row["path"] for row in inv["files"]}
    control = {HERE/name for name in ("owned-files.json", "prevalidation.json", "seal.json")}
    actual = {p for base in (HERE, SOURCE) for p in base.rglob("*") if p.is_file()} | {
        ROOT / "frontier/iterations/i167-exchange-step-braces.md"}
    assert actual-control == bound
    for row in inv["files"]:
        path = ROOT / row["path"]
        assert path.stat().st_size == row["size"] and digest(path) == row["sha256"]
    external = json.loads((SOURCE / "external-bindings.json").read_text())
    for row in external["files"]:
        if row["path"] in ("frontier/TEN-FINDINGS.md", "frontier/iterations/README.md"):
            continue
        path = ROOT / row["path"]
        assert path.stat().st_size == row["size"] and digest(path) == row["sha256"]
    data = {"iteration": 167, "creation": "exclusive-create, one seal only",
            "bindings": current, "prevalidation_sha256": digest(HERE / "prevalidation.json")}
    with (HERE / "seal.json").open("x") as f:
        f.write(json.dumps(data, indent=2)+"\n")
    print(json.dumps({"status": "SEALED", "seal_sha256": digest(HERE / "seal.json"),
                      "report_sha256": current["report_sha256"]}, indent=2))


if __name__ == "__main__":
    main()
