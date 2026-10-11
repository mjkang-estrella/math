"""One-shot exclusive seal creation; never part of diagnostic replay."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
SOURCE = ROOT / "frontier/sources/i166_affine_span_braces"
REPORT = ROOT / "frontier/iterations/i166-affine-span-braces.md"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical(obj):
    return (json.dumps(obj, indent=2, sort_keys=True) + "\n").encode()


def main():
    seal_path = HERE / "seal.json"
    assert not seal_path.exists(), "Never reseal"
    inv_path, pre_path = HERE / "owned-files.json", HERE / "prevalidation.json"
    inv = json.loads(inv_path.read_text())
    pre = json.loads(pre_path.read_text())
    assert pre["status"] == "PASS" and pre["mode"] == "--prevalidate"
    assert pre["input_inventory_sha256"] == digest(inv_path)
    expected = {ROOT / e["path"] for e in inv["files"]}
    actual = {REPORT}
    for folder in (HERE, SOURCE):
        for path in folder.rglob("*"):
            assert not path.is_symlink()
            if path.is_file():
                actual.add(path)
    assert actual - {inv_path, pre_path, seal_path} == expected
    for entry in inv["files"]:
        path = ROOT / entry["path"]
        assert path.stat().st_size == entry["size"]
        assert digest(path) == entry["sha256"]
    bindings = json.loads((SOURCE / "external-bindings.json").read_text())
    for entry in bindings["files"]:
        path = ROOT / entry["path"]
        assert path.stat().st_size == entry["size"]
        assert digest(path) == entry["sha256"]
    inv["files"].append({"path": str(pre_path.relative_to(ROOT)),
                         "size": pre_path.stat().st_size,
                         "sha256": digest(pre_path)})
    inv["files"].sort(key=lambda e: e["path"])
    inv_path.write_bytes(canonical(inv))
    seal = {"schema": "i166-seal-v1",
            "inventory_sha256": digest(inv_path),
            "prevalidation_sha256": digest(pre_path),
            "report_sha256": digest(REPORT),
            "verifier_sha256": digest(HERE / "verify.py"),
            "payload_files": len(inv["files"]),
            "creation": "exclusive-create, once"}
    with seal_path.open("xb") as handle:
        handle.write(canonical(seal))
    print(json.dumps({**seal, "seal_sha256": digest(seal_path)},
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
