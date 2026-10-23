#!/usr/bin/env python3
"""Read-only exact payload verification. Supply trusted detached hashes explicitly."""
import argparse
import hashlib
import json
import stat
from pathlib import Path

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def inventory(root):
    found = {}
    def walk(path, rel):
        st = path.lstat()
        if stat.S_ISLNK(st.st_mode):
            raise ValueError("symlink forbidden: " + rel)
        mode = format(stat.S_IMODE(st.st_mode), "04o")
        if stat.S_ISDIR(st.st_mode):
            found[rel] = {"kind": "directory", "mode": mode}
            for child in sorted(path.iterdir(), key=lambda p: p.name):
                walk(child, child.name if rel == "." else rel + "/" + child.name)
        elif stat.S_ISREG(st.st_mode):
            found[rel] = {"kind": "file", "mode": mode,
                          "bytes": st.st_size, "sha256": digest(path)}
        else:
            raise ValueError("nonregular payload object: " + rel)
    walk(root, ".")
    return found

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--root", type=Path, required=True)
    for name in ("final", "manifest", "report"):
        p.add_argument("--" + name + "-sha", required=True)
    a = p.parse_args()
    root = a.root
    if not root.is_absolute() or root.is_symlink():
        raise ValueError("root must be an explicit absolute nonsymlink path")
    for name, suffix in (("final", "md"), ("manifest", "json"), ("report", "md")):
        expected = getattr(a, name + "_sha")
        if len(expected) != 64 or any(c not in "0123456789abcdef" for c in expected):
            raise ValueError("invalid explicit anchor: " + name)
        path = root / (name.upper() + "." + suffix)
        if path.is_symlink() or not path.is_file() or digest(path) != expected:
            raise ValueError("detached anchor mismatch: " + name)
    manifest = json.loads((root / "MANIFEST.json").read_text())
    if manifest.get("schema") != "r162u-exact-payload-v1":
        raise ValueError("manifest schema mismatch")
    if digest(Path(__file__)) != manifest["verifier_sha256"]:
        raise ValueError("verifier digest mismatch")
    actual = inventory(root / "packet")
    expected = manifest["inventory"]
    if actual != expected:
        missing = sorted(set(expected) - set(actual))
        extra = sorted(set(actual) - set(expected))
        changed = sorted(k for k in set(actual) & set(expected) if actual[k] != expected[k])
        raise ValueError("payload mismatch: " + json.dumps({"missing": missing, "extra": extra, "changed": changed}))
    print(json.dumps({"integrity": "PASS", "files": sum(v["kind"] == "file" for v in actual.values()),
                      "directories": sum(v["kind"] == "directory" for v in actual.values()),
                      "mathematical_gate": False}, sort_keys=True))

if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        raise SystemExit("REJECT: " + str(exc))
