#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT License.
"""Read-only verifier for the two-order-signing-r2 package.

Order of work:
  1. authenticate seal.json against the handoff SHA256;
  2. authenticate both inventories against the seal;
  3. check exact file membership, file types and every SHA256/size;
  4. check the r4 chain (copied r4 seal, manifests and selected files);
  5. only then replay checks.py and compare stdout byte-for-byte with the
     stored receipt;
  6. authenticate everything again.

Standard library only. Opens files read-only, writes nothing, uses no network.
A pass shows integrity and finite support only; it is not a proof of T2.
"""
import argparse
import hashlib
import json
import os
import stat
import subprocess
import sys

SEAL_SCHEMA = "two-order-signing-r2-seal-v1"
INPUT_SCHEMA = "two-order-signing-r2-input-v1"
OUTPUT_SCHEMA = "two-order-signing-r2-output-v1"
CONTROL_FILES = ("seal.json", "input-manifest.json", "output-manifest.json")
RECEIPT = "checks-receipt.txt"
CHECKER = "checks.py"
REPLAY_TIMEOUT = 900

R4_SEAL_SHA256 = "e1cda9940e5020d9e47fe6e8a8e2124e7a643b8bc3e8560beee55c55f9c0ab2d"
R4_DIR = "inputs/private/context/r4"
# copied path (relative to R4_DIR) -> which r4 inventory lists it
R4_COPIED_ENTRIES = {
    "candidate.md": "output-manifest.json",
    "original-scope.md": "output-manifest.json",
    "inputs/private/literature/thesis.txt": "input-manifest.json",
}


class Reject(Exception):
    def __init__(self, stage, message):
        super().__init__(f"FAIL[{stage}] {message}")
        self.stage = stage


def read_bytes(path):
    with open(path, "rb") as fh:
        return fh.read()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def load_json(data, stage, name):
    try:
        return json.loads(data.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise Reject(stage, f"{name} is not valid JSON: {exc}")


def safe_relpath(path):
    return (isinstance(path, str) and path and not path.startswith("/")
            and "\\" not in path
            and all(part not in ("", ".", "..") for part in path.split("/")))


def walk_files(root):
    """Return the set of regular-file relative paths; reject anything else."""
    found = set()
    for dirpath, dirnames, filenames in os.walk(root, followlinks=False):
        for name in list(dirnames) + list(filenames):
            full = os.path.join(dirpath, name)
            rel = os.path.relpath(full, root).replace(os.sep, "/")
            mode = os.lstat(full).st_mode
            if stat.S_ISLNK(mode):
                raise Reject("membership", f"symlink not allowed: {rel}")
            if name in filenames:
                if not stat.S_ISREG(mode):
                    raise Reject("membership", f"not a regular file: {rel}")
                found.add(rel)
            elif not stat.S_ISDIR(mode):
                raise Reject("membership", f"unexpected entry: {rel}")
    return found


def check_entry(root, entry, stage):
    path = entry["path"]
    data = read_bytes(os.path.join(root, path))
    if len(data) != entry["size"]:
        raise Reject(stage, f"size mismatch: {path}")
    if digest(data) != entry["sha256"]:
        raise Reject(stage, f"sha256 mismatch: {path}")
    return data


def parse_manifest(data, schema, name):
    manifest = load_json(data, "inventory", name)
    if not isinstance(manifest, dict) or set(manifest) != {"schema", "files"}:
        raise Reject("inventory", f"{name} has unexpected keys")
    if manifest["schema"] != schema:
        raise Reject("inventory", f"{name} has wrong schema")
    files = manifest["files"]
    if not isinstance(files, list):
        raise Reject("inventory", f"{name} files is not a list")
    paths = []
    for entry in files:
        if (not isinstance(entry, dict)
                or set(entry) != {"path", "sha256", "size"}
                or not safe_relpath(entry["path"])
                or not isinstance(entry["size"], int)
                or not isinstance(entry["sha256"], str)
                or len(entry["sha256"]) != 64):
            raise Reject("inventory", f"{name} has a malformed entry")
        paths.append(entry["path"])
    if paths != sorted(paths) or len(set(paths)) != len(paths):
        raise Reject("inventory", f"{name} paths are not sorted and unique")
    return files


def authenticate(root, seal_sha256):
    """Full authentication. Returns (receipt bytes, counts)."""
    seal_bytes = read_bytes(os.path.join(root, "seal.json"))
    if digest(seal_bytes) != seal_sha256:
        raise Reject("seal", "seal.json SHA256 differs from the handoff value")
    seal = load_json(seal_bytes, "seal", "seal.json")
    expected_keys = {"schema", "target_status", "acceptance_claim",
                     "r4_seal_sha256", "inventories"}
    if not isinstance(seal, dict) or set(seal) != expected_keys:
        raise Reject("seal", "seal.json has unexpected keys")
    if seal["schema"] != SEAL_SCHEMA:
        raise Reject("seal", "wrong seal schema")
    if seal["target_status"] != "UNRESOLVED" or seal["acceptance_claim"] is not False:
        raise Reject("seal", "seal status must be UNRESOLVED with no acceptance claim")
    if seal["r4_seal_sha256"] != R4_SEAL_SHA256:
        raise Reject("seal", "seal names a different r4 seal")
    inventories = seal["inventories"]
    if not isinstance(inventories, dict) or set(inventories) != {
            "input-manifest.json", "output-manifest.json"}:
        raise Reject("seal", "seal inventories are incomplete")

    manifests = {}
    for name, schema in (("input-manifest.json", INPUT_SCHEMA),
                         ("output-manifest.json", OUTPUT_SCHEMA)):
        ref = inventories[name]
        data = read_bytes(os.path.join(root, name))
        if not isinstance(ref, dict) or len(data) != ref.get("size") \
                or digest(data) != ref.get("sha256"):
            raise Reject("inventory", f"{name} does not match the seal")
        manifests[name] = parse_manifest(data, schema, name)

    inputs = manifests["input-manifest.json"]
    outputs = manifests["output-manifest.json"]
    for entry in inputs:
        if not entry["path"].startswith("inputs/"):
            raise Reject("inventory", f"input entry outside inputs/: {entry['path']}")
    for entry in outputs:
        if entry["path"].startswith("inputs/") or entry["path"] in CONTROL_FILES:
            raise Reject("inventory", f"misplaced output entry: {entry['path']}")

    declared = {e["path"] for e in inputs} | {e["path"] for e in outputs}
    actual = walk_files(root)
    expected = declared | set(CONTROL_FILES)
    missing = sorted(expected - actual)
    extra = sorted(actual - expected)
    if missing:
        raise Reject("membership", f"missing files: {missing}")
    if extra:
        raise Reject("membership", f"unlisted files: {extra}")

    contents = {}
    for entry in inputs + outputs:
        contents[entry["path"]] = check_entry(root, entry, "file")
    for required in (CHECKER, RECEIPT, "verify.py", "candidate.md",
                     "original-scope.md"):
        if required not in contents:
            raise Reject("inventory", f"required file not inventoried: {required}")

    check_r4_chain(contents)
    return contents[RECEIPT], (len(inputs), len(outputs))


def check_r4_chain(contents):
    def get(rel):
        path = f"{R4_DIR}/{rel}"
        if path not in contents:
            raise Reject("r4", f"r4 copy not inventoried: {path}")
        return contents[path]

    r4_seal_bytes = get("seal.json")
    if digest(r4_seal_bytes) != R4_SEAL_SHA256:
        raise Reject("r4", "copied r4 seal differs from the r4 handoff hash")
    r4_seal = load_json(r4_seal_bytes, "r4", "r4 seal.json")
    r4_manifests = {}
    for name in ("input-manifest.json", "output-manifest.json"):
        ref = r4_seal["inventories"][name]
        data = get(name)
        if len(data) != ref["size"] or digest(data) != ref["sha256"]:
            raise Reject("r4", f"copied r4 {name} does not match the r4 seal")
        r4_manifests[name] = {e["path"]: e for e in
                              load_json(data, "r4", f"r4 {name}")["files"]}
    for rel, inventory in R4_COPIED_ENTRIES.items():
        entry = r4_manifests[inventory].get(rel)
        data = get(rel)
        if entry is None or len(data) != entry["size"] \
                or digest(data) != entry["sha256"]:
            raise Reject("r4", f"copied r4 file {rel} does not match its r4 entry")


def replay(root):
    env = {"PATH": os.environ.get("PATH", "/usr/bin:/bin"),
           "LC_ALL": "C.UTF-8", "PYTHONDONTWRITEBYTECODE": "1",
           "PYTHONHASHSEED": "0", "PYTHONIOENCODING": "utf-8"}
    try:
        proc = subprocess.run([sys.executable, "-B", "-I", CHECKER], cwd=root,
                              env=env, stdin=subprocess.DEVNULL,
                              capture_output=True, timeout=REPLAY_TIMEOUT)
    except subprocess.TimeoutExpired:
        raise Reject("replay", "checks.py timed out")
    if proc.returncode != 0:
        raise Reject("replay", f"checks.py exited with {proc.returncode}")
    return proc.stdout


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--seal-sha256", required=True,
                        help="SHA256 of seal.json taken from the handoff")
    parser.add_argument("--root", default=os.path.dirname(os.path.abspath(__file__)),
                        help="package directory to verify (default: this file's directory)")
    args = parser.parse_args(argv)
    root = os.path.abspath(args.root)
    seal_sha256 = args.seal_sha256.strip().lower()
    try:
        receipt, (n_in, n_out) = authenticate(root, seal_sha256)
        print(f"AUTHENTICATED: inputs={n_in} outputs={n_out} r4_chain=ok", flush=True)
        fresh = replay(root)
        if fresh != receipt:
            raise Reject("replay", "fresh checks.py stdout differs from the stored receipt")
        print("REPLAY: stdout byte-identical to checks-receipt.txt", flush=True)
        receipt_again, _ = authenticate(root, seal_sha256)
        if receipt_again != receipt:
            raise Reject("reauth", "receipt changed during replay")
    except Reject as exc:
        print(f"VERIFY: {exc}")
        return 1
    except (OSError, KeyError, TypeError) as exc:
        print(f"VERIFY: FAIL[error] {type(exc).__name__}: {exc}")
        return 1
    print(f"VERIFY: PASS_integrity_and_finite_support_only files={n_in + n_out + len(CONTROL_FILES)}")
    print("SCOPE: not a proof of T2; target UNRESOLVED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
