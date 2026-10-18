#!/usr/bin/env python3
"""Independent read-only seal verifier for the T338N review directory
(t338n-proof-r1). Written by the reviewer; not derived from the author's
verify.py.

Semantics:
- Reads MANIFEST.json: {"files": {relative_path: sha256_hex}}.
- Walks the directory recursively. Every entry must be a regular file or a
  directory; symlinks, fifos, devices, and sockets are rejected. Dotfile
  entries are not specially treated: exact membership only.
- The set of regular files present must equal the manifest key set plus
  exactly "MANIFEST.json". No extra, no missing files.
- Every listed file's SHA256 must match.
- If --manifest-sha256 HEX is given, the SHA256 of MANIFEST.json itself must
  equal HEX (external seal anchor).
- The verifier never writes into the target directory. --self-test operates
  on scratch copies under a temporary directory and exercises one positive
  control plus reason-checked negative controls (tamper, extra file, missing
  file, symlink injection, wrong anchor). Exit 0 iff every control behaves.

Usage:
  python3 -B verify.py --dir DIR [--manifest-sha256 HEX]
  python3 -B verify.py --dir DIR --self-test
"""

import argparse
import hashlib
import json
import os
import shutil
import sys
import tempfile


class Reject(Exception):
    pass


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def collect(root):
    """Return {relpath: abspath} for regular files; reject links/nonregular."""
    found = {}
    for dirpath, dirnames, filenames in os.walk(root, followlinks=False):
        for name in dirnames:
            full = os.path.join(dirpath, name)
            if os.path.islink(full):
                raise Reject(f"symlinked directory rejected: {full}")
        for name in filenames:
            full = os.path.join(dirpath, name)
            rel = os.path.relpath(full, root)
            if os.path.islink(full):
                raise Reject(f"symlink rejected: {rel}")
            if not os.path.isfile(full):
                raise Reject(f"non-regular file rejected: {rel}")
            found[rel] = full
    return found


def verify_dir(root, manifest_sha256=None):
    """Return None on success; raise Reject with a reason on failure."""
    if not os.path.isdir(root):
        raise Reject(f"not a directory: {root}")
    manifest_path = os.path.join(root, "MANIFEST.json")
    if os.path.islink(manifest_path) or not os.path.isfile(manifest_path):
        raise Reject("MANIFEST.json missing or not a regular file")
    if manifest_sha256 is not None:
        actual = sha256_file(manifest_path)
        if actual != manifest_sha256.lower():
            raise Reject(
                f"manifest hash mismatch: expected {manifest_sha256.lower()}, "
                f"got {actual}")
    with open(manifest_path, "r", encoding="utf-8") as f:
        manifest = json.load(f)
    files = manifest.get("files")
    if not isinstance(files, dict) or not files:
        raise Reject("MANIFEST.json has no nonempty 'files' object")
    for rel, digest in files.items():
        if not isinstance(rel, str) or not isinstance(digest, str):
            raise Reject("malformed manifest entry")
        if rel != os.path.normpath(rel) or rel.startswith(("/", "..")):
            raise Reject(f"unsafe manifest path: {rel!r}")

    found = collect(root)
    expected = set(files)
    actual = set(found) - {"MANIFEST.json"}
    for rel in sorted(expected - actual):
        raise Reject(f"missing file: {rel}")
    for rel in sorted(actual - expected):
        raise Reject(f"unexpected file: {rel}")
    for rel in sorted(expected):
        digest = sha256_file(found[rel])
        if digest != files[rel].lower():
            raise Reject(f"hash mismatch: {rel}")
    return None


def run_verified(root, manifest_sha256=None):
    try:
        verify_dir(root, manifest_sha256)
    except Reject as e:
        return False, str(e)
    return True, "PASS"


def self_test(root):
    checks = []

    def expect(name, ok, reason, want_ok, want_sub):
        good = (ok == want_ok) and (want_sub in reason)
        checks.append((name, good, reason))

    with tempfile.TemporaryDirectory(prefix="t338n-verify-") as tmp:
        pristine = os.path.join(tmp, "pristine")
        shutil.copytree(root, pristine, symlinks=False)

        ok, reason = run_verified(pristine)
        expect("positive", ok, reason, True, "PASS")

        tampered = os.path.join(tmp, "tampered")
        shutil.copytree(root, tampered, symlinks=False)
        target = os.path.join(tampered, "review.md")
        with open(target, "ab") as f:
            f.write(b"x")
        ok, reason = run_verified(tampered)
        expect("negative:tamper", ok, reason, False, "hash mismatch")

        extra = os.path.join(tmp, "extra")
        shutil.copytree(root, extra, symlinks=False)
        with open(os.path.join(extra, "injected.md"), "w") as f:
            f.write("injected")
        ok, reason = run_verified(extra)
        expect("negative:extra", ok, reason, False, "unexpected file")

        missing = os.path.join(tmp, "missing")
        shutil.copytree(root, missing, symlinks=False)
        os.remove(os.path.join(missing, "reading-limits.md"))
        ok, reason = run_verified(missing)
        expect("negative:missing", ok, reason, False, "missing file")

        linked = os.path.join(tmp, "linked")
        shutil.copytree(root, linked, symlinks=False)
        victim = os.path.join(linked, "reading-limits.md")
        os.remove(victim)
        os.symlink(os.path.join(root, "reading-limits.md"), victim)
        ok, reason = run_verified(linked)
        expect("negative:symlink", ok, reason, False, "symlink rejected")

        ok, reason = run_verified(pristine, manifest_sha256="0" * 64)
        expect("negative:anchor", ok, reason, False, "manifest hash mismatch")

    all_good = True
    for name, good, reason in checks:
        print(f"[{'PASS' if good else 'FAIL'}] self-test {name}: {reason}")
        all_good &= good
    return all_good


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", required=True)
    ap.add_argument("--manifest-sha256", default=None)
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()

    if args.self_test:
        return 0 if self_test(args.dir) else 1

    ok, reason = run_verified(args.dir, args.manifest_sha256)
    print(("PASS_SEALED" if ok else "FAIL") + f": {reason}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
