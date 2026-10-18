#!/usr/bin/env python3
"""Identity verifier for the T117Q manuscript review r1 package.

verify <dir> --anchor HEX [--repo ROOT]
    Accept only if MANIFEST.json hashes to the externally supplied anchor and the
    directory contains exactly the listed regular files with matching hashes.
    With --repo, also recheck the frozen external inputs recorded in evidence.json.
seal <dir>
    Write MANIFEST.json for the current contents (used only on copies and for the
    final seal). Self-computed hashes are not an external trust source.

Prints PASS_IDENTITY_ONLY or FAIL: <reason>. Identity checks are not mathematics.
"""
import argparse
import hashlib
import json
import os
import re
import stat
import sys

FORMAT = "t117q-manuscript-review-r1/1"
MANIFEST = "MANIFEST.json"


class Fail(Exception):
    pass


def sha256_bytes(b):
    return hashlib.sha256(b).hexdigest()


def no_duplicates(pairs):
    out = {}
    for k, v in pairs:
        if k in out:
            raise Fail("duplicate key")
        out[k] = v
    return out


def safe_rel(p):
    if not isinstance(p, str) or not p or p.startswith("/") or "\\" in p or "\0" in p:
        return False
    parts = p.split("/")
    return all(x not in ("", ".", "..") for x in parts)


def check_root(root):
    path = os.path.abspath(root)
    cur = path
    while True:
        if os.path.islink(cur):
            raise Fail("symlink root or ancestor")
        parent = os.path.dirname(cur)
        if parent == cur:
            break
        cur = parent
    if not os.path.isdir(path):
        raise Fail("not a directory")
    return path


def walk(root):
    files, dirs = set(), set()
    for dirpath, dirnames, filenames in os.walk(root, followlinks=False):
        for name in sorted(dirnames + filenames):
            full = os.path.join(dirpath, name)
            rel = os.path.relpath(full, root).replace(os.sep, "/")
            st = os.lstat(full)
            if stat.S_ISLNK(st.st_mode):
                raise Fail("symlink")
            if stat.S_ISDIR(st.st_mode):
                dirs.add(rel)
            elif stat.S_ISREG(st.st_mode) and st.st_nlink == 1:
                files.add(rel)
            elif rel != MANIFEST:
                raise Fail("nonregular or hardlink")
    return files, dirs


def load_manifest(root):
    mp = os.path.join(root, MANIFEST)
    try:
        st = os.lstat(mp)
    except FileNotFoundError:
        raise Fail("missing manifest")
    if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
        raise Fail("unsafe manifest")
    with open(mp, "rb") as fh:
        raw = fh.read()
    return raw


def verify(root, anchor, repo=None):
    if not re.fullmatch(r"[0-9a-f]{64}", anchor or ""):
        raise Fail("bad anchor")
    root = check_root(root)
    raw = load_manifest(root)
    if sha256_bytes(raw) != anchor:
        raise Fail("external anchor mismatch")
    try:
        man = json.loads(raw.decode("utf-8"), object_pairs_hook=no_duplicates)
    except Fail:
        raise
    except Exception:
        raise Fail("malformed manifest")
    if not isinstance(man, dict) or set(man) != {"format", "files", "directories"} \
            or man["format"] != FORMAT or not isinstance(man["files"], list) \
            or not isinstance(man["directories"], list):
        raise Fail("malformed manifest")
    listed = {}
    for e in man["files"]:
        if not isinstance(e, dict) or set(e) != {"path", "sha256", "size"}:
            raise Fail("malformed manifest")
        if not safe_rel(e["path"]) or e["path"] == MANIFEST:
            raise Fail("unsafe path")
        if e["path"] in listed:
            raise Fail("duplicate path")
        listed[e["path"]] = e
    for d in man["directories"]:
        if not safe_rel(d):
            raise Fail("unsafe path")
    files, dirs = walk(root)
    files.discard(MANIFEST)
    if files != set(listed) or dirs != set(man["directories"]):
        raise Fail("exact inventory mismatch")
    for p, e in sorted(listed.items()):
        with open(os.path.join(root, p), "rb") as fh:
            b = fh.read()
        if len(b) != e["size"] or sha256_bytes(b) != e["sha256"]:
            raise Fail("hash mismatch")
    if repo is not None:
        with open(os.path.join(root, "evidence.json"), "rb") as fh:
            ev = json.loads(fh.read().decode("utf-8"), object_pairs_hook=no_duplicates)
        anchors = ev.get("external_anchors_verified")
        if not isinstance(anchors, dict) or not anchors:
            raise Fail("malformed evidence")
        for rel, want in sorted(anchors.items()):
            if not safe_rel(rel):
                raise Fail("unsafe path")
            full = os.path.join(os.path.abspath(repo), rel)
            if os.path.islink(full) or not os.path.isfile(full):
                raise Fail("external input mismatch")
            with open(full, "rb") as fh:
                if sha256_bytes(fh.read()) != want:
                    raise Fail("external input mismatch")


def seal(root):
    root = check_root(root)
    mp = os.path.join(root, MANIFEST)
    if os.path.lexists(mp):
        os.remove(mp)
    files, dirs = walk(root)
    entries = []
    for p in sorted(files):
        with open(os.path.join(root, p), "rb") as fh:
            b = fh.read()
        entries.append({"path": p, "sha256": sha256_bytes(b), "size": len(b)})
    man = {"format": FORMAT, "files": entries, "directories": sorted(dirs)}
    data = (json.dumps(man, indent=1, sort_keys=True) + "\n").encode("utf-8")
    with open(mp, "wb") as fh:
        fh.write(data)
    return sha256_bytes(data)


def main(argv=None):
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    v = sub.add_parser("verify")
    v.add_argument("dir")
    v.add_argument("--anchor", required=True)
    v.add_argument("--repo")
    s = sub.add_parser("seal")
    s.add_argument("dir")
    a = ap.parse_args(argv)
    try:
        if a.cmd == "verify":
            verify(a.dir, a.anchor, a.repo)
            print("PASS_IDENTITY_ONLY")
        else:
            print(seal(a.dir))
        return 0
    except Fail as exc:
        print("FAIL: %s" % exc)
        return 1


if __name__ == "__main__":
    sys.exit(main())
