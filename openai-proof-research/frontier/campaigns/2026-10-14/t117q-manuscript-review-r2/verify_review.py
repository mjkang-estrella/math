#!/usr/bin/env python3
"""Identity verifier for the T117Q manuscript review r2 package.

verify <dir> --anchor HEX [--repo ROOT]
    Accept only if MANIFEST.json hashes to the externally supplied anchor and the
    directory holds exactly the listed regular files and directories, with matching
    sizes and hashes. With --repo, also recheck every frozen external input recorded
    under "external_anchors_verified" in evidence.json.
seal <dir>
    Write MANIFEST.json for the current contents. Used on scratch copies and for the
    final seal only; a self-computed hash is never an external trust source.

Prints PASS_IDENTITY_ONLY or FAIL: <reason>. Identity checks are not mathematics.
"""
import argparse
import hashlib
import json
import os
import re
import stat
import sys

FORMAT = "t117q-manuscript-review-r2/1"
MANIFEST = "MANIFEST.json"
EVIDENCE = "evidence.json"


class Fail(Exception):
    pass


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read_regular(path):
    st = os.lstat(path)
    if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
        raise Fail("nonregular or hardlink")
    with open(path, "rb") as fh:
        return fh.read()


def strict_json(data):
    def hook(pairs):
        obj = {}
        for key, value in pairs:
            if key in obj:
                raise Fail("duplicate key")
            obj[key] = value
        return obj
    try:
        return json.loads(data.decode("utf-8"), object_pairs_hook=hook)
    except Fail:
        raise
    except Exception:
        raise Fail("malformed manifest")


def is_safe_rel(rel):
    if not isinstance(rel, str) or not rel or rel.startswith("/"):
        return False
    if "\\" in rel or "\0" in rel:
        return False
    return all(part not in ("", ".", "..") for part in rel.split("/"))


def resolve_root(root):
    path = os.path.abspath(root)
    probe = path
    while True:
        if os.path.islink(probe):
            raise Fail("symlink root or ancestor")
        up = os.path.dirname(probe)
        if up == probe:
            break
        probe = up
    if not os.path.isdir(path):
        raise Fail("not a directory")
    return path


def inventory(root):
    files, dirs = set(), set()
    for here, subdirs, names in os.walk(root, followlinks=False):
        for name in sorted(subdirs + names):
            full = os.path.join(here, name)
            rel = os.path.relpath(full, root).replace(os.sep, "/")
            st = os.lstat(full)
            if stat.S_ISLNK(st.st_mode):
                raise Fail("symlink")
            if stat.S_ISDIR(st.st_mode):
                dirs.add(rel)
            elif rel == MANIFEST:
                continue
            elif stat.S_ISREG(st.st_mode) and st.st_nlink == 1:
                files.add(rel)
            else:
                raise Fail("nonregular or hardlink")
    return files, dirs


def manifest_bytes(root):
    path = os.path.join(root, MANIFEST)
    if not os.path.lexists(path):
        raise Fail("missing manifest")
    st = os.lstat(path)
    if not stat.S_ISREG(st.st_mode) or st.st_nlink != 1:
        raise Fail("unsafe manifest")
    with open(path, "rb") as fh:
        return fh.read()


def parse_manifest(raw):
    man = strict_json(raw)
    if not isinstance(man, dict) or set(man) != {"format", "files", "directories"}:
        raise Fail("malformed manifest")
    if man["format"] != FORMAT:
        raise Fail("malformed manifest")
    if not isinstance(man["files"], list) or not isinstance(man["directories"], list):
        raise Fail("malformed manifest")
    listed = {}
    for entry in man["files"]:
        if not isinstance(entry, dict) or set(entry) != {"path", "sha256", "size"}:
            raise Fail("malformed manifest")
        if not is_safe_rel(entry["path"]) or entry["path"] == MANIFEST:
            raise Fail("unsafe path")
        if entry["path"] in listed:
            raise Fail("duplicate path")
        listed[entry["path"]] = entry
    for rel in man["directories"]:
        if not is_safe_rel(rel):
            raise Fail("unsafe path")
    if len(set(man["directories"])) != len(man["directories"]):
        raise Fail("duplicate path")
    return listed, set(man["directories"])


def check_repo(root, repo):
    ev = strict_json(read_regular(os.path.join(root, EVIDENCE)))
    anchors = ev.get("external_anchors_verified") if isinstance(ev, dict) else None
    if not isinstance(anchors, dict) or not anchors:
        raise Fail("malformed evidence")
    base = os.path.abspath(repo)
    for rel, want in sorted(anchors.items()):
        if not is_safe_rel(rel) or not isinstance(want, str):
            raise Fail("unsafe path")
        full = os.path.join(base, rel)
        if os.path.islink(full) or not os.path.isfile(full):
            raise Fail("external input mismatch")
        with open(full, "rb") as fh:
            if digest(fh.read()) != want:
                raise Fail("external input mismatch")


def verify(root, anchor, repo=None):
    if not re.fullmatch(r"[0-9a-f]{64}", anchor or ""):
        raise Fail("bad anchor")
    root = resolve_root(root)
    raw = manifest_bytes(root)
    if digest(raw) != anchor:
        raise Fail("external anchor mismatch")
    listed, want_dirs = parse_manifest(raw)
    files, dirs = inventory(root)
    if files != set(listed) or dirs != want_dirs:
        raise Fail("exact inventory mismatch")
    for rel, entry in sorted(listed.items()):
        data = read_regular(os.path.join(root, rel))
        if len(data) != entry["size"] or digest(data) != entry["sha256"]:
            raise Fail("hash mismatch")
    if repo is not None:
        check_repo(root, repo)


def seal(root):
    root = resolve_root(root)
    path = os.path.join(root, MANIFEST)
    if os.path.lexists(path):
        os.remove(path)
    files, dirs = inventory(root)
    entries = []
    for rel in sorted(files):
        data = read_regular(os.path.join(root, rel))
        entries.append({"path": rel, "sha256": digest(data), "size": len(data)})
    man = {"format": FORMAT, "files": entries, "directories": sorted(dirs)}
    out = (json.dumps(man, indent=1, sort_keys=True) + "\n").encode("utf-8")
    with open(path, "wb") as fh:
        fh.write(out)
    return digest(out)


def main(argv=None):
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    pv = sub.add_parser("verify")
    pv.add_argument("dir")
    pv.add_argument("--anchor", required=True)
    pv.add_argument("--repo")
    ps = sub.add_parser("seal")
    ps.add_argument("dir")
    args = ap.parse_args(argv)
    try:
        if args.cmd == "verify":
            verify(args.dir, args.anchor, args.repo)
            print("PASS_IDENTITY_ONLY")
        else:
            print(seal(args.dir))
        return 0
    except Fail as exc:
        print("FAIL: %s" % exc)
        return 1


if __name__ == "__main__":
    sys.exit(main())
