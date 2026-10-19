#!/usr/bin/env python3
"""Read-only integrity verifier for the T195D93 contribution review directory.

Integrity only: a successful run is not a mathematical gate.

Usage: verify.py --final-sha256 HEX [--root REVIEW_DIR] [--repo REPO_ROOT]
"""
import argparse
import hashlib
import json
import os
import stat
import sys

EXCLUDED_TOP = {"MANIFEST.json", "FINAL.json", "CONTROLS.json", "scratch"}


def _deny(event, args):
    if event == "open":
        mode = args[1] if len(args) > 1 else "r"
        flags = args[2] if len(args) > 2 else 0
        if isinstance(mode, str) and any(c in mode for c in "wax+"):
            raise PermissionError("write open denied")
        if isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND):
            raise PermissionError("write open denied")
    if event in {"os.remove", "os.rename", "os.rmdir", "os.mkdir", "os.chmod", "os.symlink",
                 "os.link", "os.truncate", "shutil.rmtree", "shutil.copyfile", "os.utime",
                 "subprocess.Popen", "os.system", "os.exec", "os.posix_spawn", "os.fork"}:
        raise PermissionError(event + " denied")


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def git_blob_sha1(path):
    with open(path, "rb") as f:
        data = f.read()
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def fail(msg):
    print(json.dumps({"status": "REJECTED", "reason": msg, "mathematical_gate": False}))
    sys.exit(1)


def walk(root):
    files, dirs = {}, []
    for dirpath, dirnames, filenames in os.walk(root, followlinks=False):
        rel_dir = os.path.relpath(dirpath, root)
        if rel_dir == ".":
            dirnames[:] = sorted(d for d in dirnames if d not in EXCLUDED_TOP)
            filenames = [n for n in filenames if n not in EXCLUDED_TOP]
        else:
            dirnames.sort()
        for d in dirnames:
            p = os.path.join(dirpath, d)
            if os.path.islink(p):
                fail("symlink directory: " + os.path.relpath(p, root))
            dirs.append(os.path.relpath(p, root))
        for n in sorted(filenames):
            p = os.path.join(dirpath, n)
            st = os.lstat(p)
            if not stat.S_ISREG(st.st_mode):
                fail("non-regular payload: " + os.path.relpath(p, root))
            files[os.path.relpath(p, root)] = st
    return files, sorted(dirs)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--final-sha256", required=True)
    here = os.path.dirname(os.path.abspath(__file__))
    ap.add_argument("--root", default=os.path.dirname(here))
    ap.add_argument("--repo", default=None)
    a = ap.parse_args()
    root = os.path.abspath(a.root)
    repo = os.path.abspath(a.repo) if a.repo else os.path.abspath(os.path.join(root, "..", "..", "..", ".."))
    sys.addaudithook(_deny)

    final_path = os.path.join(root, "FINAL.json")
    if os.path.islink(final_path) or not os.path.isfile(final_path):
        fail("FINAL.json missing or not regular")
    if sha256(final_path) != a.final_sha256:
        fail("FINAL.json detached hash mismatch")
    with open(final_path, "rb") as f:
        final = json.loads(f.read())

    man_path = os.path.join(root, "MANIFEST.json")
    if os.path.islink(man_path) or sha256(man_path) != final["manifest_sha256"]:
        fail("MANIFEST.json hash mismatch")
    if sha256(os.path.join(root, "REVIEW.md")) != final["review_sha256"]:
        fail("REVIEW.md hash mismatch")
    with open(man_path, "rb") as f:
        manifest = json.loads(f.read())

    files, dirs = walk(root)
    if sorted(files) != sorted(manifest["files"]):
        extra = sorted(set(files) - set(manifest["files"]))
        missing = sorted(set(manifest["files"]) - set(files))
        fail("payload set mismatch extra=%s missing=%s" % (extra, missing))
    if dirs != sorted(manifest["directories"]):
        fail("directory set mismatch")
    for rel, rec in manifest["files"].items():
        st = files[rel]
        p = os.path.join(root, rel)
        if st.st_size != rec["bytes"] or stat.S_IMODE(st.st_mode) != rec["mode"] or st.st_nlink != rec["nlink"]:
            fail("metadata mismatch: " + rel)
        if sha256(p) != rec["sha256"]:
            fail("content mismatch: " + rel)
    for rel, mode in manifest["directory_modes"].items():
        if stat.S_IMODE(os.lstat(os.path.join(root, rel)).st_mode) != mode:
            fail("directory mode mismatch: " + rel)

    with open(os.path.join(root, "public", "reading.json"), "rb") as f:
        reading = json.loads(f.read())
    checked = 0
    externals = dict(reading["detached_author_anchors"])
    for b in reading["bodies"]:
        externals[b["path"]] = b["sha256"]
    externals[reading["preprints_tree"]["path"]] = reading["preprints_tree"]["sha256"]
    src = reading["pinned_source"]
    externals[src["path"]] = src["sha256"]
    for rel, want in sorted(externals.items()):
        p = os.path.join(repo, rel)
        if os.path.islink(p) or not os.path.isfile(p):
            fail("external missing: " + rel)
        if sha256(p) != want:
            fail("external hash mismatch: " + rel)
        checked += 1
    if git_blob_sha1(os.path.join(repo, src["path"])) != src["git_blob_sha1"]:
        fail("pinned source git blob mismatch")
    with open(os.path.join(repo, reading["preprints_tree"]["path"]), "rb") as f:
        tree = json.loads(f.read())
    entries = tree["tree"] if isinstance(tree, dict) else tree
    if isinstance(tree, dict) and tree.get("truncated") is not False:
        fail("preprints tree not marked untruncated")
    if len(entries) != reading["preprints_tree"]["entries"]:
        fail("preprints tree entry count mismatch")
    hit = [e for e in entries if e.get("path") == src["tree_path"]]
    if len(hit) != 1 or hit[0].get("sha") != src["git_blob_sha1"]:
        fail("pinned source not matched in complete preprints tree")

    print(json.dumps({
        "status": "INTEGRITY_ONLY_OK",
        "mathematical_gate": False,
        "payloads": len(files),
        "directories": len(dirs),
        "external_hashes_checked": checked,
        "verdict_recorded": final.get("verdict_conditional_on_correctness"),
    }, sort_keys=True))


if __name__ == "__main__":
    main()
