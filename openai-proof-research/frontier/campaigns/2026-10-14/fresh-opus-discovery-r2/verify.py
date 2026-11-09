#!/usr/bin/env python3
"""Read-only identity verifier for fresh-opus-discovery-r1-corrected. Fails closed.

Trust model: the ONLY anchor is the externally supplied --anchor hash, compared against
sha256 of the RAW BYTES of seal.json (read in binary; no newline normalization, so a
CRLF-folded seal does NOT match an LF anchor). Every file's path/bytes/sha256 (and, for
private-source files, the git blob id) is recomputed and compared DIRECTLY against the
frozen arrays inside seal.json. seal.sha256 and the derived manifests are NOT anchors;
manifests are merely listed, authenticated files.

Integrity discipline:
- every listed and on-disk file is lstat'd BEFORE any open; it must be a regular file
  (rejects fifo/socket/device -> no read hang) with st_nlink==1 (rejects hardlinks);
- every ancestor directory within the packet must be a real directory, not a symlink;
- the on-disk set of files AND of directories must equal the seal's recorded sets exactly
  (rejects extra/missing files and extra/missing/symlinked directories);
- duplicate paths and duplicate private-source blob ids in the seal are rejected;
- absolute / path-traversal seal entries are rejected.

This rejects the paired-tamper case (payload + its mutable-manifest hash both edited,
seal.json untouched) because each payload is checked against seal.json, and it rejects a
CRLF-folded seal because the anchor is over raw bytes.

Usage:  python3 -B verify.py --anchor=<externally supplied seal sha256>
Exit 0 = all checks pass; exit 1 = any mismatch. Writes nothing."""
import hashlib, json, os, stat, sys

ROOT = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(ROOT, "..", "..", "..", ".."))
TREE = os.path.join(REPO, "sources", "preprints-tree.json")
EXPECTED_TREE_SHA256 = "eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b"
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
SPECIAL = {"seal.json", "seal.sha256"}  # anchor files, not in files[] inventory

def fail(msg):
    print("FAIL:", msg); sys.exit(1)

def sha256_file(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()

def git_blob_sha1(p):
    data = open(p, "rb").read()
    return hashlib.sha1(b"blob %d\x00" % len(data) + data).hexdigest()

def bad_path(rel):
    if not isinstance(rel, str) or not rel or rel.startswith("/") or rel.startswith("\\"):
        return True
    parts = rel.replace("\\", "/").split("/")
    return any(p in ("", "..", ".") for p in parts)

def check_file_secure(full, rel):
    # ancestors within the packet must be real directories, never symlinks
    acc = ROOT
    for p in rel.split("/")[:-1]:
        acc = os.path.join(acc, p)
        st = os.lstat(acc)
        if stat.S_ISLNK(st.st_mode):
            fail("symlink ancestor directory: " + os.path.relpath(acc, ROOT))
        if not stat.S_ISDIR(st.st_mode):
            fail("non-directory ancestor: " + os.path.relpath(acc, ROOT))
    st = os.lstat(full)  # lstat BEFORE open: never open a fifo/device/socket
    if stat.S_ISLNK(st.st_mode):
        fail("symlink file: " + rel)
    if not stat.S_ISREG(st.st_mode):
        fail("not a regular file (fifo/socket/device): " + rel)
    if st.st_nlink != 1:
        fail("hardlinked file (nlink=%d): %s" % (st.st_nlink, rel))

def main():
    anchor = None
    for a in sys.argv[1:]:
        if a.startswith("--anchor="):
            anchor = a.split("=", 1)[1].strip()
    if not anchor:
        fail("no --anchor given (external anchor required)")

    seal_path = os.path.join(ROOT, "seal.json")
    # lstat the anchor file itself before reading; require a real regular file.
    st = os.lstat(seal_path) if os.path.lexists(seal_path) else None
    if st is None:
        fail("seal.json missing")
    if stat.S_ISLNK(st.st_mode):
        fail("seal.json is a symlink")
    if not stat.S_ISREG(st.st_mode):
        fail("seal.json is not a regular file")
    raw = open(seal_path, "rb").read()              # RAW bytes, no newline normalization
    recomputed = hashlib.sha256(raw).hexdigest()
    if recomputed != anchor:
        fail("sha256(raw seal.json) != external --anchor (seal tampered / CRLF / wrong anchor)")
    # seal.sha256 is a convenience copy only; flag inconsistency but never trust it.
    sp = os.path.join(ROOT, "seal.sha256")
    if os.path.lexists(sp):
        if os.path.islink(sp):
            fail("seal.sha256 is a symlink")
        if open(sp, "rb").read().decode("utf-8", "replace").strip() != recomputed:
            fail("seal.sha256 copy inconsistent with sha256(seal.json)")

    seal = json.loads(raw.decode("utf-8"))
    if seal.get("pin") != PIN:
        fail("seal pin mismatch")
    live_tree = sha256_file(TREE)
    if live_tree != EXPECTED_TREE_SHA256:
        fail("pinned tree sha256 != stipulated external constant")
    if seal.get("external_anchor_tree_sha256") != EXPECTED_TREE_SHA256:
        fail("seal's tree anchor != stipulated external constant")

    files = seal.get("files")
    dirs = seal.get("directories")
    if not isinstance(files, list) or not files:
        fail("seal has no files inventory")
    if not isinstance(dirs, list):
        fail("seal has no directories inventory")

    seen_paths, seen_src_blobs, S = set(), set(), set()
    for f in files:
        rel = f.get("path", "")
        if bad_path(rel):
            fail("bad/traversal path in seal: %r" % rel)
        if rel in SPECIAL:
            fail("seal must not list anchor file: " + rel)
        if rel in seen_paths:
            fail("duplicate path in seal: " + rel)
        seen_paths.add(rel); S.add(rel)
        if f.get("role") == "private-source":
            b = f.get("git_blob_sha1")
            if b in seen_src_blobs:
                fail("duplicate source blob id in seal: " + str(b))
            seen_src_blobs.add(b)
    D_seal = set()
    for d in dirs:
        if bad_path(d):
            fail("bad/traversal directory in seal: %r" % d)
        D_seal.add(d)

    # Whole-inventory: enumerate disk (files + dirs), no opening of non-regular files.
    disk_files, disk_dirs = set(), set()
    for dirpath, dirnames, filenames in os.walk(ROOT, followlinks=False):
        for dn in dirnames:
            fp = os.path.join(dirpath, dn)
            rel = os.path.relpath(fp, ROOT).replace(os.sep, "/")
            std = os.lstat(fp)
            if stat.S_ISLNK(std.st_mode):
                fail("symlinked directory: " + rel)
            disk_dirs.add(rel)
        for fn in filenames:
            fp = os.path.join(dirpath, fn)
            rel = os.path.relpath(fp, ROOT).replace(os.sep, "/")
            stf = os.lstat(fp)
            if stat.S_ISLNK(stf.st_mode):
                fail("symlink file: " + rel)
            if not stat.S_ISREG(stf.st_mode):
                fail("non-regular file (fifo/socket/device) on disk: " + rel)
            if rel in SPECIAL:
                continue
            disk_files.add(rel)
    extra_f, missing_f = disk_files - S, S - disk_files
    if extra_f:
        fail("extra unlisted file(s): " + ", ".join(sorted(extra_f)))
    if missing_f:
        fail("missing file(s): " + ", ".join(sorted(missing_f)))
    extra_d, missing_d = disk_dirs - D_seal, D_seal - disk_dirs
    if extra_d:
        fail("extra unlisted directorie(s): " + ", ".join(sorted(extra_d)))
    if missing_d:
        fail("missing directorie(s): " + ", ".join(sorted(missing_d)))

    # Direct per-file authentication against the frozen seal arrays (never via manifests).
    t = json.load(open(TREE)); entries = t if isinstance(t, list) else (t.get("tree") or t.get("entries"))
    idx = {e["path"]: (e.get("sha") or e.get("id") or e.get("oid"))
           for e in entries if isinstance(e, dict) and "path" in e}
    for f in files:
        rel = f["path"]; full = os.path.join(ROOT, rel)
        check_file_secure(full, rel)                # lstat discipline BEFORE any open
        if os.path.getsize(full) != f.get("bytes"):
            fail("byte count changed: " + rel)
        if sha256_file(full) != f.get("sha256"):
            fail("sha256 changed: " + rel)
        if f.get("role") == "private-source":
            if git_blob_sha1(full) != f.get("git_blob_sha1"):
                fail("source blob changed: " + rel)
            if idx.get(f.get("repo_path", "")) != f.get("git_blob_sha1"):
                fail("source does not match pinned tree: " + rel)

    print("OK: raw-byte external anchor + seal + pinned tree verified; "
          "%d files (%d public/%d private-source/%d private-tool) and %d directories authenticated; "
          "no extra/missing/link/hardlink/non-regular/dup."
          % (len(files),
             sum(1 for f in files if f.get("role") == "public"),
             sum(1 for f in files if f.get("role") == "private-source"),
             sum(1 for f in files if f.get("role") == "private-tool"),
             len(dirs)))
    sys.exit(0)

if __name__ == "__main__":
    main()
