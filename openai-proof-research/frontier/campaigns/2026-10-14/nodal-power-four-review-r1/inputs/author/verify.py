#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""Read-only, fail-closed verifier for fresh-analytic-discovery-r13.

Writes nothing. Checks:
  1. size and SHA-256 of every file in inputs-manifest.json and
     outputs-manifest.json; no unlisted file exists in this directory;
  2. seal.json entries and the detached seal.sha256 (required unless
     --pre-seal is given); with --anchor=<sha256>, the seal must also
     match that externally reported value;
  3. frozen-scope hash, as recorded in status.json and here;
  4. Git blob SHA-1 and size of the 31 pinned source copies, against
     git-identities.json and against the live sources/preprints-tree.json;
  5. status.json is not self-passed and not counted;
  6. unchanged-input receipts: live repository copies of the snapshots in
     inputs/context/ (upstream.json must match; other files are reported).
Exit code 0 only if every check passes. Passing is integrity only.
"""
import hashlib
import json
import os
import sys

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
PROJECT = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
REVISION = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
SCOPE_SHA256 = "3348c130c424d6f753a39c6529cff81c0d923c3bb8d1eeb395327abb6734dc0f"
N_PINNED = 31
CONTEXT = {
    "inputs/context/upstream.json": ("sources/upstream.json", True),
    "inputs/context/fresh-r13-brief.txt":
        ("frontier/campaigns/2026-10-14/brenier-logconcave-parent/fresh-r13-brief.txt", False),
    "inputs/context/fresh-r13-launch.json":
        ("frontier/campaigns/2026-10-14/brenier-logconcave-parent/fresh-r13-launch.json", False),
    "inputs/context/NEW-TEN-2026-10-14.md": ("frontier/NEW-TEN-2026-10-14.md", False),
}
SEAL_FILES = {"seal.json", "seal.sha256", "verify-receipt.json",
              "inputs-manifest.json", "outputs-manifest.json"}

failures = []


def check(cond, msg):
    print(("ok   " if cond else "FAIL ") + msg)
    if not cond:
        failures.append(msg)


def read_bytes(path):
    with open(path, "rb") as fh:
        return fh.read()


def sha256(path):
    return hashlib.sha256(read_bytes(path)).hexdigest()


def git_blob(data):
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def load_json(name):
    path = os.path.join(HERE, name)
    if not os.path.exists(path):
        check(False, f"{name} exists")
        return None
    try:
        with open(path, encoding="utf-8") as fh:
            return json.load(fh)
    except ValueError:
        check(False, f"{name} parses as JSON")
        return None


def all_files():
    out = set()
    for root, dirs, files in os.walk(HERE):
        dirs[:] = [d for d in dirs if d != "__pycache__"]
        for f in files:
            out.add(os.path.relpath(os.path.join(root, f), HERE).replace(os.sep, "/"))
    return out


def manifests():
    listed = set()
    for name in ("inputs-manifest.json", "outputs-manifest.json"):
        m = load_json(name)
        if m is None:
            continue
        check(m.get("format") == "sha256-size-v1", f"{name} format")
        for e in m.get("files", []):
            p = os.path.join(HERE, e["path"])
            listed.add(e["path"])
            if not os.path.isfile(p):
                check(False, f"{e['path']} present")
                continue
            ok = os.path.getsize(p) == e["size"] and sha256(p) == e["sha256"]
            check(ok, f"{name}: {e['path']} size/sha256")
    extra = sorted(all_files() - listed - SEAL_FILES)
    check(not extra, "no unlisted files" + (f": {extra}" if extra else ""))
    pyc = [f for f in all_files() if f.endswith(".pyc")]
    check(not pyc, "no bytecode files")


def seal(pre_seal, anchor):
    if pre_seal:
        print("note seal checks skipped (--pre-seal)")
        return
    s = load_json("seal.json")
    if s is None:
        return
    check(s.get("revision") == REVISION, "seal revision")
    check(s.get("scope_sha256") == SCOPE_SHA256, "seal scope hash")
    check(s.get("counted") is False, "seal counted=false")
    for key in ("inputs", "outputs", "receipt"):
        e = s.get(key, {})
        p = os.path.join(HERE, e.get("path", "?"))
        ok = os.path.isfile(p) and os.path.getsize(p) == e.get("size") and sha256(p) == e.get("sha256")
        check(ok, f"seal binds {e.get('path')}")
    seal_hash = sha256(os.path.join(HERE, "seal.json"))
    try:
        detached = open(os.path.join(HERE, "seal.sha256"), encoding="utf-8").read().split()
        check(detached == [seal_hash, "seal.json"], "detached seal.sha256 matches seal.json")
    except OSError:
        check(False, "seal.sha256 readable")
    if anchor is not None:
        check(seal_hash == anchor, "seal.json matches external anchor")
    else:
        print("note no external anchor given; pass --anchor=<sha256> reported by the author")


def scope_and_status():
    check(sha256(os.path.join(HERE, "original-scope.md")) == SCOPE_SHA256, "original-scope.md hash")
    st = load_json("status.json")
    if st is None:
        return
    check(st.get("scope_sha256") == SCOPE_SHA256, "status scope hash")
    check(st.get("self_pass") is False, "status self_pass=false")
    check(st.get("counted") is False, "status counted=false")
    check(st.get("pinned_upstream") == "openai/math " + REVISION, "status revision")
    cand = read_bytes(os.path.join(HERE, "candidate.md")).decode("utf-8")
    check(SCOPE_SHA256 in cand, "candidate cites frozen scope hash")


def blobs():
    gi = load_json("git-identities.json")
    if gi is None:
        return
    check(gi.get("revision") == REVISION, "git-identities revision")
    files = gi.get("files", [])
    check(len(files) == N_PINNED, f"{N_PINNED} pinned identities listed")
    tree_path = os.path.join(PROJECT, "sources", "preprints-tree.json")
    try:
        with open(tree_path, encoding="utf-8") as fh:
            tree = json.load(fh)
        idx = {e["path"]: e for e in tree["tree"] if e.get("type") == "blob"}
        check(tree.get("truncated") is False, "preprints-tree.json not truncated")
    except (OSError, ValueError, KeyError):
        idx = None
        check(False, "live sources/preprints-tree.json readable")
    for e in files:
        p = os.path.join(HERE, e["local"])
        if not os.path.isfile(p):
            check(False, f"{e['local']} present")
            continue
        data = read_bytes(p)
        ok = git_blob(data) == e["git_blob_sha1"] and len(data) == e["size"]
        check(ok, f"blob {e['local']}")
        if idx is not None:
            t = idx.get(e["upstream_path"])
            check(t is not None and t["sha"] == e["git_blob_sha1"] and t.get("size") == len(data),
                  f"tree entry {e['upstream_path'].split('/')[1][:40]}.../{os.path.basename(e['local'])}")
    pinned = {f for f in all_files() if f.startswith("inputs/pinned/")}
    check(pinned == {e["local"] for e in files}, "pinned directory membership equals identities")


def receipts():
    for snap, (live, strict) in CONTEXT.items():
        sp = os.path.join(HERE, snap)
        lp = os.path.join(PROJECT, live)
        if not os.path.isfile(sp):
            check(False, f"{snap} present")
            continue
        if not os.path.isfile(lp):
            msg = f"live {live} missing"
            if strict:
                check(False, msg)
            else:
                print("note " + msg)
            continue
        same = sha256(sp) == sha256(lp)
        if strict:
            check(same, f"live {live} unchanged since snapshot")
        else:
            print(("ok   " if same else "note ") + f"live {live} "
                  + ("unchanged" if same else "CHANGED since snapshot (informational)"))
    up = load_json("inputs/context/upstream.json")
    if up is not None:
        check(up.get("commit") == REVISION, "snapshot upstream commit")


def main():
    pre_seal = "--pre-seal" in sys.argv
    anchor = None
    for a in sys.argv[1:]:
        if a.startswith("--anchor="):
            anchor = a.split("=", 1)[1].strip().lower()
    manifests()
    seal(pre_seal, anchor)
    scope_and_status()
    blobs()
    receipts()
    print("RESULT:", "ALL CHECKS PASSED" if not failures else f"{len(failures)} FAILURE(S)")
    print("meaning: integrity only; not a mathematical PASS and not a novelty finding")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
