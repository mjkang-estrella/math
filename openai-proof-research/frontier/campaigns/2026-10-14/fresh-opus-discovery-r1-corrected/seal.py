#!/usr/bin/env python3
"""One-shot sealer for fresh-opus-discovery-r1-corrected.

Builds seal.json = the single frozen anchor listing EVERY regular file in the packet
(except seal.json and seal.sha256), each with role/bytes/sha256, and for
private-source files also the git blob id cross-checked against the pinned tree.
Also records the exact set of directories under the packet. Writes derived manifests
(sources-/outputs-manifest.json), themselves listed in seal.json. seal.json is written
as raw bytes and the anchor = sha256 of those raw bytes (no newline normalization).
seal.sha256 stores that anchor as a CONVENIENCE COPY ONLY; the authoritative anchor
is supplied externally to verify.py. Refuses to seal symlinks, non-regular files
(fifo/socket/device), or hardlinked (nlink!=1) files. Writes only manifest/seal files."""
import hashlib, json, os, stat

ROOT = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(ROOT, "..", "..", "..", ".."))
TREE = os.path.join(REPO, "sources", "preprints-tree.json")
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
EXPECTED_TREE_SHA256 = "eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b"
SUPERSEDES = {"packet": "fresh-opus-discovery-r1",
              "seal_sha256": "04ccf3f1320b91b6d7999098eefaf17b8c254f3735b38655ca89ef34ede41ef4"}

SPECIAL = {"seal.json", "seal.sha256"}      # anchor files, not in files[]
MANIFESTS = {"sources-manifest.json", "outputs-manifest.json"}

def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def sha256_file(p) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()

def git_blob_sha1(p):
    data = open(p, "rb").read()
    return hashlib.sha1(b"blob %d\x00" % len(data) + data).hexdigest()

def tree_index():
    t = json.load(open(TREE))
    entries = t if isinstance(t, list) else (t.get("tree") or t.get("entries"))
    return {e["path"]: (e.get("sha") or e.get("id") or e.get("oid"))
            for e in entries if isinstance(e, dict) and "path" in e}

def role_of(rel):
    if rel.startswith("private/src/"):
        return "private-source"
    if rel.startswith("private/"):
        return "private-tool"
    return "public"

def check_ancestors_secure(rel):
    acc = ROOT
    for p in rel.split("/")[:-1]:
        acc = os.path.join(acc, p)
        st = os.lstat(acc)
        if stat.S_ISLNK(st.st_mode):
            raise SystemExit("refusing to seal: symlink ancestor: " + rel)
        if not stat.S_ISDIR(st.st_mode):
            raise SystemExit("refusing to seal: non-directory ancestor: " + rel)

def enumerate_packet():
    files, dirs = [], set()
    for dirpath, dirnames, filenames in os.walk(ROOT, followlinks=False):
        for dn in dirnames:
            fp = os.path.join(dirpath, dn)
            rel = os.path.relpath(fp, ROOT).replace(os.sep, "/")
            st = os.lstat(fp)
            if stat.S_ISLNK(st.st_mode):
                raise SystemExit("refusing to seal: symlinked directory: " + rel)
            dirs.add(rel)
        for fn in filenames:
            fp = os.path.join(dirpath, fn)
            rel = os.path.relpath(fp, ROOT).replace(os.sep, "/")
            st = os.lstat(fp)
            if stat.S_ISLNK(st.st_mode):
                raise SystemExit("refusing to seal: symlink file: " + rel)
            if not stat.S_ISREG(st.st_mode):
                raise SystemExit("refusing to seal: non-regular file (fifo/socket/device): " + rel)
            if st.st_nlink != 1:
                raise SystemExit("refusing to seal: hardlinked file (nlink=%d): %s" % (st.st_nlink, rel))
            if rel in SPECIAL or rel in MANIFESTS:
                continue
            files.append(rel)
    return sorted(set(files)), sorted(dirs)

def build_record(rel, idx):
    full = os.path.join(ROOT, rel)
    check_ancestors_secure(rel)
    rec = {"path": rel, "role": role_of(rel),
           "bytes": os.path.getsize(full), "sha256": sha256_file(full)}
    if rec["role"] == "private-source":
        repo_rel = rel[len("private/src/"):]
        rec["git_blob_sha1"] = git_blob_sha1(full)
        rec["repo_path"] = repo_rel
        rec["tree_blob_sha1"] = idx.get(repo_rel)
        rec["blob_matches_tree"] = (idx.get(repo_rel) == rec["git_blob_sha1"])
    return rec

def main():
    anchor_tree = sha256_file(TREE)
    idx = tree_index()
    base, dirs = enumerate_packet()
    files = [build_record(rel, idx) for rel in base]

    sources = [f for f in files if f["role"] == "private-source"]
    outputs = [f for f in files if f["role"] == "public"]
    json.dump({"pin": PIN, "tree_sha256": anchor_tree,
               "sources": [{k: s[k] for k in ("repo_path", "bytes", "git_blob_sha1",
                                              "tree_blob_sha1", "blob_matches_tree")}
                           for s in sources]},
              open(os.path.join(ROOT, "sources-manifest.json"), "w"), indent=2)
    json.dump({"pin": PIN, "tree_sha256": anchor_tree,
               "outputs": [{k: o[k] for k in ("path", "bytes", "sha256")} for o in outputs]},
              open(os.path.join(ROOT, "outputs-manifest.json"), "w"), indent=2)

    for rel in sorted(MANIFESTS):
        files.append(build_record(rel, idx))
    files.sort(key=lambda f: f["path"])

    seal = {
        "package": "fresh-opus-discovery-r1-corrected",
        "family": 186,
        "result": "Theorem OPT (optimality of Friedgut-Kalai hypergraph exponent r/(r-1), r>=3)",
        "status": "PROVED; contribution TECHNICAL (not a substantial nominee); count unchanged 17/20",
        "pin": PIN,
        "external_anchor_tree_sha256": anchor_tree,
        "supersedes": SUPERSEDES,
        "directories": dirs,
        "files": files,
    }
    data = (json.dumps(seal, sort_keys=True, indent=2) + "\n").encode("utf-8")
    with open(os.path.join(ROOT, "seal.json"), "wb") as f:
        f.write(data)
    anchor = sha256_bytes(data)
    with open(os.path.join(ROOT, "seal.sha256"), "wb") as f:
        f.write((anchor + "\n").encode("utf-8"))

    npub = sum(1 for f in files if f["role"] == "public")
    nsrc = sum(1 for f in files if f["role"] == "private-source")
    ntool = sum(1 for f in files if f["role"] == "private-tool")
    print("tree_sha256:", anchor_tree, "(matches stipulated:", anchor_tree == EXPECTED_TREE_SHA256, ")")
    print("files sealed:", len(files), "| public:", npub, "| private-source:", nsrc,
          "| private-tool:", ntool, "| directories:", len(dirs))
    print("sources all blob-match pinned tree:", all(s["blob_matches_tree"] for s in sources))
    print("seal.sha256 (EXTERNAL ANCHOR to report):", anchor)

if __name__ == "__main__":
    main()
