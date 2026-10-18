#!/usr/bin/env python3
"""Read-only verifier for the T117Q manuscript closure review r3 package.

verify <dir> --anchor HEX [--repo ROOT]
    Accept only if MANIFEST.json hashes to the externally supplied anchor and the
    directory holds exactly the listed regular files and directories with matching
    sizes and hashes. With --repo, also recheck every external input recorded under
    "external_anchors_verified" in evidence.json.
closure <dir> --anchor HEX --repo ROOT
    verify, then re-run the R1 closure checks read-only against ROOT: v3 main.tex is v2
    main.tex plus exactly the four -{}- option repairs; the p.14 Reproduction paragraph
    of the v3 PDF (pdftotext to stdout) prints the four options in ASCII with no dash
    glyphs; the printed option names match build.py and the formal rebuild.py. The
    closure inputs are compared with the recorded anchors last.
seal <dir>
    Write MANIFEST.json for the current contents. Used on scratch copies and for the
    final seal only; a self-computed hash is never an external trust source.

Prints PASS_IDENTITY_ONLY / PASS_CLOSURE_CHECKS or FAIL: <reason>.
Identity, text and build checks are not mathematics.
"""
import argparse
import hashlib
import json
import os
import re
import stat
import subprocess
import sys

FORMAT = "t117q-manuscript-review-r3/1"
MANIFEST = "MANIFEST.json"
EVIDENCE = "evidence.json"
CAMPAIGN = "frontier/campaigns/2026-10-14/"
V2_TEX = CAMPAIGN + "t117q-manuscript-v2/main.tex"
V3_TEX = CAMPAIGN + "t117q-manuscript-v3/main.tex"
V3_PDF = CAMPAIGN + "t117q-manuscript-v3/main.pdf"
V3_BUILD = CAMPAIGN + "t117q-manuscript-v3/build.py"
FORMAL = CAMPAIGN + "t117q-formal-v1/rebuild.py"
REPAIRS = [b"build.py --output", b"\\texttt{--output}", b"\\texttt{--lean}", b"\\texttt{--cache}"]
PRINTED_COMMAND = "python3 -B build.py --output /var/tmp/NEW-PDF-BUILD"
DASH_GLYPHS = "\u2010\u2011\u2012\u2013\u2014\u2015\u2212"


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
        raise Fail("malformed json")


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
                raise Fail("symlink member")
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


def load_evidence(root):
    ev = strict_json(read_regular(os.path.join(root, EVIDENCE)))
    if not isinstance(ev, dict):
        raise Fail("malformed evidence")
    return ev


def repo_file(repo, rel):
    if not is_safe_rel(rel):
        raise Fail("unsafe path")
    full = os.path.join(os.path.abspath(repo), rel)
    if os.path.islink(full) or not os.path.isfile(full):
        raise Fail("external input mismatch")
    with open(full, "rb") as fh:
        return full, fh.read()


def check_repo(root, repo):
    anchors = load_evidence(root).get("external_anchors_verified")
    if not isinstance(anchors, dict) or not anchors:
        raise Fail("malformed evidence")
    for rel, want in sorted(anchors.items()):
        if not isinstance(want, str):
            raise Fail("malformed evidence")
        if digest(repo_file(repo, rel)[1]) != want:
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
    return root


def declared_options(source):
    return set(re.findall(r"add_argument\(\s*'(--[a-z]+)'", source))


def closure(root, repo):
    _, v2 = repo_file(repo, V2_TEX)
    _, v3 = repo_file(repo, V3_TEX)
    rebuilt = v2
    for target in REPAIRS:
        if rebuilt.count(target) != 1:
            raise Fail("v2 repair target not unique")
        rebuilt = rebuilt.replace(target, target.replace(b"--", b"-{}-"))
    if v3 == v2:
        raise Fail("four option repairs absent")
    if v3 != rebuilt:
        raise Fail("source change beyond four option repairs")

    pdf, _ = repo_file(repo, V3_PDF)
    try:
        text = subprocess.run(["pdftotext", "-raw", "-f", "14", "-l", "14", pdf, "-"],
                              check=True, capture_output=True).stdout.decode("utf-8")
    except (OSError, subprocess.CalledProcessError, UnicodeDecodeError):
        raise Fail("pdftotext failed")
    start, end = text.find("Reproduction."), text.find("formal-coverage limits.")
    if start < 0 or end < start:
        raise Fail("reproduction paragraph not found on p.14")
    para = text[start:end]
    if any(ch in para for ch in DASH_GLYPHS):
        raise Fail("dash glyph in reproduction paragraph")
    if PRINTED_COMMAND not in [line.strip() for line in para.split("\n")]:
        raise Fail("printed command not ASCII as expected")
    found = re.findall(r"(?<![\w-])--[a-z]+", para)
    if sorted(found) != sorted(["--output", "--output", "--lean", "--cache"]):
        raise Fail("printed options mismatch")

    _, build = repo_file(repo, V3_BUILD)
    _, formal = repo_file(repo, FORMAL)
    if "--output" not in declared_options(build.decode("utf-8")):
        raise Fail("build.py option mismatch")
    if declared_options(formal.decode("utf-8")) != {"--output", "--lean", "--cache"}:
        raise Fail("formal option mismatch")

    anchors = load_evidence(root).get("closure_anchors")
    if not isinstance(anchors, dict) or set(anchors) != {V2_TEX, V3_TEX, V3_PDF, V3_BUILD, FORMAL}:
        raise Fail("malformed evidence")
    for rel, want in sorted(anchors.items()):
        if digest(repo_file(repo, rel)[1]) != want:
            raise Fail("closure anchor mismatch")


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
    pc = sub.add_parser("closure")
    pc.add_argument("dir")
    pc.add_argument("--anchor", required=True)
    pc.add_argument("--repo", required=True)
    ps = sub.add_parser("seal")
    ps.add_argument("dir")
    args = ap.parse_args(argv)
    try:
        if args.cmd == "verify":
            verify(args.dir, args.anchor, args.repo)
            print("PASS_IDENTITY_ONLY")
        elif args.cmd == "closure":
            root = verify(args.dir, args.anchor)
            closure(root, args.repo)
            print("PASS_CLOSURE_CHECKS (identity and typesetting only)")
        else:
            print(seal(args.dir))
    except Fail as exc:
        print("FAIL: " + str(exc), file=sys.stderr)
        return 1
    except OSError as exc:
        print("FAIL: io error " + exc.__class__.__name__, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
