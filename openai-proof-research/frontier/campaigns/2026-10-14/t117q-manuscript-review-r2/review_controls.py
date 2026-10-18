#!/usr/bin/env python3
"""Reason-checked integrity controls for verify_review.py, run only on copies.

usage: review_controls.py <package dir> --scratch /var/tmp/NEW --repo ROOT --out FILE

The package members (excluding MANIFEST.json and controls-result.json) are copied into
a fresh scratch directory disjoint from the package and sealed there. Each case then
mutates its own fresh copy of that sealed base. The external inputs listed in
evidence.json are copied into a scratch repository, so the real package and the real
repository are only read. A case passes only when acceptance and the printed reason
both match expectations.
"""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys

EXCLUDE = {"MANIFEST.json", "controls-result.json"}
V2_TEX = "frontier/campaigns/2026-10-14/t117q-manuscript-v2/main.tex"


def sha_file(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def call_verifier(tool, target, anchor, repo=None):
    cmd = [sys.executable, "-B", tool, "verify", target, "--anchor", anchor]
    if repo:
        cmd += ["--repo", repo]
    proc = subprocess.run(cmd, capture_output=True, text=True)
    out = proc.stdout.strip()
    return proc.returncode, out[6:] if out.startswith("FAIL: ") else out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("package")
    ap.add_argument("--scratch", required=True)
    ap.add_argument("--repo", required=True)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()
    pkg = os.path.realpath(args.package)
    scratch = os.path.realpath(args.scratch)
    if scratch == pkg or scratch.startswith(pkg + os.sep) or pkg.startswith(scratch + os.sep):
        sys.exit("scratch must be disjoint from the package")
    if os.path.lexists(scratch):
        sys.exit("scratch must not exist")
    out_path = os.path.realpath(args.out)
    if out_path.startswith(scratch + os.sep):
        sys.exit("output must not be inside scratch")
    os.makedirs(scratch)

    base = os.path.join(scratch, "base")
    os.makedirs(base)
    for name in sorted(os.listdir(pkg)):
        if name in EXCLUDE:
            continue
        src = os.path.join(pkg, name)
        if os.path.islink(src) or not os.path.isfile(src):
            sys.exit("unexpected package member type: " + name)
        shutil.copy2(src, os.path.join(base, name))
    sealer = os.path.join(base, "verify_review.py")
    anchor = subprocess.run([sys.executable, "-B", sealer, "seal", base],
                            capture_output=True, text=True, check=True).stdout.strip()
    if anchor != sha_file(os.path.join(base, "MANIFEST.json")):
        sys.exit("seal output does not match manifest bytes")
    tool = os.path.join(scratch, "verify_review.py")
    shutil.copy2(sealer, tool)

    with open(os.path.join(base, "evidence.json"), "rb") as fh:
        anchors = json.loads(fh.read().decode("utf-8"))["external_anchors_verified"]
    if V2_TEX not in anchors:
        sys.exit("evidence must anchor the v2 main.tex")
    good_repo = os.path.join(scratch, "repo")
    for rel in sorted(anchors):
        dst = os.path.join(good_repo, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copy2(os.path.join(args.repo, rel), dst)

    n = [0]

    def fresh():
        n[0] += 1
        d = os.path.join(scratch, "case%02d" % n[0], "pkg")
        shutil.copytree(base, d, symlinks=True)
        return d

    def flip(hexstr):
        return ("1" if hexstr[0] == "0" else "0") + hexstr[1:]

    def write_manifest(d, data):
        with open(os.path.join(d, "MANIFEST.json"), "wb") as fh:
            fh.write(data)
        return hashlib.sha256(data).hexdigest()

    def load_manifest(d):
        with open(os.path.join(d, "MANIFEST.json"), "rb") as fh:
            return json.loads(fh.read().decode("utf-8"))

    def dump(man):
        return (json.dumps(man, indent=1, sort_keys=True) + "\n").encode("utf-8")

    cases = []

    def case(name, expect_ok, expect_reason, target, anc, repo=None):
        rc, reason = call_verifier(tool, target, anc, repo)
        accepted = rc == 0
        ok = accepted == expect_ok and reason == expect_reason
        cases.append({"case": name, "accepted": accepted, "returncode": rc,
                      "reason": reason, "expected_reason": expect_reason, "ok": ok})

    case("positive", True, "PASS_IDENTITY_ONLY", fresh(), anchor)
    case("positive-with-repo", True, "PASS_IDENTITY_ONLY", fresh(), anchor, good_repo)
    case("wrong-anchor", False, "external anchor mismatch", fresh(), flip(anchor))
    case("malformed-anchor", False, "bad anchor", fresh(), anchor[:-1] + "g")

    d = fresh()
    with open(os.path.join(d, "review.md"), "ab") as fh:
        fh.write(b"\n")
    case("changed-payload", False, "hash mismatch", d, anchor)

    d = fresh()
    p = os.path.join(d, "review.md")
    with open(p, "r", encoding="utf-8") as fh:
        text = fh.read()
    edited = text.replace("**REPAIR_REQUIRED_T117Q_MANUSCRIPT**", "**PASS_FULL_MANUSCRIPT_T117Q**", 1)
    if edited == text:
        sys.exit("verdict marker not found in review.md")
    with open(p, "w", encoding="utf-8") as fh:
        fh.write(edited)
    case("verdict-edit", False, "hash mismatch", d, anchor)

    d = fresh()
    p = os.path.join(d, "evidence.json")
    with open(p, "rb") as fh:
        raw = fh.read()
    edited = raw.replace(b'"verdict": "REPAIR_REQUIRED_T117Q_MANUSCRIPT"',
                         b'"verdict": "PASS_FULL_MANUSCRIPT_T117Q"', 1)
    if edited == raw:
        sys.exit("verdict marker not found in evidence.json")
    with open(p, "wb") as fh:
        fh.write(edited)
    case("evidence-verdict-edit", False, "hash mismatch", d, anchor)

    d = fresh()
    os.remove(os.path.join(d, "reading-limits.md"))
    case("missing-payload", False, "exact inventory mismatch", d, anchor)

    d = fresh()
    with open(os.path.join(d, "extra.txt"), "w") as fh:
        fh.write("x\n")
    case("extra-file", False, "exact inventory mismatch", d, anchor)

    d = fresh()
    os.makedirs(os.path.join(d, "extra-dir"))
    case("extra-directory", False, "exact inventory mismatch", d, anchor)

    d = fresh()
    os.makedirs(os.path.join(d, "__pycache__"))
    with open(os.path.join(d, "__pycache__", "verify_review.cpython.pyc"), "wb") as fh:
        fh.write(b"\0")
    case("bytecode-cache", False, "exact inventory mismatch", d, anchor)

    d = fresh()
    target = os.path.join(d, "evidence.json")
    moved = os.path.join(os.path.dirname(d), "evidence.json")
    shutil.move(target, moved)
    os.symlink(moved, target)
    case("payload-symlink", False, "symlink", d, anchor)

    d = fresh()
    os.link(os.path.join(d, "evidence.json"), os.path.join(os.path.dirname(d), "hl"))
    case("payload-hardlink", False, "nonregular or hardlink", d, anchor)

    d = fresh()
    os.mkfifo(os.path.join(d, "fifo"))
    case("fifo", False, "nonregular or hardlink", d, anchor)

    d = fresh()
    link = os.path.join(os.path.dirname(d), "rootlink")
    os.symlink(d, link)
    case("root-symlink", False, "symlink root or ancestor", link, anchor)

    d = fresh()
    anc = os.path.join(scratch, "anclink")
    os.symlink(os.path.dirname(d), anc)
    case("ancestor-symlink", False, "symlink root or ancestor", os.path.join(anc, "pkg"), anchor)

    d = fresh()
    mp = os.path.join(d, "MANIFEST.json")
    real = os.path.join(os.path.dirname(d), "MANIFEST.real")
    shutil.move(mp, real)
    os.symlink(real, mp)
    case("manifest-symlink", False, "unsafe manifest", d, anchor)

    d = fresh()
    os.link(os.path.join(d, "MANIFEST.json"), os.path.join(os.path.dirname(d), "mhl"))
    case("manifest-hardlink", False, "unsafe manifest", d, anchor)

    d = fresh()
    os.remove(os.path.join(d, "MANIFEST.json"))
    case("missing-manifest", False, "missing manifest", d, anchor)

    d = fresh()
    with open(os.path.join(d, "review.md"), "ab") as fh:
        fh.write(b"tamper\n")
    subprocess.run([sys.executable, "-B", tool, "seal", d], capture_output=True, check=True)
    case("self-reseal", False, "external anchor mismatch", d, anchor)

    d = fresh()
    with open(os.path.join(d, "MANIFEST.json"), "rb") as fh:
        raw = fh.read().decode("utf-8")
    dup = raw.replace('"format":', '"format": "x",\n "format":', 1).encode("utf-8")
    case("duplicate-key", False, "duplicate key", d, write_manifest(d, dup))

    d = fresh()
    man = load_manifest(d)
    man["format"] = "t117q-manuscript-review-r1/1"
    case("wrong-format", False, "malformed manifest", d, write_manifest(d, dump(man)))

    d = fresh()
    man = load_manifest(d)
    man["files"].append({"path": "../outside", "sha256": "0" * 64, "size": 0})
    case("unsafe-path", False, "unsafe path", d, write_manifest(d, dump(man)))

    d = fresh()
    man = load_manifest(d)
    man["files"] = [e for e in man["files"] if e["path"] != "evidence.json"]
    case("omitted-member", False, "exact inventory mismatch", d, write_manifest(d, dump(man)))

    bad_repo = os.path.join(scratch, "repo-bad")
    shutil.copytree(good_repo, bad_repo)
    with open(os.path.join(bad_repo, V2_TEX), "ab") as fh:
        fh.write(b"%\n")
    case("external-input-changed", False, "external input mismatch", fresh(), anchor, bad_repo)

    result = {
        "role": "identity controls on /var/tmp copies; not mathematical evidence",
        "pre_final_base_anchor": anchor,
        "base_members": sorted(x for x in os.listdir(base) if x != "MANIFEST.json"),
        "cases": cases,
        "all_ok": all(c["ok"] for c in cases),
        "accepted_cases": [c["case"] for c in cases if c["accepted"]],
    }
    with open(out_path, "w", encoding="utf-8") as fh:
        json.dump(result, fh, indent=1, sort_keys=True)
        fh.write("\n")
    print("cases=%d all_ok=%s accepted=%s" % (len(cases), result["all_ok"], result["accepted_cases"]))
    return 0 if result["all_ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
