#!/usr/bin/env python3
"""Reason-checked integrity controls for verify_review.py, run only on copies.

usage: review_controls.py <package dir> --scratch /var/tmp/NEW --repo ROOT --out FILE

The package is copied (without MANIFEST.json and controls-result.json) into a fresh
scratch directory outside the package and sealed there. Every case then works on its
own fresh copy of that sealed base. The original package and repository are only read.
"""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys

EXCLUDE = {"MANIFEST.json", "controls-result.json"}


def run_verify(verifier, target, anchor, repo=None):
    cmd = [sys.executable, "-B", verifier, "verify", target, "--anchor", anchor]
    if repo:
        cmd += ["--repo", repo]
    p = subprocess.run(cmd, capture_output=True, text=True)
    out = p.stdout.strip()
    reason = out[len("FAIL: "):] if out.startswith("FAIL: ") else out
    return p.returncode, reason


def sha(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("package")
    ap.add_argument("--scratch", required=True)
    ap.add_argument("--repo", required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    pkg = os.path.realpath(a.package)
    scratch = os.path.realpath(a.scratch)
    if scratch == pkg or scratch.startswith(pkg + os.sep) or pkg.startswith(scratch + os.sep):
        sys.exit("scratch must be disjoint from the package")
    if os.path.lexists(scratch):
        sys.exit("scratch must not exist")
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
    verifier = os.path.join(base, "verify_review.py")
    seal = subprocess.run([sys.executable, "-B", verifier, "seal", base],
                          capture_output=True, text=True, check=True)
    anchor = seal.stdout.strip()
    assert anchor == sha(os.path.join(base, "MANIFEST.json"))
    tool = os.path.join(scratch, "verify_review.py")
    shutil.copy2(verifier, tool)

    fake_repo = os.path.join(scratch, "repo")
    with open(os.path.join(base, "evidence.json"), "rb") as fh:
        anchors = json.loads(fh.read().decode("utf-8"))["external_anchors_verified"]
    for rel in sorted(anchors):
        dst = os.path.join(fake_repo, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copy2(os.path.join(a.repo, rel), dst)

    counter = [0]

    def fresh():
        counter[0] += 1
        d = os.path.join(scratch, "case%02d" % counter[0], "pkg")
        shutil.copytree(base, d, symlinks=True)
        return d

    def flip(h):
        return ("0" if h[0] != "0" else "1") + h[1:]

    def reseal_raw(d, data):
        with open(os.path.join(d, "MANIFEST.json"), "wb") as fh:
            fh.write(data)
        return hashlib.sha256(data).hexdigest()

    cases = []

    def case(name, expect_ok, expect_reason, target, anc, repo=None):
        rc, reason = run_verify(tool, target, anc, repo)
        accepted = rc == 0
        ok = accepted == expect_ok and (expect_ok or reason == expect_reason)
        cases.append({"case": name, "accepted": accepted, "returncode": rc,
                      "reason": reason, "expected_reason": expect_reason, "ok": ok})

    case("positive", True, "PASS_IDENTITY_ONLY", fresh(), anchor)
    case("positive-with-repo", True, "PASS_IDENTITY_ONLY", fresh(), anchor, fake_repo)
    case("wrong-anchor", False, "external anchor mismatch", fresh(), flip(anchor))
    case("malformed-anchor", False, "bad anchor", fresh(), anchor[:-1] + "g")

    d = fresh()
    with open(os.path.join(d, "review.md"), "ab") as fh:
        fh.write(b"\n")
    case("changed-payload", False, "hash mismatch", d, anchor)

    d = fresh()
    p = os.path.join(d, "review.md")
    with open(p, "r", encoding="utf-8") as fh:
        t = fh.read()
    with open(p, "w", encoding="utf-8") as fh:
        fh.write(t.replace("**REPAIR_REQUIRED_T117Q_MANUSCRIPT**", "**PASS_FULL_MANUSCRIPT_T117Q**", 1))
    case("verdict-edit", False, "hash mismatch", d, anchor)

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
    with open(os.path.join(d, "__pycache__", "x.pyc"), "wb") as fh:
        fh.write(b"\0")
    case("bytecode-cache", False, "exact inventory mismatch", d, anchor)

    d = fresh()
    ev = os.path.join(d, "evidence.json")
    moved = os.path.join(os.path.dirname(d), "evidence.json")
    shutil.move(ev, moved)
    os.symlink(moved, ev)
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
    anc_link = os.path.join(scratch, "anclink")
    os.symlink(os.path.dirname(d), anc_link)
    case("ancestor-symlink", False, "symlink root or ancestor", os.path.join(anc_link, "pkg"), anchor)

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
    with open(os.path.join(d, "review.md"), "ab") as fh:
        fh.write(b"tamper\n")
    subprocess.run([sys.executable, "-B", tool, "seal", d], capture_output=True, check=True)
    case("self-reseal", False, "external anchor mismatch", d, anchor)

    d = fresh()
    with open(os.path.join(d, "MANIFEST.json"), "rb") as fh:
        raw = fh.read().decode("utf-8")
    dup = raw.replace('"format":', '"format": "x",\n "format":', 1).encode("utf-8")
    case("duplicate-key", False, "duplicate key", d, reseal_raw(d, dup))

    d = fresh()
    with open(os.path.join(d, "MANIFEST.json"), "rb") as fh:
        man = json.loads(fh.read().decode("utf-8"))
    man["files"].append({"path": "../outside", "sha256": "0" * 64, "size": 0})
    case("unsafe-path", False, "unsafe path", d,
         reseal_raw(d, (json.dumps(man, indent=1, sort_keys=True) + "\n").encode("utf-8")))

    d = fresh()
    with open(os.path.join(d, "MANIFEST.json"), "rb") as fh:
        man = json.loads(fh.read().decode("utf-8"))
    man["files"] = [e for e in man["files"] if e["path"] != "evidence.json"]
    case("omitted-member", False, "exact inventory mismatch", d,
         reseal_raw(d, (json.dumps(man, indent=1, sort_keys=True) + "\n").encode("utf-8")))

    bad_repo = os.path.join(scratch, "repo-bad")
    shutil.copytree(fake_repo, bad_repo)
    tex = os.path.join(bad_repo, "frontier/campaigns/2026-10-14/t117q-manuscript-v1/main.tex")
    with open(tex, "ab") as fh:
        fh.write(b"%\n")
    case("external-input-changed", False, "external input mismatch", fresh(), anchor, bad_repo)

    result = {
        "role": "identity controls on /var/tmp copies; not mathematical evidence",
        "pre_final_base_anchor": anchor,
        "base_members": sorted(n for n in os.listdir(base) if n != "MANIFEST.json"),
        "cases": cases,
        "all_ok": all(c["ok"] for c in cases),
        "accepted_cases": [c["case"] for c in cases if c["accepted"]],
    }
    with open(a.out, "w", encoding="utf-8") as fh:
        json.dump(result, fh, indent=1, sort_keys=True)
        fh.write("\n")
    print("cases=%d all_ok=%s accepted=%s" % (len(cases), result["all_ok"], result["accepted_cases"]))
    return 0 if result["all_ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
