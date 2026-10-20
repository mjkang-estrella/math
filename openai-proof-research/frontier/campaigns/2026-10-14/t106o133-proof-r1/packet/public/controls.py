"""Copied controls for the T106O133 correctness review r1.

    python -B packet/public/controls.py --root ROOT --project PROJECT --finalhash DETACHED_SHA256

All mutations happen on copies in a temporary directory under ROOT/controls/, which is removed
afterwards. The receipt ROOT/controls/artifact-controls.json is outside the packet and is not
bound by FINAL. The original review and author inputs are only read.
"""
import argparse
import datetime
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
CONTEXT = [
    "AGENTS.md",
    "sources/upstream.json",
    "sources/preprints-tree.json",
    "frontier/campaigns/2026-10-14/discovery-structural-r133-parent/review-context-r1.txt",
    "frontier/campaigns/2026-10-14/discovery-structural-r133-parent/proof-r1-brief-prepared.txt",
]
AUTHOR = "frontier/campaigns/2026-10-14/fresh-structural-discovery-r133"


def sha(p):
    with open(p, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def verify(root, project, finalhash):
    r = subprocess.run([sys.executable, "-B", os.path.join(root, "packet", "public", "verify.py"),
                        "--root", root, "--project", project, "--finalhash", finalhash],
                       capture_output=True, text=True)
    return r.returncode


def copy_review(src, dst):
    os.makedirs(dst)
    for f in ("FINAL.json", "REPORT.md"):
        shutil.copy2(os.path.join(src, f), os.path.join(dst, f))
    shutil.copytree(os.path.join(src, "packet"), os.path.join(dst, "packet"),
                    ignore=shutil.ignore_patterns("__pycache__"))


def flip(path):
    with open(path, "rb") as fh:
        data = bytearray(fh.read())
    data[len(data) // 2] ^= 1
    with open(path, "wb") as fh:
        fh.write(bytes(data))


def reseal(root):
    sys.path.insert(0, os.path.join(root, "packet", "public"))
    import importlib
    seal = importlib.import_module("seal")
    importlib.reload(seal)
    sys.path.pop(0)
    old = json.load(open(os.path.join(root, "FINAL.json")))["manifest_sha256"]
    new = seal.write_manifest(root)
    rp = os.path.join(root, "REPORT.md")
    text = open(rp).read().replace(old, new)
    with open(rp, "w") as fh:
        fh.write(text)
    return seal.write_final(root)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--project", required=True)
    ap.add_argument("--finalhash", required=True)
    a = ap.parse_args()
    root, proj = os.path.abspath(a.root), os.path.abspath(a.project)
    cdir = os.path.join(root, "controls")
    os.makedirs(cdir, exist_ok=True)
    tmp = tempfile.mkdtemp(prefix="run-", dir=cdir)
    results = []

    def record(name, rc, expect_pass):
        ok = (rc == 0) == expect_pass
        results.append({"control": name, "exit": rc, "expected": "pass" if expect_pass else "fail", "ok": ok})
        print(("ok   " if ok else "FAIL ") + f"{name}: exit {rc}")

    try:
        record("original review, real project", verify(root, proj, a.finalhash), True)
        record("original review, wrong detached hash", verify(root, proj, "0" * 64), False)

        def fresh(name):
            d = os.path.join(tmp, name)
            copy_review(root, d)
            return d

        c = fresh("copy-clean")
        record("copied review, real project", verify(c, proj, a.finalhash), True)

        c = fresh("copy-review-edit")
        flip(os.path.join(c, "packet", "public", "review.md"))
        record("copied review.md one-bit change", verify(c, proj, a.finalhash), False)

        c = fresh("copy-extra-file")
        open(os.path.join(c, "packet", "public", "extra.txt"), "w").write("x\n")
        record("copied packet extra file", verify(c, proj, a.finalhash), False)

        c = fresh("copy-report-edit")
        with open(os.path.join(c, "REPORT.md"), "a") as fh:
            fh.write(" ")
        record("copied REPORT.md appended byte", verify(c, proj, a.finalhash), False)

        c = fresh("copy-source-resealed")
        flip(os.path.join(c, "packet", "private", "src106", "sections", "lists.tex"))
        newhash = reseal(c)
        record("copied source change resealed (blob check only)", verify(c, proj, newhash), False)

        fake = os.path.join(tmp, "fake-project")
        for rel in CONTEXT:
            os.makedirs(os.path.dirname(os.path.join(fake, rel)), exist_ok=True)
            shutil.copy2(os.path.join(proj, rel), os.path.join(fake, rel))
        shutil.copytree(os.path.join(proj, AUTHOR), os.path.join(fake, AUTHOR))
        c = fresh("copy-for-fake-project")
        record("copied review, copied project", verify(c, fake, a.finalhash), True)
        flip(os.path.join(fake, AUTHOR, "packet", "public", "proof.md"))
        record("copied author proof.md one-bit change", verify(c, fake, a.finalhash), False)
        flip(os.path.join(fake, AUTHOR, "packet", "public", "proof.md"))
        open(os.path.join(fake, AUTHOR, "scratch", "extra.txt"), "w").write("x\n")
        record("copied author root extra file", verify(c, fake, a.finalhash), False)
        os.remove(os.path.join(fake, AUTHOR, "scratch", "extra.txt"))
        flip(os.path.join(fake, CONTEXT[3]))
        record("copied review-context change", verify(c, fake, a.finalhash), False)
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    receipt = {
        "when": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
        "finalhash": a.finalhash,
        "controls": results,
        "all_ok": all(r["ok"] for r in results),
        "note": "Artifact controls only; not a mathematical verdict.",
    }
    with open(os.path.join(cdir, "artifact-controls.json"), "w") as fh:
        json.dump(receipt, fh, indent=1)
        fh.write("\n")
    print("CONTROLS PASS" if receipt["all_ok"] else "CONTROLS FAIL")
    return 0 if receipt["all_ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
