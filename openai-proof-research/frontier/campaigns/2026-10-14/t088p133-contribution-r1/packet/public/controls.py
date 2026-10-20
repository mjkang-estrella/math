#!/usr/bin/env python3
"""Copied tamper controls for the T088P133 contribution-review packet.

Copies the review root into a temporary directory INSIDE this root's controls/ area, then runs the
read-only verifier against the detached anchors on intact and tampered copies. Expectations:
  intact: PASS; flip of review.md / reading-limits.md / MANIFEST.json / FINAL.json / REPORT.md: FAIL;
  extra file: FAIL; deleted file: FAIL.
Prints "CONTROLS ALL AS EXPECTED <n>" and exits 0 iff every case behaves as expected.
Writes only under CONTROLS_TMP (deleted afterwards) inside the copied tree location given by --tmp.
"""
import argparse, hashlib, json, os, shutil, subprocess, sys


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def run_verify(root, anchors):
    return subprocess.run(
        [sys.executable, os.path.join(root, "packet", "public", "verify.py"),
         "--root", root, "--manifest-sha256", anchors["manifest"],
         "--final-sha256", anchors["final"], "--report-sha256", anchors["report"]],
        capture_output=True, text=True)


def flip(path):
    with open(path, "r+b") as f:
        b = f.read(1)
        f.seek(0)
        f.write(bytes([b[0] ^ 1]))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--anchors", required=True, help="JSON file with manifest/final/report sha256")
    ap.add_argument("--tmp", required=True, help="scratch dir INSIDE the review root")
    a = ap.parse_args()
    src = os.path.abspath(a.root)
    anchors = json.load(open(a.anchors))
    tmp = os.path.abspath(a.tmp)
    shutil.rmtree(tmp, ignore_errors=True)
    os.makedirs(tmp)

    cases = []  # (name, expect_pass, mutate-fn or None)
    cases.append(("intact", True, None))
    for name, rel in (("flip-review", "packet/public/review.md"),
                      ("flip-reading-limits", "packet/public/reading-limits.md"),
                      ("flip-manifest", "packet/MANIFEST.json"),
                      ("flip-final", "FINAL.json"),
                      ("flip-report", "REPORT.md")):
        cases.append((name, False, ("flip", rel)))
    cases.append(("extra-file", False, ("extra", None)))
    cases.append(("delete-file", False, ("delete", "packet/public/reading-limits.md")))

    results, allok = [], True
    for name, expect, mut in cases:
        dst = os.path.join(tmp, name)
        shutil.copytree(src, dst, ignore=shutil.ignore_patterns("controls", "scratch"))
        if mut:
            kind, rel = mut
            if kind == "flip":
                flip(os.path.join(dst, rel))
            elif kind == "extra":
                open(os.path.join(dst, "packet", "public", "unexpected.txt"), "w").write("x")
            elif kind == "delete":
                os.remove(os.path.join(dst, rel))
        r = run_verify(dst, anchors)
        passed = r.returncode == 0
        ok = passed == expect
        allok &= ok
        results.append(dict(case=name, expect_pass=expect, exit=r.returncode,
                            first_line=(r.stdout.strip().splitlines() or [""])[0], as_expected=ok))
        shutil.rmtree(dst)
    shutil.rmtree(tmp, ignore_errors=True)
    print(json.dumps(results, indent=1))
    print("CONTROLS %s %d" % ("ALL AS EXPECTED" if allok else "MISMATCH", len(cases)))
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
