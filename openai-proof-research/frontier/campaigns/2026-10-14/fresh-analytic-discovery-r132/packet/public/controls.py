#!/usr/bin/env python3
# MIT License. Runs verify.py on disposable copies of the sealed root (intact + mutations). Never touches the original.
import json
import os
import shutil
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True


def run(verify, root, m, f, r):
    p = subprocess.run([sys.executable, "-B", verify, "--root", root, "--manifest-sha256", m, "--final-sha256", f,
                        "--report-sha256", r], capture_output=True, text=True)
    return p.returncode, p.stdout.strip().splitlines()[0] if p.stdout.strip() else ""


def main():
    root, m, f, r, tmpbase = sys.argv[1:6]
    verify = os.path.join(root, "packet/public/verify.py")
    results = []

    def case(name, mutate, expect_pass, anchors=(m, f, r)):
        d = tempfile.mkdtemp(dir=tmpbase)
        c = os.path.join(d, "root")
        shutil.copytree(root, c, symlinks=True, ignore=shutil.ignore_patterns("CONTROL-RESULTS.json", "control-tmp"))
        mutate(c)
        code, line = run(verify, c, *anchors)
        ok = (code == 0) == expect_pass
        results.append({"case": name, "expect_pass": expect_pass, "exit": code, "first_line": line, "as_expected": ok})
        shutil.rmtree(d)

    def flip(rel):
        def g(c):
            p = os.path.join(c, rel)
            b = bytearray(open(p, "rb").read())
            b[len(b) // 2] ^= 1
            open(p, "wb").write(bytes(b))
        return g

    case("intact", lambda c: None, True)
    case("flip-public-report", flip("packet/public/report.md"), False)
    case("flip-private-upstream", flip("packet/private/upstream/preprints/A-product-counterexample-to-the-simplex-maximum-for-projection-body-volume-September-24-2026/build/main.tex"), False)
    case("flip-notes", flip("work/notes.md"), False)
    case("flip-manifest", flip("packet/MANIFEST.json"), False)
    case("flip-final", flip("FINAL.json"), False)
    case("flip-report", flip("REPORT.md"), False)
    case("extra-file", lambda c: open(os.path.join(c, "work/extra.txt"), "w").write("x"), False)
    case("extra-dir", lambda c: os.mkdir(os.path.join(c, "work/extra")), False)
    case("delete-file", lambda c: os.remove(os.path.join(c, "scratch/psi2.py")), False)
    case("symlink", lambda c: os.symlink("notes.md", os.path.join(c, "work/link.md")), False)
    case("wrong-manifest-anchor", lambda c: None, False, ("0" * 64, f, r))
    case("wrong-final-anchor", lambda c: None, False, (m, "0" * 64, r))
    case("wrong-report-anchor", lambda c: None, False, (m, f, "0" * 64))
    print(json.dumps({"cases": len(results), "all_as_expected": all(x["as_expected"] for x in results), "results": results}, indent=1))


if __name__ == "__main__":
    main()
