#!/usr/bin/env python3
"""Reason-checked controls for the T117Q manuscript closure review r3 verifier.

review_controls.py <sealed-package-dir> --anchor HEX --repo ROOT

Every case runs on disposable copies under /var/tmp; the package and ROOT are only read.
Fake repositories contain copies of the needed anchored files only. Each case must be
accepted or rejected as expected, with the expected reason. Prints a JSON result.
Controls exercise the verifier; they are not mathematical evidence.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

C = "frontier/campaigns/2026-10-14/"
V2_TEX = C + "t117q-manuscript-v2/main.tex"
V2_PDF = C + "t117q-manuscript-v2/main.pdf"
V3_TEX = C + "t117q-manuscript-v3/main.tex"
V3_PDF = C + "t117q-manuscript-v3/main.pdf"
V3_BUILD = C + "t117q-manuscript-v3/build.py"
FORMAL = C + "t117q-formal-v1/rebuild.py"
CLOSURE_FILES = [V2_TEX, V2_PDF, V3_TEX, V3_PDF, V3_BUILD, FORMAL]


def run(pkg, *args):
    r = subprocess.run([sys.executable, "-B", str(Path(pkg) / "verify_review.py"), *args],
                       text=True, capture_output=True)
    return r.returncode, r.stdout + r.stderr


def sha(data):
    return hashlib.sha256(data).hexdigest()


def fake_repo(base, repo, files, name):
    dest = base / name
    for rel in files:
        target = dest / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(Path(repo) / rel, target)
    return dest


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("package")
    ap.add_argument("--anchor", required=True)
    ap.add_argument("--repo", required=True)
    args = ap.parse_args()
    src = Path(args.package).absolute()
    repo = Path(args.repo).absolute()
    anchors = json.loads((src / "evidence.json").read_text())["external_anchors_verified"]
    os.makedirs("/var/tmp/t117q-msrev-r3-controls", exist_ok=True)
    results = []
    with tempfile.TemporaryDirectory(prefix="run-", dir="/var/tmp/t117q-msrev-r3-controls") as tmp:
        base = Path(tmp)

        def case(name, expect_ok, reason, mutate=None, mode="verify", repo_arg=None):
            pkg = base / ("pkg-" + name)
            shutil.copytree(src, pkg)
            anchor = args.anchor
            if mutate:
                out = mutate(pkg)
                if isinstance(out, tuple):
                    pkg, anchor = out
                elif isinstance(out, str):
                    anchor = out
                elif isinstance(out, Path):
                    pkg = out
            cli = [mode, str(pkg), "--anchor", anchor]
            if repo_arg is not None:
                cli += ["--repo", str(repo_arg)]
            code, text = run(pkg if Path(pkg).exists() else src, *cli)
            ok = code == 0
            if ok != expect_ok or reason not in text:
                raise AssertionError((name, code, text))
            results.append({"case": name, "accepted": ok, "returncode": code, "reason": reason})

        def raw_manifest_anchor(edit):
            def mutate(pkg):
                m = pkg / "MANIFEST.json"
                data = edit(m.read_text())
                m.write_text(data)
                return sha(data.encode())
            return mutate

        def append(rel):
            def mutate(pkg):
                with open(pkg / rel, "a") as fh:
                    fh.write("\nchanged\n")
            return mutate

        def remove(rel):
            return lambda pkg: (pkg / rel).unlink()

        def symlink_member(pkg):
            (pkg / "review.md").unlink()
            (pkg / "review.md").symlink_to("reading-limits.md")

        def fifo_member(pkg):
            (pkg / "review.md").unlink()
            os.mkfifo(pkg / "review.md")

        def root_link(pkg):
            link = base / "root-alias"
            link.symlink_to(pkg, target_is_directory=True)
            return link

        def ancestor_link(pkg):
            link = base / "ancestor-alias"
            link.symlink_to(base, target_is_directory=True)
            return link / pkg.name

        def self_reseal(pkg):
            append("review.md")(pkg)
            subprocess.run([sys.executable, "-B", str(pkg / "verify_review.py"), "seal", str(pkg)],
                           check=True, capture_output=True)

        def unsafe_path(text):
            man = json.loads(text)
            man["files"].append({"path": "../outside", "sha256": "0" * 64, "size": 0})
            return json.dumps(man)

        # Identity cases.
        case("positive", True, "PASS_IDENTITY_ONLY")
        case("wrong-anchor", False, "external anchor mismatch", lambda p: "0" * 64)
        case("malformed-anchor", False, "bad anchor", lambda p: "xyz")
        case("changed-member", False, "hash mismatch", append("review.md"))
        case("missing-member", False, "exact inventory mismatch", remove("reading-limits.md"))
        case("extra-file", False, "exact inventory mismatch", lambda p: (p / "extra").write_text("x") and None)
        case("extra-directory", False, "exact inventory mismatch", lambda p: (p / "extra").mkdir())
        case("root-symlink", False, "symlink root or ancestor", root_link)
        case("ancestor-symlink", False, "symlink root or ancestor", ancestor_link)
        case("member-symlink", False, "symlink member", symlink_member)
        case("member-hardlink", False, "nonregular or hardlink",
             lambda p: os.link(p / "review.md", base / "review-hardlink"))
        case("fifo-member", False, "nonregular or hardlink", fifo_member)
        case("manifest-hardlink", False, "unsafe manifest",
             lambda p: os.link(p / "MANIFEST.json", base / "manifest-hardlink"))
        case("missing-manifest", False, "missing manifest", remove("MANIFEST.json"))
        case("duplicate-key-manifest", False, "duplicate key",
             raw_manifest_anchor(lambda t: t.replace("{", '{\n "format": "dup",', 1)))
        case("unsafe-path-manifest", False, "unsafe path", raw_manifest_anchor(unsafe_path))
        case("wrong-format-manifest", False, "malformed manifest",
             raw_manifest_anchor(lambda t: t.replace("t117q-manuscript-review-r3/1", "other/1")))
        case("self-reseal", False, "external anchor mismatch", self_reseal)

        # External-input cases.
        case("repo-positive", True, "PASS_IDENTITY_ONLY", repo_arg=repo)
        tampered = fake_repo(base, repo, anchors, "repo-tampered")
        with open(tampered / C / "t117q-manuscript-v3/README.md", "ab") as fh:
            fh.write(b"\n")
        case("repo-tampered", False, "external input mismatch", repo_arg=tampered)
        missing = fake_repo(base, repo, anchors, "repo-missing")
        (missing / V3_PDF).unlink()
        case("repo-missing", False, "external input mismatch", repo_arg=missing)

        # Closure cases.
        case("closure-positive", True, "PASS_CLOSURE_CHECKS", mode="closure", repo_arg=repo)
        reverted = fake_repo(base, repo, CLOSURE_FILES, "closure-reverted")
        shutil.copyfile(reverted / V2_TEX, reverted / V3_TEX)
        case("closure-reverted-source", False, "four option repairs absent", mode="closure",
             repo_arg=reverted)
        extra = fake_repo(base, repo, CLOSURE_FILES, "closure-extra")
        tex = (extra / V3_TEX).read_bytes()
        (extra / V3_TEX).write_bytes(tex.replace(b"Theorem", b"Theorem ", 1))
        case("closure-extra-source-change", False, "source change beyond four option repairs",
             mode="closure", repo_arg=extra)
        oldpdf = fake_repo(base, repo, CLOSURE_FILES, "closure-v2-pdf")
        shutil.copyfile(oldpdf / V2_PDF, oldpdf / V3_PDF)
        case("closure-en-dash-pdf", False, "dash glyph in reproduction paragraph", mode="closure",
             repo_arg=oldpdf)
        formal = fake_repo(base, repo, CLOSURE_FILES, "closure-formal")
        src_formal = (formal / FORMAL).read_text()
        (formal / FORMAL).write_text(src_formal.replace("'--cache'", "'--cache-dir'", 1))
        case("closure-formal-option", False, "formal option mismatch", mode="closure",
             repo_arg=formal)
        anchored = fake_repo(base, repo, CLOSURE_FILES, "closure-anchor")
        with open(anchored / V3_BUILD, "a") as fh:
            fh.write("# changed\n")
        case("closure-anchor", False, "closure anchor mismatch", mode="closure",
             repo_arg=anchored)

    print(json.dumps({"identity_and_typesetting_only": True, "pre_final_anchor": args.anchor,
                      "cases": len(results), "results": results}, indent=1))


if __name__ == "__main__":
    main()
