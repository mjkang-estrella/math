#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Copied-packet identity mutation controls. No mathematical verdict.

Every mutation runs on a fresh disposable copy under a temporary directory
(default /var/tmp). The original packets are only read and copied.
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(os.path.abspath(__file__)).parent
AUTHOR = HERE.parent / "fresh-arithmetic-discovery-r28"
AUTHOR_MANIFEST = "2a476225d2df44641e62313dfa3653fb26820879b1dc55537d0ec7a7b8e77a19"
AUTHOR_VERIFIER = "f69ed2552d049fd35ae0bfc8089eb53aca3a7763c3f7a99f4acf56d8e794164e"
ZERO = "0" * 64


def run(script, args):
    proc = subprocess.run([sys.executable, str(script), *args],
                          capture_output=True, text=True, timeout=300)
    return {"returncode": proc.returncode,
            "stdout": proc.stdout.strip(), "stderr": proc.stderr.strip()}


def fresh(src, work, name):
    dst = work / name / src.name
    shutil.copytree(src, dst, symlinks=True)
    return dst


def mutations(edit_file, delete_file, private_file):
    def edit(root):
        with open(root / edit_file, "ab") as handle:
            handle.write(b"\n")

    def delete(root):
        (root / delete_file).unlink()

    def extra_file(root):
        (root / "extra.txt").write_bytes(b"x\n")

    def extra_dir(root):
        (root / "extra-empty-dir").mkdir()

    def symlink(root):
        target = root / edit_file
        data = target.read_bytes()
        target.unlink()
        (root / (edit_file + ".real")).write_bytes(data)
        target.symlink_to(edit_file + ".real")

    def symlink_same_bytes_outside(root):
        target = root / edit_file
        outside = root.parent / "outside-copy"
        outside.write_bytes(target.read_bytes())
        target.unlink()
        target.symlink_to(outside)

    def hardlink(root):
        os.link(root / edit_file, root.parent / "hardlink-outside")

    def fifo(root):
        os.mkfifo(root / "extra.fifo")

    def private_edit(root):
        with open(root / private_file, "ab") as handle:
            handle.write(b"\n")

    return {"edit_payload_byte": edit, "delete_payload": delete,
            "extra_file": extra_file, "extra_empty_directory": extra_dir,
            "symlink_payload": symlink,
            "symlink_same_bytes_outside": symlink_same_bytes_outside,
            "hardlink_payload": hardlink, "fifo_node": fifo,
            "private_body_edit": private_edit}


def control_suite(src, script_name, good_args, wrong_sets, edit_file,
                  delete_file, private_file, work):
    results = {}
    root = fresh(src, work, "baseline")
    results["baseline"] = run(root / script_name, good_args)
    for label, args in wrong_sets.items():
        root = fresh(src, work, label)
        results[label] = run(root / script_name, args)
    for label, mutate in mutations(edit_file, delete_file, private_file).items():
        root = fresh(src, work, label)
        mutate(root)
        results[label] = run(root / script_name, good_args)
    root = fresh(src, work, "root_symlink")
    link = root.parent / "linked-root"
    link.symlink_to(root, target_is_directory=True)
    results["root_symlink_invocation"] = run(link / script_name, good_args)
    root = fresh(src, work, "ancestor_symlink")
    link = root.parent.parent / "linked-ancestor"
    link.symlink_to(root.parent, target_is_directory=True)
    results["ancestor_symlink_invocation"] = run(link / root.name / script_name, good_args)
    return results


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--target", choices=["author", "own"], required=True)
    parser.add_argument("--anchor", help="own preliminary manifest SHA256")
    parser.add_argument("--source-tree", type=Path, required=True)
    parser.add_argument("--workdir", type=Path, default=Path("/var/tmp"))
    args = parser.parse_args()
    tree = str(args.source_tree.resolve())
    work = Path(tempfile.mkdtemp(prefix="t008m-cr1-controls-", dir=args.workdir))
    if args.target == "author":
        good = ["--manifest-sha256", AUTHOR_MANIFEST, "--verifier-sha256",
                AUTHOR_VERIFIER, "--private", "--source-tree", tree]
        bad_tree = work / "bad-tree.json"
        data = json.loads(Path(tree).read_text())
        data["tree"] = [row for row in data["tree"]
                        if "The-Deligne-Drinfeld-conjecture" not in row["path"]
                        or not row["path"].endswith("04-deletion.tex")]
        bad_tree.write_text(json.dumps(data))
        wrong = {
            "wrong_manifest_anchor": ["--manifest-sha256", ZERO, "--verifier-sha256",
                                      AUTHOR_VERIFIER, "--private", "--source-tree", tree],
            "wrong_verifier_anchor": ["--manifest-sha256", AUTHOR_MANIFEST,
                                      "--verifier-sha256", ZERO, "--private",
                                      "--source-tree", tree],
            "wrong_source_tree": ["--manifest-sha256", AUTHOR_MANIFEST,
                                  "--verifier-sha256", AUTHOR_VERIFIER, "--private",
                                  "--source-tree", str(bad_tree)],
        }
        results = control_suite(
            AUTHOR, "verify.py", good, wrong, "candidate-008.md", "scope-008.md",
            "private/The-Deligne-Drinfeld-conjecture-September-23-2026/build/sections/04-deletion.tex",
            work)
        anchors = {"manifest_sha256": AUTHOR_MANIFEST, "verifier_sha256": AUTHOR_VERIFIER}
    else:
        if not args.anchor:
            parser.error("--anchor required for own target")
        author = str(AUTHOR)
        good = ["--anchor", args.anchor, "--private", "--source-tree", tree,
                "--author-dir", author]
        bad_tree = work / "bad-tree.json"
        bad_tree.write_bytes(Path(tree).read_bytes() + b"\n")
        wrong = {"wrong_manifest_anchor": ["--anchor", ZERO, "--private",
                                           "--source-tree", tree, "--author-dir", author],
                 "wrong_source_tree": ["--anchor", args.anchor, "--private",
                                       "--source-tree", str(bad_tree),
                                       "--author-dir", author],
                 "missing_author_packet": ["--anchor", args.anchor, "--private",
                                           "--source-tree", tree,
                                           "--author-dir", str(work / "absent")]}
        results = control_suite(HERE, "verify.py", good, wrong, "review.md",
                                "reading-and-limits.md",
                                "private/primary/Nisan1991-noncomm.pdf", work)
        anchors = {"preliminary_manifest_sha256": args.anchor}
    expected_pass = {"baseline"}
    summary = {k: ("PASS" if v["returncode"] == 0 else "REJECTED") for k, v in results.items()}
    ok = all((summary[k] == "PASS") == (k in expected_pass) for k in summary)
    print(json.dumps({"target": args.target, "anchors": anchors,
                      "all_controls_behaved_as_expected": ok,
                      "summary": summary, "results": results,
                      "interpretation": "Identity controls on disposable copies only; no mathematical validation."},
                     indent=2, sort_keys=True))
    shutil.rmtree(work)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
