#!/usr/bin/env python3
"""Verify a path-filtered history and optionally push it to the authorized repo.

The source checkout and its branches are never modified. Only committed contents
of openai-proof-research are exported. Unreviewed proposals retain their labels.
Run from any directory; requires git. No force push is performed.
"""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

PREFIX = "openai-proof-research"
REMOTE = "https://github.com/mjkang-estrella/math"


def git(cwd, *args, **kwargs):
    return subprocess.run(["git", "-C", str(cwd), *args], check=True, **kwargs)


def output(cwd, *args):
    return git(cwd, *args, stdout=subprocess.PIPE, text=True).stdout.strip()


def marks(path):
    return dict(line.split() for line in path.read_text().splitlines())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--push", action="store_true")
    args = parser.parse_args()
    source = Path(output(Path(__file__).resolve().parent, "rev-parse", "--show-toplevel"))
    source_head = output(source, "rev-parse", "refs/heads/main")
    source_tree = output(source, "rev-parse", f"{source_head}:{PREFIX}")
    git_dir = Path(output(source, "rev-parse", "--absolute-git-dir"))
    receipt_path = git_dir / "openai-proof-publication.json"
    with tempfile.TemporaryDirectory(prefix="openai-proof-publication-") as temp:
        temp = Path(temp)
        public = temp / "public.git"
        git(temp, "init", "--bare", "--quiet", str(public))
        stream = temp / "history.export"
        old_marks = temp / "source.marks"
        new_marks = temp / "public.marks"
        with stream.open("wb") as handle:
            git(source, "fast-export", "--signed-tags=strip", "--tag-of-filtered-object=drop",
                f"--export-marks={old_marks}", "refs/heads/main", "--", PREFIX,
                stdout=handle)
        with stream.open("rb") as handle:
            git(public, "fast-import", "--quiet", f"--export-marks={new_marks}", stdin=handle)
        public_head = output(public, "rev-parse", "refs/heads/main")
        public_tree = output(public, "rev-parse", f"{public_head}:{PREFIX}")
        if public_tree != source_tree:
            raise RuntimeError("Filtered tree differs from committed source tree")
        commits = output(public, "rev-list", "refs/heads/main").splitlines()
        for commit in commits:
            paths = output(public, "ls-tree", "-r", "--name-only", commit).splitlines()
            if not paths or any(not p.startswith(PREFIX + "/") for p in paths):
                raise RuntimeError(f"Unauthorized or empty path set in {commit}")
        objects = output(public, "rev-list", "--objects", "refs/heads/main").splitlines()
        object_ids = [line.split(" ", 1)[0] for line in objects]
        sizes = git(public, "cat-file", "--batch-check=%(objectname) %(objecttype) %(objectsize)",
                    input="\n".join(object_ids) + "\n", text=True, stdout=subprocess.PIPE).stdout
        largest_blob = 0
        for line in sizes.splitlines():
            oid, kind, size = line.split()
            if kind == "blob":
                largest_blob = max(largest_blob, int(size))
                if int(size) >= 100 * 1024 * 1024:
                    raise RuntimeError(f"GitHub oversized blob: {oid}")
        git(public, "fsck", "--full", "--no-reflogs", stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        old, new = marks(old_marks), marks(new_marks)
        commit_set = set(commits)
        mapping = {oid: new[mark] for mark, oid in old.items()
                   if mark in new and new[mark] in commit_set}
        receipt = {
            "remote": REMOTE, "prefix": PREFIX, "source_head": source_head,
            "public_head": public_head, "subtree": public_tree,
            "verified_commits": len(commits), "verified_objects": len(objects),
            "largest_blob_bytes": largest_blob, "commit_mapping": mapping,
            "path_audit": "PASS: every path of every exported commit is within the authorized prefix",
            "tree_audit": "PASS: committed project subtree is byte-identical",
            "pushed": False,
        }
        if args.push:
            git(public, "push", REMOTE, "refs/heads/main:refs/heads/main")
            remote = output(public, "ls-remote", REMOTE, "refs/heads/main").split()
            if not remote or remote[0] != public_head:
                raise RuntimeError("Push completed but remote head verification failed")
            receipt["pushed"] = True
        receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")
        print(json.dumps({k: v for k, v in receipt.items() if k != "commit_mapping"}, indent=2))
        print(f"Full commit mapping and receipt: {receipt_path}")


if __name__ == "__main__":
    main()
