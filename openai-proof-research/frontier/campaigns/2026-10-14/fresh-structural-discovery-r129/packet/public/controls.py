#!/usr/bin/env python3
"""Disposable copied artifact controls, exclusively inside the owned root. MIT."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import runpy
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--root", type=Path, required=True)
    p.add_argument("--project", type=Path, required=True)
    p.add_argument("--finalhash", required=True)
    a = p.parse_args()
    root, project = a.root.absolute(), a.project.absolute()
    api = runpy.run_path(str(root / "packet/public/verify.py"))
    inventory, sha = api["inventory"], api["sha"]
    before = inventory(root)
    workspace = root / ".control-work"
    if workspace.exists():
        raise RuntimeError("refusing preexisting control workspace")
    workspace.mkdir()
    results = []
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")

    def reseal(copy):
        manifest = {"version": 1, "entries": inventory(copy / "packet", True)}
        (copy / "packet/MANIFEST.json").write_text(json.dumps(manifest, sort_keys=True, indent=2) + "\n")
        f = json.loads((copy / "FINAL.json").read_text())
        f["manifest_sha256"] = sha((copy / "packet/MANIFEST.json").read_bytes())
        (copy / "FINAL.json").write_text(json.dumps(f, sort_keys=True, indent=2) + "\n")
        anchor = sha((copy / "FINAL.json").read_bytes())
        (copy / "FINAL.sha256").write_text(anchor + "\n")
        return anchor

    def edit_json(path, fn):
        obj = json.loads(path.read_text())
        fn(obj)
        path.write_text(json.dumps(obj, indent=2) + "\n")

    def one(name, mutate=None, reanchor=False, expected=1, anchor=None, omit=False, audit=None):
        copy = workspace / name
        shutil.copytree(root, copy, ignore=lambda directory, names: {".control-work", "artifact-controls.json"} if Path(directory) == root else set())
        if mutate:
            mutate(copy)
        detached = reseal(copy) if reanchor else (anchor or a.finalhash)
        script = copy / "packet/public/verify.py"
        if audit:
            code = ("import runpy,sys,socket; m=runpy.run_path(sys.argv[1]); m['install_audit'](); " +
                    ("open(sys.argv[2], 'w').write('forbidden')" if audit == "write" else "socket.socket()"))
            cmd = [sys.executable, "-B", "-c", code, str(script), str(copy / "denied-write")]
        else:
            cmd = [sys.executable, "-B", str(script), "--root", str(copy), "--project", str(project)]
            if not omit:
                cmd += ["--finalhash", detached]
        # Mutated symlink/hardlink inventories intentionally cannot pass inventory().
        def fingerprint(path):
            rows = {}
            for entry in sorted(path.rglob("*")):
                s = entry.lstat()
                rel = entry.relative_to(path).as_posix()
                rows[rel] = [s.st_mode, s.st_nlink, os.readlink(entry) if entry.is_symlink() else
                             (hashlib.sha256(entry.read_bytes()).hexdigest() if entry.is_file() else None)]
            return rows
        prior = fingerprint(copy)
        result = subprocess.run(cmd, env=env, capture_output=True, text=True)
        unchanged = prior == fingerprint(copy)
        okay = (result.returncode == 0) if expected == 0 else (result.returncode != 0)
        if audit:
            okay = okay and "readonly verifier denied" in result.stderr
        results.append({"case": name, "expected": "accept" if expected == 0 else "reject",
                        "exit": result.returncode, "expected_outcome": okay, "copied_input_unchanged": unchanged,
                        "output": (result.stdout + result.stderr)[-600:]})
        shutil.rmtree(copy)

    try:
        one("baseline", expected=0)
        one("missing-detached-anchor", omit=True)
        one("wrong-detached-anchor", anchor="0" * 64)
        one("changed-public", lambda c: (c / "packet/public/report.md").write_text("changed\n"))
        one("missing-public", lambda c: (c / "packet/public/rights.md").unlink())
        one("extra-file", lambda c: (c / "packet/extra").write_text("extra\n"))
        one("extra-empty-directory", lambda c: (c / "packet/empty").mkdir())
        one("changed-mode", lambda c: (c / "packet/public/rights.md").chmod(0o600))
        def link(c):
            q = c / "packet/public/rights.md"
            q.unlink()
            q.symlink_to("report.md")
        one("symlink-payload", link)
        def hardlink(c):
            q = c / "packet/public/rights.md"
            q.unlink()
            os.link(c / "packet/public/report.md", q)
        one("hardlink-payload", hardlink)
        one("outside-report-change", lambda c: (c / "REPORT.md").write_text("changed\n"))
        one("extra-root-item", lambda c: (c / "unexpected").write_text("extra\n"))
        one("canonical-full-record-resealed", lambda c: edit_json(c / "packet/private/canonical.json", lambda x: x[0]["record"].update(mode="100755")), True)
        one("raw-url-resealed", lambda c: edit_json(c / "packet/private/canonical.json", lambda x: x[0].update(url="https://example.invalid/")), True)
        def source_change(c):
            record = json.loads((c / "packet/private/canonical.json").read_text())[0]
            with (c / "packet" / record["local"]).open("ab") as f:
                f.write(b"\nchanged\n")
        one("source-body-resealed", source_change, True)
        one("primary-pdf-resealed", lambda c: (c / "packet/private/primary/handbook-ch8.pdf").write_bytes(b"changed"), True)
        one("history-binding-resealed", lambda c: edit_json(c / "packet/private/history/records.json", lambda x: x[0].update(original="AGENTS.md")), True)
        one("input-binding-resealed", lambda c: edit_json(c / "packet/private/context/input-bindings.json", lambda x: x[0].update(sha256="0" * 64)), True)
        one("readonly-write-denial", audit="write")
        one("readonly-socket-denial", audit="socket")
    finally:
        shutil.rmtree(workspace)
    original_unchanged = before == inventory(root)
    receipt = {"cases": results, "cases_expected": len(results),
               "all_expected": all(r["expected_outcome"] and r["copied_input_unchanged"] for r in results),
               "whole_actual_owned_root_unchanged_before_receipt": original_unchanged,
               "fingerprint_fields": "exact paths, file bytes, modes, link counts; directories include modes; times excluded",
               "detached_final_sha256": a.finalhash, "mathematical_gate": False,
               "scope": "Copied artifact controls only; other agents' whole roots were not fingerprinted."}
    (root / "artifact-controls.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: v for k, v in receipt.items() if k != "cases"}, sort_keys=True))
    return 0 if receipt["all_expected"] and original_unchanged else 1


if __name__ == "__main__":
    raise SystemExit(main())
