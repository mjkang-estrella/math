#!/usr/bin/env python3
"""Exercise trusted verify.py against temporary copied packets. MIT."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def fingerprint(root):
    return {p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else "directory" for p in sorted(root.rglob("*"))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packet", required=True)
    parser.add_argument("--workdir", required=True)
    parser.add_argument("--expected-manifest-sha256", required=True)
    args = parser.parse_args()
    root, work = Path(args.packet).resolve(), Path(args.workdir).resolve()
    if work == root or root in work.parents:
        parser.error("temporary workdir must be outside the sealed packet")
    work.mkdir(parents=True, exist_ok=True)
    checker = Path(__file__).resolve().with_name("verify.py")
    before = fingerprint(root)
    results = []
    names = ["pristine", "missing_detached_hash", "wrong_detached_hash", "changed_public", "missing_private", "extra_file", "extra_directory", "symlink_file", "symlink_directory", "changed_manifest", "changed_copied_verifier"]
    for name in names:
        with tempfile.TemporaryDirectory(prefix="r76-control-", dir=work) as temporary:
            copied = Path(temporary) / "packet"
            shutil.copytree(root, copied)
            if name == "changed_public":
                with (copied / "public/research.md").open("ab") as stream:
                    stream.write(b"\nCONTROL MUTATION\n")
            elif name == "missing_private":
                next((copied / "private/primary").glob("*.pdf")).unlink()
            elif name == "extra_file":
                (copied / "extra.txt").write_text("control")
            elif name == "extra_directory":
                (copied / "empty-extra").mkdir()
            elif name == "symlink_file":
                target = copied / "public/research.md"
                target.unlink()
                target.symlink_to(root / "public/research.md")
            elif name == "symlink_directory":
                (copied / "linked").symlink_to(root / "public", target_is_directory=True)
            elif name == "changed_manifest":
                with (copied / "manifest.json").open("ab") as stream:
                    stream.write(b"\n")
            elif name == "changed_copied_verifier":
                with (copied / "public/verify.py").open("ab") as stream:
                    stream.write(b"\n# CONTROL MUTATION\n")
            command = [sys.executable, "-B", str(checker), "--packet", str(copied)]
            if name != "missing_detached_hash":
                expected = "0" * 64 if name == "wrong_detached_hash" else args.expected_manifest_sha256
                command += ["--expected-manifest-sha256", expected]
            ran = subprocess.run(command, capture_output=True, text=True)
            correct = (ran.returncode == 0) if name == "pristine" else (ran.returncode != 0)
            results.append({"case": name, "expected_accept": name == "pristine", "exit_code": ran.returncode, "control_passed": correct, "stdout": ran.stdout.strip(), "stderr": ran.stderr.strip()})
    unchanged = before == fingerprint(root)
    ok = unchanged and all(row["control_passed"] for row in results)
    print(json.dumps({"status": "CONTROLS_OK" if ok else "CONTROLS_FAILED", "trusted_verifier": str(checker), "manifest_sha256": args.expected_manifest_sha256, "original_packet_unchanged": unchanged, "copied_controls": results, "mathematical_gate": False}, indent=2))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
