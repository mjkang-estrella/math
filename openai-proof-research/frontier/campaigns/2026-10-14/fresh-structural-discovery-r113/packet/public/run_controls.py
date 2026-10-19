#!/usr/bin/env python3
"""Exercise the sealed verifier on temporary copies. Byte integrity only."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("packet", type=Path)
    ap.add_argument("--expected-manifest-sha256", required=True)
    ap.add_argument("--work-directory", type=Path, required=True)
    args = ap.parse_args()
    source = args.packet.resolve(strict=True)
    work = args.work_directory.resolve(strict=True)
    if work == source or source in work.parents:
        raise RuntimeError("control workspace must be outside the packet")
    initial = {p.relative_to(source).as_posix(): sha(p.read_bytes()) for p in source.rglob("*") if p.is_file()}
    rows = []
    with tempfile.TemporaryDirectory(prefix="r113-controls-", dir=work) as temp:
        temp = Path(temp)
        copied = temp / "packet"
        shutil.copytree(source, copied)
        verifier = copied / "public/verify.py"

        def invoke(name, expected_success=False, anchor=args.expected_manifest_sha256, root=copied):
            command = [sys.executable, "-B", str(verifier), str(root)]
            if anchor is not None:
                command += ["--expected-manifest-sha256", anchor]
            done = subprocess.run(command, capture_output=True, text=True)
            ok = (done.returncode == 0) == expected_success
            rows.append({"case": name, "expected_success": expected_success, "returncode": done.returncode, "control_satisfied": ok, "stdout": done.stdout.strip(), "stderr": done.stderr.strip()})
            if not ok:
                raise RuntimeError("unexpected verifier result: " + name)

        invoke("clean_copy", True)
        invoke("wrong_detached_anchor", anchor="0" * 64)
        invoke("missing_detached_anchor", anchor=None)
        invoke("malformed_detached_anchor", anchor="x")
        target = copied / "public/report.md"
        original = target.read_bytes()
        target.write_bytes(original + b"\nchanged\n")
        invoke("changed_payload")
        target.write_bytes(original)
        target.unlink()
        invoke("missing_payload")
        target.write_bytes(original)
        extra = copied / "extra"
        extra.write_text("extra\n")
        invoke("extra_file")
        extra.unlink()
        extra.mkdir()
        invoke("extra_empty_directory")
        extra.rmdir()
        target.unlink()
        target.symlink_to(copied / "public/screen-238.md")
        invoke("symlink_payload")
        target.unlink()
        target.write_bytes(original)
        os.link(target, extra)
        invoke("hardlink_payload")
        extra.unlink()
        os.mkfifo(extra)
        invoke("special_file")
        extra.unlink()
        manifest = copied / "manifest.json"
        mbytes = manifest.read_bytes()
        manifest.write_bytes(mbytes + b"\n")
        invoke("changed_manifest")
        manifest.write_bytes(mbytes)
        duplicate = b'{"schema":"x",' + mbytes.lstrip()[1:]
        manifest.write_bytes(duplicate)
        invoke("duplicate_json_key_with_new_anchor", anchor=sha(duplicate))
        manifest.write_bytes(mbytes)
        symlink_root = temp / "root-link"
        symlink_root.symlink_to(copied, target_is_directory=True)
        invoke("symlink_root", root=symlink_root)
        invoke("restored_copy", True)
    final = {p.relative_to(source).as_posix(): sha(p.read_bytes()) for p in source.rglob("*") if p.is_file()}
    if final != initial:
        raise RuntimeError("source packet changed during copied controls")
    print(json.dumps({"status": "copied_integrity_controls_only", "manifest_sha256": args.expected_manifest_sha256, "source_packet_bytes_unchanged": True, "temporary_copies_removed": True, "cases": rows}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
