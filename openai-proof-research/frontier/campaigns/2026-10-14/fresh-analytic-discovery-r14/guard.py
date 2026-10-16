#!/usr/bin/env python3
"""Externally hash-check then run the inspected verifier under a read-only guard.

Copyright 2026 Myeongjin Kang. MIT. This guard is original package code,
not a historical or mathematical executable. Call with -B.
"""
import argparse
import hashlib
from pathlib import Path
import sys


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--verifier-sha256", required=True)
    p.add_argument("--anchor", required=True)
    p.add_argument("--controls", action="store_true")
    args = p.parse_args()
    path = Path(__file__).absolute().parent / "verify.py"
    code = path.read_bytes()
    if hashlib.sha256(code).hexdigest() != args.verifier_sha256:
        raise ValueError("external verifier-code hash mismatch")

    def audit(event, values):
        if event == "open":
            mode = values[1]
            flags = values[2]
            if isinstance(mode, str) and any(c in mode for c in "wax+"):
                raise PermissionError("write open denied")
            if isinstance(flags, int) and flags & (1 | 2 | 64 | 512 | 1024):
                raise PermissionError("write flags denied")
        if event.startswith(("subprocess.", "socket.", "ctypes.")) or event in {
            "os.system", "os.remove", "os.rename", "os.mkdir", "os.rmdir",
            "os.unlink", "os.chmod", "os.chown", "os.utime", "os.link",
            "os.symlink", "os.truncate", "os.exec", "os.posix_spawn", "os.fork",
        }:
            raise PermissionError("mutation/process/network denied: " + event)

    sys.dont_write_bytecode = True
    sys.addaudithook(audit)
    sys.argv = [str(path), "--anchor", args.anchor]
    if args.controls:
        sys.argv.append("--controls")
    exec(compile(code, str(path), "exec"), {"__name__": "__main__", "__file__": str(path)})


if __name__ == "__main__":
    main()
