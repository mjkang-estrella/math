#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT License.
"""Optional rejection tests for verify.py, run on disposable copies only.

The original package is verified first and is never modified. Each mutation
is applied to a fresh copy in a temporary directory outside the package,
which is deleted on exit. The original verify.py is run against each copy
with --root, so a mutated copy cannot weaken the verifier being tested.
"""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
VERIFY = os.path.join(HERE, "verify.py")
CONTROL_FILES = ("seal.json", "input-manifest.json", "output-manifest.json")


def sha256_file(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def run_verify(root, seal_sha256):
    proc = subprocess.run([sys.executable, "-B", VERIFY, "--seal-sha256",
                           seal_sha256, "--root", root],
                          capture_output=True, text=True, timeout=1200)
    return proc.returncode, proc.stdout + proc.stderr


def reseal(root, **seal_overrides):
    """Rebuild both inventories and the seal of a copy; return the seal SHA256."""
    inputs, outputs = [], []
    for dirpath, _dirs, files in os.walk(root):
        for name in files:
            rel = os.path.relpath(os.path.join(dirpath, name), root).replace(os.sep, "/")
            if rel in CONTROL_FILES:
                continue
            with open(os.path.join(root, rel), "rb") as fh:
                data = fh.read()
            entry = {"path": rel, "sha256": hashlib.sha256(data).hexdigest(),
                     "size": len(data)}
            (inputs if rel.startswith("inputs/") else outputs).append(entry)
    inventories = {}
    for name, schema, files in (
            ("input-manifest.json", "two-order-signing-r2-input-v1", inputs),
            ("output-manifest.json", "two-order-signing-r2-output-v1", outputs)):
        files.sort(key=lambda e: e["path"])
        data = (json.dumps({"files": files, "schema": schema}, indent=2,
                           sort_keys=True) + "\n").encode("utf-8")
        with open(os.path.join(root, name), "wb") as fh:
            fh.write(data)
        inventories[name] = {"sha256": hashlib.sha256(data).hexdigest(),
                             "size": len(data)}
    seal = {"acceptance_claim": False, "inventories": inventories,
            "r4_seal_sha256": "e1cda9940e5020d9e47fe6e8a8e2124e7a643b8bc3e8560beee55c55f9c0ab2d",
            "schema": "two-order-signing-r2-seal-v1",
            "target_status": "UNRESOLVED"}
    seal.update(seal_overrides)
    data = (json.dumps(seal, indent=2, sort_keys=True) + "\n").encode("utf-8")
    with open(os.path.join(root, "seal.json"), "wb") as fh:
        fh.write(data)
    return hashlib.sha256(data).hexdigest()


def append(path, data):
    with open(path, "ab") as fh:
        fh.write(data)


def flip_byte(path, offset=100):
    with open(path, "r+b") as fh:
        fh.seek(offset)
        b = fh.read(1)
        fh.seek(offset)
        fh.write(bytes([b[0] ^ 0x01]))


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--seal-sha256", required=True)
    args = parser.parse_args()
    handoff = args.seal_sha256.strip().lower()

    code, out = run_verify(HERE, handoff)
    if code != 0:
        print(out)
        print("MUTATION_TESTS: ABORT original package does not verify")
        return 1
    print("ORIGINAL: verified")

    scratch = tempfile.mkdtemp(prefix="two-order-r2-mutation-")
    failures = []
    try:
        counter = [0]

        def fresh_copy():
            counter[0] += 1
            dest = os.path.join(scratch, f"copy{counter[0]}")
            shutil.copytree(HERE, dest, symlinks=True)
            return dest

        sentinel = os.path.join(scratch, "SENTINEL_CHECKER_WAS_EXECUTED")

        def m_receipt(c):
            append(os.path.join(c, "checks-receipt.txt"), b"tampered\n")
            return handoff, "FAIL[file]"

        def m_input(c):
            flip_byte(os.path.join(c, "inputs/private/literature/brs-2202.02217.txt"))
            return handoff, "FAIL[file]"

        def m_missing(c):
            os.remove(os.path.join(c, "literature-screen.md"))
            return handoff, "FAIL[membership]"

        def m_extra(c):
            with open(os.path.join(c, "exploration", "stray.txt"), "wb") as fh:
                fh.write(b"extra\n")
            return handoff, "FAIL[membership]"

        def m_symlink(c):
            os.symlink("candidate.md", os.path.join(c, "candidate-link.md"))
            return handoff, "FAIL[membership]"

        def m_wrong_handoff(c):
            return "0" * 64, "FAIL[seal]"

        def m_sentinel_checker(c):
            with open(os.path.join(c, "checks.py"), "w", encoding="utf-8") as fh:
                fh.write(f"open({sentinel!r}, 'w').write('x')\n"
                         f"print(open('checks-receipt.txt').read(), end='')\n")
            return handoff, "FAIL[file]"

        def m_resealed_receipt(c):
            path = os.path.join(c, "checks-receipt.txt")
            with open(path, "rb") as fh:
                data = fh.read()
            with open(path, "wb") as fh:
                fh.write(data.replace(b"ALL_PASS", b"ALL_PASS_EDITED", 1))
            return reseal(c), "FAIL[replay]"

        def m_resealed_r4(c):
            append(os.path.join(c, "inputs/private/context/r4/candidate.md"), b"\n")
            return reseal(c), "FAIL[r4]"

        def m_resealed_status(c):
            return reseal(c, target_status="PROVED"), "FAIL[seal]"

        def m_resealed_extra_unlisted(c):
            new_hash = reseal(c)
            with open(os.path.join(c, "late.txt"), "wb") as fh:
                fh.write(b"added after sealing\n")
            return new_hash, "FAIL[membership]"

        def control_resealed_clean(c):
            return reseal(c), None

        cases = [
            ("receipt_tamper", m_receipt),
            ("input_tamper", m_input),
            ("missing_file", m_missing),
            ("extra_file", m_extra),
            ("symlink", m_symlink),
            ("wrong_handoff_hash", m_wrong_handoff),
            ("sentinel_checker_not_executed", m_sentinel_checker),
            ("resealed_wrong_receipt_rejected_at_replay", m_resealed_receipt),
            ("resealed_broken_r4_chain", m_resealed_r4),
            ("resealed_status_claim", m_resealed_status),
            ("file_added_after_reseal", m_resealed_extra_unlisted),
            ("control_clean_reseal_accepted", control_resealed_clean),
        ]
        for name, mutate in cases:
            copy = fresh_copy()
            seal_hash, expected = mutate(copy)
            code, out = run_verify(copy, seal_hash)
            if expected is None:
                ok = code == 0 and "VERIFY: PASS" in out
                verdict = "ACCEPTED" if code == 0 else "REJECTED"
            else:
                ok = code != 0 and f"VERIFY: {expected}" in out
                verdict = "REJECTED" if code != 0 else "ACCEPTED"
                if name == "sentinel_checker_not_executed" and os.path.exists(sentinel):
                    ok = False
                    verdict += " but sentinel was written"
            line = out.strip().splitlines()[-1] if out.strip() else ""
            print(f"MUTATION {name}: {verdict} {'as expected' if ok else 'UNEXPECTED'} | {line}")
            if not ok:
                failures.append(name)
            shutil.rmtree(copy)
    finally:
        shutil.rmtree(scratch, ignore_errors=True)

    code, _ = run_verify(HERE, handoff)
    if code != 0:
        failures.append("original_after_tests")
    print("ORIGINAL_AFTER_TESTS:", "verified" if code == 0 else "FAILED")
    print("MUTATION_TESTS:", "ALL_AS_EXPECTED" if not failures else "FAILURES " + ",".join(failures))
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
