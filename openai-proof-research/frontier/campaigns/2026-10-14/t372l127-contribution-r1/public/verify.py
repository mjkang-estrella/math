#!/usr/bin/env python3
"""Read-only artifact-integrity verifier for the T372L127 contribution review r1.

Usage:
  python3 public/verify.py --root <review-root> --final-hash <sha256 of FINAL.json> \
                           --report-hash <sha256 of REPORT.md> [--author-root <path>]

Checks (artifact integrity only; never a mathematical or contribution gate):
  1. FINAL.json and REPORT.md match the DETACHED hashes supplied on the command line.
  2. MANIFEST.json matches the manifest hash recorded inside FINAL.json.
  3. Every manifest payload exists with the recorded SHA256 and byte count, and no
     unlisted file exists under the root except the fixed excluded set.
  4. FINAL.json records the expected verdict, pin and input anchors; if the author root
     is present (default ../fresh-analytic-discovery-r127), the frozen scope, proof.md,
     outside REPORT, FINAL and MANIFEST anchors recorded in FINAL.json are re-hashed
     against the actual files (read-only).
An audit hook denies file writes, sockets and subprocesses for the whole run.
Exit 0 on ACCEPT, 2 on REJECT.
"""
import argparse, hashlib, json, os, sys

EXCLUDED = {"FINAL.json", "REPORT.md", "MANIFEST.json", "controls/receipt.json"}
TEMP_PREFIX = "controls/tmp-"


def _audit(event, args):
    if event == "open":
        mode = args[1] if len(args) > 1 and isinstance(args[1], str) else "r"
        if any(c in mode for c in "wax+"):
            raise RuntimeError("verifier is read-only: write denied: %r" % (args[0],))
    if event.startswith("socket.") or event in ("subprocess.Popen", "os.system", "os.exec", "os.posix_spawn", "os.spawn"):
        raise RuntimeError("verifier denies %s" % event)


sys.addaudithook(_audit)


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def reject(msg):
    sys.stderr.write("REJECT: %s\n" % msg)
    sys.exit(2)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--final-hash", required=True)
    ap.add_argument("--report-hash", required=True)
    ap.add_argument("--author-root", default=None)
    a = ap.parse_args()
    root = os.path.abspath(a.root)
    final_p, report_p, man_p = (os.path.join(root, n) for n in ("FINAL.json", "REPORT.md", "MANIFEST.json"))
    for p in (final_p, report_p, man_p):
        if not os.path.isfile(p):
            reject("missing %s" % os.path.basename(p))
    if sha256(final_p) != a.final_hash.lower():
        reject("detached FINAL mismatch")
    if sha256(report_p) != a.report_hash.lower():
        reject("detached REPORT mismatch")
    with open(final_p, "r", encoding="utf-8") as f:
        final = json.load(f)
    if sha256(man_p) != final.get("manifest_sha256"):
        reject("MANIFEST hash does not match FINAL.json")
    with open(man_p, "r", encoding="utf-8") as f:
        man = json.load(f)
    payloads = man.get("payloads", {})
    if set(man.get("excluded", [])) != EXCLUDED:
        reject("manifest excluded set differs from the fixed set")
    # inventory
    found = set()
    for dp, dns, fns in os.walk(root):
        rel_dir = os.path.relpath(dp, root)
        dns[:] = [d for d in dns if not os.path.join(rel_dir, d).replace("\\", "/").lstrip("./").startswith(TEMP_PREFIX)]
        for fn in fns:
            rel = os.path.normpath(os.path.join(rel_dir, fn)).replace("\\", "/")
            if rel.startswith("./"):
                rel = rel[2:]
            found.add(rel)
    expected = set(payloads) | EXCLUDED
    extra = sorted(f for f in found if f not in expected)
    if extra:
        reject("unlisted files present: %s" % extra[:5])
    missing = sorted(p for p in payloads if p not in found)
    if missing:
        reject("missing payloads: %s" % missing[:5])
    for rel, rec in payloads.items():
        p = os.path.join(root, rel)
        if os.path.getsize(p) != rec["bytes"] or sha256(p) != rec["sha256"]:
            reject("payload changed: %s" % rel)
    # FINAL fields
    if final.get("verdict") != "TECHNICAL" or final.get("conditional_on_correctness") is not True:
        reject("FINAL verdict fields unexpected")
    if final.get("pin") != "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb":
        reject("pin mismatch")
    anchors = final.get("author_input_anchors", {})
    author_root = a.author_root or os.path.join(os.path.dirname(root), "fresh-analytic-discovery-r127")
    author_checked = 0
    if os.path.isdir(author_root):
        for rel, h in anchors.get("files", {}).items():
            p = os.path.join(author_root, rel)
            if not os.path.isfile(p) or sha256(p) != h:
                reject("author input anchor mismatch: %s" % rel)
            author_checked += 1
    out = {"artifact_integrity_only": True, "mathematical_gate": False, "contribution_gate": False,
           "payloads": len(payloads), "author_input_anchors_checked": author_checked,
           "verdict_recorded": final.get("verdict"), "result": "ACCEPT"}
    print(json.dumps(out, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
