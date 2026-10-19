#!/usr/bin/env python3
"""Mutation controls for the T372L127 contribution review r1 verifier.

Runs public/verify.py against DISPOSABLE COPIES of the review tree placed under
controls/tmp-* inside this directory. The original tree is never modified: its
full file inventory is hashed before and after, and the receipt records both.
Each control states the expected outcome (ACCEPT / REJECT) and the observed one.

Usage: python3 controls/run_controls.py --final-hash <sha> --report-hash <sha>
Writes controls/receipt.json (excluded from MANIFEST.json so it can be written
after sealing). Artifact integrity only; never a mathematical or contribution gate.
"""
import argparse, hashlib, json, os, shutil, subprocess, sys, tempfile, time

sys.dont_write_bytecode = True  # importing seal.py must not leave a __pycache__ in the sealed tree

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
VERIFY = os.path.join(ROOT, "public", "verify.py")
AUTHOR_ROOT = os.path.join(os.path.dirname(ROOT), "fresh-analytic-discovery-r127")
RECEIPT = os.path.join(HERE, "receipt.json")
TEMP_PREFIX = "tmp-"


def sha256_bytes(b):
    return hashlib.sha256(b).hexdigest()


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def tree_hash(root, skip_receipt=True):
    """Deterministic hash of every file (path + content) under root, excluding tmp copies."""
    items = []
    for dp, dns, fns in os.walk(root):
        rel_dir = os.path.relpath(dp, root)
        dns[:] = sorted(d for d in dns if not (rel_dir == "controls" and d.startswith(TEMP_PREFIX)))
        for fn in sorted(fns):
            rel = os.path.normpath(os.path.join(rel_dir, fn)).replace("\\", "/")
            if rel.startswith("./"):
                rel = rel[2:]
            if skip_receipt and rel == "controls/receipt.json":
                continue
            items.append((rel, sha256(os.path.join(dp, fn))))
    h = hashlib.sha256()
    for rel, d in items:
        h.update(("%s\0%s\n" % (rel, d)).encode())
    return h.hexdigest(), len(items)


def run_verify(copy_root, final_hash, report_hash, author_root=AUTHOR_ROOT):
    # Always use the ORIGINAL verifier so a mutated copy cannot bring its own verifier.
    p = subprocess.run([sys.executable, VERIFY, "--root", copy_root, "--final-hash", final_hash,
                        "--report-hash", report_hash, "--author-root", author_root],
                       capture_output=True, text=True)
    return "ACCEPT" if p.returncode == 0 else "REJECT", p.returncode, (p.stdout + p.stderr).strip()[-300:]


def make_copy():
    d = tempfile.mkdtemp(prefix=TEMP_PREFIX, dir=HERE)
    dst = os.path.join(d, "copy")

    def ignore(dp, names):
        if os.path.abspath(dp) == HERE:
            return [n for n in names if n.startswith(TEMP_PREFIX) or n == "receipt.json"]
        return []

    shutil.copytree(ROOT, dst, ignore=ignore)
    return d, dst


def reseal(copy_root):
    """Rebuild MANIFEST.json and FINAL.manifest_sha256 of a copy; return new FINAL hash."""
    sys.path.insert(0, os.path.join(ROOT, "controls"))
    from seal import build_manifest  # noqa
    man = build_manifest(copy_root)
    man_p = os.path.join(copy_root, "MANIFEST.json")
    with open(man_p, "w", encoding="utf-8") as f:
        json.dump(man, f, indent=1, sort_keys=True)
        f.write("\n")
    final_p = os.path.join(copy_root, "FINAL.json")
    with open(final_p, "r", encoding="utf-8") as f:
        final = json.load(f)
    final["manifest_sha256"] = sha256(man_p)
    with open(final_p, "w", encoding="utf-8") as f:
        json.dump(final, f, indent=1, sort_keys=True)
        f.write("\n")
    return sha256(final_p)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--final-hash", required=True)
    ap.add_argument("--report-hash", required=True)
    a = ap.parse_args()
    fh, rh = a.final_hash.lower(), a.report_hash.lower()
    before, n_before = tree_hash(ROOT)
    results = []
    temp_dirs = []

    def record(name, expected, observed, note=""):
        results.append({"control": name, "expected": expected, "observed": observed[0], "exit": observed[1],
                        "pass": expected == observed[0], "tail": observed[2], "note": note})

    try:
        # C0 baseline: untouched copy with the true detached hashes must ACCEPT
        d, c = make_copy(); temp_dirs.append(d)
        record("C0 untouched copy, true hashes", "ACCEPT", run_verify(c, fh, rh))

        # C1 wrong detached FINAL hash
        record("C1 untouched copy, wrong FINAL hash", "REJECT", run_verify(c, "0" * 64, rh))

        # C2 wrong detached REPORT hash
        record("C2 untouched copy, wrong REPORT hash", "REJECT", run_verify(c, fh, "0" * 64))

        # C3 single byte flipped in a payload (literature table)
        d, c = make_copy(); temp_dirs.append(d)
        p = os.path.join(c, "public", "literature-comparison.md")
        b = bytearray(open(p, "rb").read()); b[len(b) // 2] ^= 0x01
        open(p, "wb").write(bytes(b))
        record("C3 one byte flipped in public/literature-comparison.md", "REJECT", run_verify(c, fh, rh))

        # C4 REPORT.md edited by one byte (detached hash must catch it)
        d, c = make_copy(); temp_dirs.append(d)
        p = os.path.join(c, "REPORT.md")
        open(p, "ab").write(b" ")
        record("C4 one byte appended to REPORT.md", "REJECT", run_verify(c, fh, rh))

        # C5 unlisted extra file under public/
        d, c = make_copy(); temp_dirs.append(d)
        open(os.path.join(c, "public", "extra.txt"), "w").write("unlisted\n")
        record("C5 unlisted file public/extra.txt added", "REJECT", run_verify(c, fh, rh))

        # C6 payload deleted
        d, c = make_copy(); temp_dirs.append(d)
        os.remove(os.path.join(c, "public", "search-receipts.json"))
        record("C6 payload public/search-receipts.json deleted", "REJECT", run_verify(c, fh, rh))

        # C7 verdict changed in FINAL.json, manifest resealed consistently, but detached FINAL hash is the true one
        d, c = make_copy(); temp_dirs.append(d)
        fp = os.path.join(c, "FINAL.json")
        final = json.load(open(fp)); final["verdict"] = "SUBSTANTIAL"
        json.dump(final, open(fp, "w"), indent=1, sort_keys=True); open(fp, "a").write("\n")
        record("C7 FINAL verdict changed, true detached hash", "REJECT", run_verify(c, fh, rh))
        # C7b same copy, attacker supplies the hash of the altered FINAL: verifier still rejects on verdict field
        record("C7b FINAL verdict changed, re-anchored hash", "REJECT", run_verify(c, sha256(fp), rh))

        # C8 payload mutated AND manifest resealed, FINAL re-anchored (consistent copy): ACCEPT is expected,
        # showing that the detached hashes, not the manifest, are the outside anchor; C8b: with the TRUE
        # detached FINAL hash the same copy is REJECTED.
        d, c = make_copy(); temp_dirs.append(d)
        p = os.path.join(c, "public", "reading-limits.md")
        open(p, "ab").write(b"\n")
        new_fh = reseal(c)
        record("C8 payload changed + resealed + re-anchored FINAL", "ACCEPT", run_verify(c, new_fh, rh),
               "consistent copy accepted under ITS OWN detached hash; shows anchor must be published outside")
        record("C8b same copy under the TRUE detached FINAL hash", "REJECT", run_verify(c, fh, rh))

        # C9 author input anchor broken: point verifier at a fake author root with altered proof.md
        d, c = make_copy(); temp_dirs.append(d)
        fake_author = os.path.join(d, "fake-author")
        shutil.copytree(AUTHOR_ROOT, fake_author)
        open(os.path.join(fake_author, "packet", "public", "proof.md"), "ab").write(b"\n")
        obs = run_verify(c, fh, rh, author_root=fake_author)
        record("C9 author proof.md altered in a copied author root", "REJECT", obs)

        # C10 verifier is read-only: a copy of verify.py patched to attempt a write must raise
        d, c = make_copy(); temp_dirs.append(d)
        vp = os.path.join(d, "verify_write_probe.py")
        src = open(VERIFY).read().replace("def main():", "def main():\n    open(os.path.join(os.path.dirname(__file__), 'probe.txt'), 'w').write('x')\n", 1)
        open(vp, "w").write(src)
        pr = subprocess.run([sys.executable, vp, "--root", c, "--final-hash", fh, "--report-hash", rh, "--author-root", AUTHOR_ROOT],
                            capture_output=True, text=True)
        wrote = os.path.exists(os.path.join(d, "probe.txt"))
        results.append({"control": "C10 audit hook denies write inside verifier", "expected": "no file written, nonzero exit",
                        "observed": "written" if wrote else ("not written, exit %d" % pr.returncode), "exit": pr.returncode,
                        "pass": (not wrote) and pr.returncode != 0, "tail": (pr.stdout + pr.stderr).strip()[-200:], "note": ""})
    finally:
        for d in temp_dirs:
            shutil.rmtree(d, ignore_errors=True)
    after, n_after = tree_hash(ROOT)
    receipt = {
        "artifact_integrity_only": True, "mathematical_gate": False, "contribution_gate": False,
        "generated_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "verifier": "public/verify.py", "verifier_sha256": sha256(VERIFY),
        "detached_final_sha256_used": fh, "detached_report_sha256_used": rh,
        "original_tree_hash_before": before, "original_tree_hash_after": after,
        "original_files_hashed": n_before, "original_unchanged": before == after and n_before == n_after,
        "temp_copies_removed": all(not os.path.exists(d) for d in temp_dirs),
        "controls": results, "all_pass": all(r["pass"] for r in results) and before == after,
    }
    with open(RECEIPT, "w", encoding="utf-8") as f:
        json.dump(receipt, f, indent=1, sort_keys=True)
        f.write("\n")
    print(json.dumps({k: receipt[k] for k in ("all_pass", "original_unchanged", "temp_copies_removed")}))
    for r in results:
        print("%-5s %-60s expected=%s observed=%s" % ("PASS" if r["pass"] else "FAIL", r["control"][:60], r["expected"], r["observed"]))
    return 0 if receipt["all_pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
