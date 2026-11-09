#!/usr/bin/env python3
"""Copied-mutation integrity controls for the sealed packet.

Copies the public packet (without private/) into a temporary directory inside
integrity/, runs tools/verify.py on the unmodified copy (must pass) and on
mutated copies (must fail), deletes the copies, checks the original packet is
unchanged, and writes integrity/controls.json.  Integrity only.
Usage: controls.py ROOT DETACHED_FINAL_SHA256
"""
import hashlib, json, os, shutil, subprocess, sys, tempfile

root = os.path.abspath(sys.argv[1]); fh = sys.argv[2]
tree = os.path.normpath(os.path.join(root, "../../../../sources/preprints-tree.json"))
def sha(p): return hashlib.sha256(open(p, "rb").read()).hexdigest()
def snapshot():
    man = json.load(open(os.path.join(root, "MANIFEST.json")))
    return {e["path"]: sha(os.path.join(root, e["path"])) for e in man["public"]} | \
           {"FINAL.json": sha(os.path.join(root, "FINAL.json")), "MANIFEST.json": sha(os.path.join(root, "MANIFEST.json"))}
before = snapshot()
os.makedirs(os.path.join(root, "integrity"), exist_ok=True)

def fresh_copy():
    d = tempfile.mkdtemp(prefix="copy-", dir=os.path.join(root, "integrity"))
    for name in os.listdir(root):
        if name in ("private", "integrity"): continue
        s = os.path.join(root, name)
        if os.path.isdir(s): shutil.copytree(s, os.path.join(d, name), ignore=shutil.ignore_patterns("__pycache__"))
        else: shutil.copy2(s, os.path.join(d, name))
    return d

def run(d, finalhash):
    r = subprocess.run([sys.executable, "-I", "-B", os.path.join(d, "tools", "verify.py"), "--root", d,
                        "--finalhash", finalhash, "--tree", tree], capture_output=True, text=True)
    return r.returncode == 0

def flip(path):
    b = bytearray(open(path, "rb").read()); b[len(b) // 2] ^= 1; open(path, "wb").write(bytes(b))

cases = []
def case(name, mutate, expect_pass, finalhash=fh):
    d = fresh_copy()
    try:
        mutate(d)
        got = run(d, finalhash)
        cases.append({"case": name, "expected_pass": expect_pass, "verifier_passed": got, "ok": got == expect_pass})
    finally:
        shutil.rmtree(d)

case("unmodified copy", lambda d: None, True)
case("byte flip in proof.md", lambda d: flip(os.path.join(d, "proof.md")), False)
case("byte flip in scope-freeze.md", lambda d: flip(os.path.join(d, "scope-freeze.md")), False)
case("wrong detached FINAL hash", lambda d: None, False, finalhash="0" * 64)
case("extra unlisted public file", lambda d: open(os.path.join(d, "extra.md"), "w").write("x"), False)
def bad_receipt(d):
    p = os.path.join(d, "source-receipts.json"); r = json.load(open(p))
    for e in r:
        if e.get("status") == "ok": e["tree_blob"] = "0" * 40; break
    json.dump(r, open(p, "w"), indent=1)
case("corrupted tree-blob anchor in source-receipts.json", bad_receipt, False)

after = snapshot()
res = {"all_ok": all(c["ok"] for c in cases) and before == after,
       "original_packet_unchanged": before == after, "cases": cases,
       "note": "Integrity controls only; they certify bytes, not mathematics."}
json.dump(res, open(os.path.join(root, "integrity", "controls.json"), "w"), indent=1)
print(json.dumps(res, indent=1))
sys.exit(0 if res["all_ok"] else 1)
