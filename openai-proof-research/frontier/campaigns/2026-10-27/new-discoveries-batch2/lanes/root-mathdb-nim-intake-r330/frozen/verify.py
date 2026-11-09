"""Independent post-write verifier for lane pi-subtraction-nim-source-hypothesis-r325.

Rejects on: (a) any listed file whose sha256/size differs from manifest.json;
(b) any file present in the lane but NOT listed in the manifest (unlisted files),
except manifest.json itself and verification-receipt.json (written after);
(c) source-byte hash mismatches vs sources/provenance.json;
(d) failure of the re-run decisive source comparisons.

Usage: python3 -B verify.py            (exit 0 = accept, 1 = reject)
"""
import os, sys, json, hashlib

HERE = os.path.dirname(os.path.abspath(__file__))


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    errors = []
    manifest = json.load(open(os.path.join(HERE, "manifest.json")))
    listed = {}
    for e in manifest["files"]:
        listed[e["path"]] = e

    # walk lane
    actual = []
    for root, dirs, files in os.walk(HERE):
        for fn in files:
            rel = os.path.relpath(os.path.join(root, fn), HERE)
            if rel in ("manifest.json", "verification-receipt.json"):
                continue
            actual.append(rel)
    actual_set = set(actual)

    for rel in sorted(actual_set):
        if rel not in listed:
            errors.append(f"UNLISTED FILE: {rel}")
    for rel, e in sorted(listed.items()):
        p = os.path.join(HERE, rel)
        if not os.path.exists(p):
            errors.append(f"MISSING: {rel}")
            continue
        h = sha256(p)
        sz = os.path.getsize(p)
        if h != e["sha256"]:
            errors.append(f"HASH MISMATCH: {rel} manifest={e['sha256']} actual={h}")
        if sz != e["bytes"]:
            errors.append(f"SIZE MISMATCH: {rel} manifest={e['bytes']} actual={sz}")

    # source bytes vs provenance
    prov = json.load(open(os.path.join(HERE, "sources", "provenance.json")))
    for f in prov["fetches"]:
        p = os.path.join(HERE, f["file"])
        if sha256(p) != f["sha256"]:
            errors.append(f"SOURCE HASH MISMATCH: {f['file']}")
    cached = prov["cached_mathdb_record"]
    if sha256(cached["path"]) != cached["sha256"]:
        errors.append("CACHED MATHDB RECORD HASH MISMATCH")

    # re-run decisive source comparisons (independent recomputation)
    sys.path.insert(0, os.path.join(HERE, "scripts"))
    os.environ.setdefault("PYTHONDONTWRITEBYTECODE", "1")
    from scan3 import analyze  # noqa: E402

    r = analyze((1, 3, 5), 20000)
    if r["min_period"] != 2 or any(s % 2 for s in (4, 8, 6)):
        errors.append("DECISIVE CHECK FAILED: S=(1,3,5) literal conjecture should hold")
    r = analyze((2, 5, 6), 20000)
    if r["min_period"] != 11:
        errors.append("DECISIVE CHECK FAILED: S=(2,5,6) m != 11")

    # quote presence in extracted text (exact substrings)
    t = open(os.path.join(HERE, "sources", "paper-2606.11658.txt"), encoding="utf-8",
             errors="replace").read()
    if "The minimality is not required for them" not in t:
        errors.append("QUOTE MISSING: Moriwaki Definition 2 minimality sentence")
    if "periodic with a period a + b, b + c or c + a" not in t.replace("\n", " "):
        errors.append("QUOTE MISSING: Moriwaki Conjecture 1")
    w = open(os.path.join(HERE, "sources", "paper-1606.04029.txt"), encoding="utf-8",
             errors="replace").read()
    if "is a divisor of at least one of the numbers" not in w:
        errors.append("QUOTE MISSING: Ward Case II")
    m = json.load(open(os.path.join(HERE, "..", "..", "..", "..", "..",
                                     "2026-10-25", "twenty-proof-discrete-lane",
                                     "sources", "mathdb-375237.json"),
                       encoding="utf-8")) if False else None

    if errors:
        print("REJECT")
        for e in errors:
            print(" -", e)
        sys.exit(1)
    print(f"ACCEPT: {len(listed)} files verified, sources and decisive checks OK")
    sys.exit(0)


if __name__ == "__main__":
    main()
