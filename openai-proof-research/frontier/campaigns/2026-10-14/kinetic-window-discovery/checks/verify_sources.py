#!/usr/bin/env python3
"""Re-fetch the pinned H source files and compare SHA-256, size and git blob id.

Usage:  python3 -I verify_sources.py [path/to/sources/preprints-tree.json]
Needs network access to raw.githubusercontent.com.  Nothing is written to disk.
The expected values are those recorded in ../input-authentication.json.
"""
import hashlib
import json
import sys
import urllib.request

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
BASE = ("https://raw.githubusercontent.com/openai/math/" + PIN +
        "/preprints/Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan-"
        "September-23-2026/build/")
EXPECT = {
    "sections/01-introduction.tex": "f64b52941054e73c5a9e80ed7698c6a2d0a5d7f6894decd8c9dbb8fcd9d4c2a8",
    "sections/02-initial-target.tex": "51fad6beefe3041c56ea2686776dbfdedf8522120762f4aaef019947fe902396",
    "sections/03-dhm-inputs.tex": "a2506a516767704d4d3630e65395ed7b9481fbcbddff912ad38ba2441e5c1cbf",
    "sections/04-cluster-expansion.tex": "5f824af314132999e830425354a43a273d2e17e14bf46d02a4d254917c8f8d47",
    "sections/05-cutoff.tex": "e5380f7a81c4f32ce23ebf3ad62aee4f23c4530d342da2198cd2b9602ecfac4e",
    "sections/06-sharp-asymptotics.tex": "32a5a00ce410873a30fbed113b0b1ec56a80da5b6bc28664ae19a73637282883",
    "sections/07-gaussian-limit.tex": "9cf6ab1d1c78ab4203a403bfc09331779c2b9b029280f1751009b0ac4faf99e4",
    "sections/08-transfer.tex": "3efa338da518fd1141222a800e9ef45b3a3b998145d3aa39e725abe35b240136",
    "figures/chronological-mergers.tex": "f53514c94daef063a7c8ffdd4bc525c28364aef09988d7bc714f127cbb87bf17",
    "references.bib": "6c423a9ebddaa027e88a9e34ebdcb49188642d22219b9b5d8049d9de663d4a6c",
    "main.tex": "4f84d56fd4dcb78bb2f776063969c097279feaa19a74e95a63be2613d90e53af",
}


def blob_sha1(data):
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def main():
    inventory = {}
    if len(sys.argv) > 1:
        tree = json.load(open(sys.argv[1]))
        items = tree["tree"] if isinstance(tree, dict) else tree
        for it in items:
            p = it.get("path", "")
            if "Hard-sphere-fluctuations-on-the-regular-Boltzmann-lifespan" in p and "/build/" in p:
                inventory[p.split("/build/", 1)[1]] = (it.get("sha"), it.get("size"))
    ok = True
    for rel, want in EXPECT.items():
        data = urllib.request.urlopen(BASE + rel, timeout=60).read()
        sha = hashlib.sha256(data).hexdigest()
        blob = blob_sha1(data)
        inv = inventory.get(rel)
        inv_ok = inv is None or (inv[0] == blob and inv[1] == len(data))
        good = sha == want and inv_ok
        ok &= good
        print(f"{'ok ' if good else 'BAD'} {rel:40s} {len(data):6d} sha256={sha[:16]}.. blob={blob}"
              + ("" if inv is None else f" inventory={'match' if inv_ok else 'MISMATCH'}"))
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
