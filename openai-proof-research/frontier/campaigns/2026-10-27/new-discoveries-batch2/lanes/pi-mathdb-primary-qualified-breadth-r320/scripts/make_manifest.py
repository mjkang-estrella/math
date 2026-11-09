#!/usr/bin/env python3
"""Build manifest.json: actual SHA-256 of every delivered payload.
Excludes manifest.json and verification-receipt.json by exact filename.
Records real clock time and upstream retrieval provenance."""
import hashlib, json, os, datetime

LANE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXCLUDE = {"manifest.json", "verification-receipt.json"}
SKIP_DIRS = {"frozen", "__pycache__"}  # frozen inputs are bound separately in bindings.json (28 entries)

def sha256(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 20), b""):
            h.update(b)
    return h.hexdigest()

payloads = []
for root, dirs, files in os.walk(LANE):
    dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
    for fn in sorted(files):
        if fn in EXCLUDE:
            continue
        p = os.path.join(root, fn)
        rel = os.path.relpath(p, LANE)
        payloads.append({"path": rel, "bytes": os.path.getsize(p), "sha256": sha256(p)})
payloads.sort(key=lambda x: x["path"])

manifest = {
    "schema_version": 1,
    "lane": "pi-mathdb-primary-qualified-breadth-r320",
    "generated_at": datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds"),
    "hash_algorithm": "sha256",
    "excluded_by_name": sorted(EXCLUDE),
    "upstream_retrieval_provenance": [
        {"url": "https://arxiv.org/html/2008.01164v2", "file": "sources/2008.01164v2.html", "kind": "arXiv HTML (experimental), v2 2021-06-11", "retrieved_at_utc": "2026-10-30T23:46:16Z"},
        {"url": "https://arxiv.org/abs/2008.01164", "file": "sources/2008.01164-abs.html", "kind": "arXiv abstract page", "retrieved_at_utc": "2026-10-30T23:46:16Z"},
        {"url": "https://arxiv.org/html/1403.3868v2", "file": "sources/1403.3868v2.html", "kind": "arXiv HTML (experimental), v2 2014-10-02", "retrieved_at_utc": "2026-10-30T23:46:16Z"},
        {"url": "https://arxiv.org/abs/1403.3868", "file": "sources/1403.3868-abs.html", "kind": "arXiv abstract page", "retrieved_at_utc": "2026-10-30T23:46:16Z"},
        {"url": "https://arxiv.org/html/1712.10010v2", "file": "sources/1712.10010v2.html", "kind": "arXiv HTML (experimental), v2 2018-05-17", "retrieved_at_utc": "2026-10-30T23:46:16Z"},
        {"url": "https://arxiv.org/abs/1712.10010", "file": "sources/1712.10010-abs.html", "kind": "arXiv abstract page", "retrieved_at_utc": "2026-10-30T23:46:16Z"},
        {"url": "https://arxiv.org/abs/2004.01327", "file": "sources/2004.01327-abs.html", "kind": "arXiv abstract page (refutation of 346000)", "retrieved_at_utc": "2026-10-30T23:46:16Z"},
        {"url": "https://arxiv.org/abs/1703.05253", "file": "sources/1703.05253-abs.html", "kind": "arXiv abstract page (resolution of 400943; JCTA 173 (2020) 105236)", "retrieved_at_utc": "2026-10-30T23:46:16Z"}
    ],
    "immutable_input_bindings": "bindings.json (28 entries; corpus chunks verified against pi-mathdb-full-corpus-inventory-r301/manifest.json)",
    "payloads": payloads
}
with open(os.path.join(LANE, "manifest.json"), "w") as f:
    json.dump(manifest, f, indent=1)
print(f"manifest written: {len(payloads)} payloads")
