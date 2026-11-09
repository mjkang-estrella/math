"""Write MANIFEST.sha256, paper-source.zip, full-dossier.zip, archives.sha256 and a package receipt.

Usage (from the lane directory): python3 -I scripts/package.py
Excluded from the manifest: itself, the two ZIPs, archives.sha256, receipts/package-receipt.json.
"""
import sys
sys.dont_write_bytecode = True
import hashlib, json, os, zipfile, datetime

EXCL = {"MANIFEST.sha256", "paper-source.zip", "full-dossier.zip", "archives.sha256", "receipts/package-receipt.json"}
FIXED = (2026, 11, 5, 0, 0, 0)


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


files = []
for dp, dns, fns in os.walk(".", followlinks=False):
    dns.sort()
    for fn in sorted(fns):
        p = os.path.relpath(os.path.join(dp, fn), ".")
        assert not os.path.islink(p), p
        assert "__pycache__" not in p, p
        if p not in EXCL:
            files.append(p)
files.sort()
with open("MANIFEST.sha256", "x") as f:
    for p in files:
        f.write("%s  %s\n" % (sha(p), p))


def mkzip(name, members):
    with zipfile.ZipFile(name, "x", zipfile.ZIP_DEFLATED) as z:
        for p in members:
            zi = zipfile.ZipInfo(p, FIXED)
            zi.compress_type = zipfile.ZIP_DEFLATED
            zi.external_attr = 0o644 << 16
            z.writestr(zi, open(p, "rb").read())
    with zipfile.ZipFile(name) as z:
        assert z.testzip() is None
        assert sorted(z.namelist()) == sorted(members)
        for p in members:
            assert hashlib.sha256(z.read(p)).hexdigest() == sha(p)


src_members = ["paper/manuscript.src", "paper/manuscript-resolved.txt", "REPRODUCE.md", "PROOF.md",
               "outputs/graph-facts.json"] + \
    sorted("outputs/search/" + f for f in os.listdir("outputs/search")) + \
    sorted("scripts/" + f for f in os.listdir("scripts") if f.endswith(".py"))
mkzip("paper-source.zip", src_members)
mkzip("full-dossier.zip", files + ["MANIFEST.sha256"])
with open("archives.sha256", "x") as f:
    for z in ("paper-source.zip", "full-dossier.zip"):
        f.write("%s  %s\n" % (sha(z), z))
rec = {"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "manifest_files": len(files),
       "manifest_sha256": sha("MANIFEST.sha256"),
       "paper_source_zip": {"members": len(src_members), "sha256": sha("paper-source.zip")},
       "full_dossier_zip": {"members": len(files) + 1, "sha256": sha("full-dossier.zip")},
       "reopened_and_crc_tested": True}
with open("receipts/package-receipt.json", "x") as f:
    json.dump(rec, f, indent=1)
print(json.dumps(rec))
