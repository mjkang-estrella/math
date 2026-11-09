"""Safe-extraction test of the Lean packet (no Lean is run, no packet code is executed).

Usage (from the lane directory):
  python3 -I scripts/safe_extract.py lean/source.zip lean/safe-extracted receipts/safe-extract-receipt.json
Checks: expected SHA-256, member names (no absolute paths, no '..', no backslashes), no symlinks
or special files, no duplicates, size caps, CRC test; extracts regular files only into a fresh
directory; compares module-order.txt and the module sources with the formal lane's final
extraction (read-only); scans the sources for forbidden tokens (informational, the audit's own
strings are expected); locates the endpoint declarations.
"""
import sys
sys.dont_write_bytecode = True
import hashlib, json, os, re, stat, zipfile, datetime

EXPECTED = "953331d0a5ed9984657fdfb8f35822e8383c19c7adf10a31c6390e0e961439ee"
MODULES = ["General", "GData", "Four", "Three", "Finite", "Endpoint", "Control", "Audit"]
LANE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FINAL = os.path.join(os.path.dirname(LANE), "irpath-formal-r1", "final-extraction")
MAX_TOTAL, MAX_MEMBERS = 5 * 2 ** 20, 200


def sha_bytes(b):
    return hashlib.sha256(b).hexdigest()


def main():
    zpath, outdir, receipt = sys.argv[1], sys.argv[2], sys.argv[3]
    raw = open(zpath, "rb").read()
    zsha = sha_bytes(raw)
    assert zsha == EXPECTED, zsha
    os.makedirs(outdir, exist_ok=False)
    rec = {"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "zip": zpath,
           "zip_sha256": zsha, "expected_sha256": EXPECTED, "members": []}
    with zipfile.ZipFile(zpath) as z:
        infos = z.infolist()
        assert len(infos) <= MAX_MEMBERS
        names = [i.filename for i in infos]
        assert len(names) == len(set(names)), "duplicate members"
        assert sum(i.file_size for i in infos) <= MAX_TOTAL
        assert z.testzip() is None, "CRC failure"
        for i in infos:
            n = i.filename
            assert not n.startswith("/") and "\\" not in n and ":" not in n, n
            parts = n.split("/")
            assert ".." not in parts and "." not in parts, n
            mode = (i.external_attr >> 16) & 0xFFFF
            if mode:
                assert not stat.S_ISLNK(mode), ("symlink", n)
                assert stat.S_ISREG(mode) or stat.S_ISDIR(mode), ("special file", n)
            if n.endswith("/"):
                continue
            data = z.read(i)
            dest = os.path.normpath(os.path.join(outdir, n))
            assert dest.startswith(os.path.abspath(outdir) + os.sep) or \
                dest.startswith(os.path.normpath(outdir) + os.sep), dest
            os.makedirs(os.path.dirname(dest), exist_ok=True)
            fd = os.open(dest, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
            with os.fdopen(fd, "wb") as f:
                f.write(data)
            rec["members"].append({"name": n, "bytes": len(data), "sha256": sha_bytes(data)})
    order = open(os.path.join(outdir, "module-order.txt")).read().split()
    assert order == MODULES, order
    rec["module_order"] = order
    cmp = {}
    for m in MODULES:
        p = os.path.join(outdir, m + ".lean")
        mine = sha_bytes(open(p, "rb").read())
        theirs = sha_bytes(open(os.path.join(FINAL, m + ".lean"), "rb").read())
        cmp[m] = {"sha256": mine, "equals_formal_final_extraction": mine == theirs}
        assert mine == theirs, m
    rec["modules"] = cmp
    tokens = ["sorry", "admit", "native_decide", "implemented_by", "extern", "unsafe", "axiom ", "partial def"]
    scan = {}
    for m in MODULES:
        txt = open(os.path.join(outdir, m + ".lean")).read()
        hits = {t: txt.count(t) for t in tokens if t in txt}
        if hits:
            scan[m] = hits
    rec["token_scan"] = scan
    allsrc = {m: open(os.path.join(outdir, m + ".lean")).read() for m in MODULES}
    decls = {}
    for name, pat in [("conjecture_false", r"theorem conjecture_false : ¬ Conjecture"),
                      ("Conjecture", r"def Conjecture : Prop"),
                      ("nonvacuity", r"theorem nonvacuity : IsIRGraph \(SimpleGraph\.pathGraph 2\)"),
                      ("pathIso", r"def pathIso : SimpleGraph\.pathGraph 9 ≃g IRGraph G9"),
                      ("IsIRGraph", r"def IsIRGraph"), ("IRGraph", r"def IRGraph"), ("Swap", r"def Swap"),
                      ("IRSet", r"def IRSet"), ("IR", r"def IR \(G"), ("Irredundant", r"def Irredundant"),
                      ("IsPrivateNbr", r"def IsPrivateNbr"), ("swap_symm", r"lemma swap_symm"),
                      ("swap_irrefl", r"lemma swap_irrefl"), ("ir_attained", r"lemma ir_attained"),
                      ("ir_upper", r"lemma ir_upper"), ("ir_G9", r"theorem ir_G9 : IR G9 = 3")]:
        where = [m for m, t in allsrc.items() if re.search(pat, t)]
        decls[name] = where
        assert len(where) == 1, (name, where)
    rec["declarations_found_in"] = decls
    rec["lean_run"] = False
    rec["verdict"] = "SAFE_EXTRACTION_PASS"
    with open(receipt, "x") as f:
        json.dump(rec, f, indent=1, ensure_ascii=False)
    print(json.dumps({"verdict": rec["verdict"], "n_members": len(rec["members"]), "token_scan": scan,
                      "declarations_found_in": decls}, ensure_ascii=False))


if __name__ == "__main__":
    main()
