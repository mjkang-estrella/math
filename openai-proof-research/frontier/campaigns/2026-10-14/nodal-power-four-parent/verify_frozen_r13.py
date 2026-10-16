#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Parent integrity replay only; no mathematical correctness claim."""
import hashlib, json, pathlib, subprocess, sys
PROJECT = pathlib.Path(__file__).resolve().parents[4]
CAND = PROJECT / "frontier/campaigns/2026-10-14/fresh-analytic-discovery-r13"
ANCHOR = "056fc8c98bbdcd01a701ed94db722bcba07a9ea983e4c4459be34f875abfa657"
REV = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def safe(rel):
    p = pathlib.PurePosixPath(rel)
    assert not p.is_absolute() and p.as_posix() == rel and ".." not in p.parts
    assert rel not in ("", ".")
    return CAND / rel
def entry(e):
    p = safe(e["path"])
    assert p.is_file() and not p.is_symlink()
    assert p.stat().st_size == e["size"] and digest(p) == e["sha256"], p
    return e["path"]
assert digest(CAND / "seal.json") == ANCHOR
seal = json.loads((CAND / "seal.json").read_text())
assert seal["revision"] == REV and seal["counted"] is False
expected = {"seal.json", "seal.sha256"}
assert (CAND / "seal.sha256").read_text().split() == [ANCHOR, "seal.json"]
for key in ("inputs", "outputs", "receipt"):
    rel = entry(seal[key])
    assert rel not in expected
    expected.add(rel)
    if key != "receipt":
        m = json.loads(safe(rel).read_text())
        assert m["format"] == "sha256-size-v1"
        for e in m["files"]:
            rel2 = entry(e)
            assert rel2 not in expected
            expected.add(rel2)
actual = set()
dirs = {pathlib.PurePosixPath(".")}
for p in CAND.rglob("*"):
    assert not p.is_symlink(), p
    assert p.is_file() or p.is_dir(), p
    if p.is_file():
        actual.add(p.relative_to(CAND).as_posix())
    else:
        dirs.add(pathlib.PurePosixPath(p.relative_to(CAND).as_posix()))
assert actual == expected, (actual - expected, expected - actual)
expected_dirs = {q for rel in expected for q in pathlib.PurePosixPath(rel).parents}
assert dirs == expected_dirs, (dirs - expected_dirs, expected_dirs - dirs)
tree = json.loads((PROJECT / "sources/preprints-tree.json").read_text())
assert tree["truncated"] is False
idx = {e["path"]: e for e in tree["tree"] if e["type"] == "blob"}
gi = json.loads((CAND / "git-identities.json").read_text())
assert gi["revision"] == REV and len(gi["files"]) == 31
assert len({e["local"] for e in gi["files"]}) == 31
assert {p for p in expected if p.startswith("inputs/pinned/")} == {e["local"] for e in gi["files"]}
for e in gi["files"]:
    data = safe(e["local"]).read_bytes()
    sha = hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()
    t = idx[e["upstream_path"]]
    assert sha == e["git_blob_sha1"] == t["sha"]
    assert len(data) == e["size"] == t["size"]
external = [PROJECT / p for p in [
    "sources/upstream.json", "sources/preprints-tree.json",
    "frontier/campaigns/2026-10-14/brenier-logconcave-parent/fresh-r13-brief.txt",
    "frontier/campaigns/2026-10-14/brenier-logconcave-parent/fresh-r13-launch.json",
    "frontier/NEW-TEN-2026-10-14.md"]]
protected = [safe(p) for p in sorted(expected)] + external
before = {str(p): digest(p) for p in protected}
guard = r'''
import hashlib, json, os, pathlib, sys
sys.dont_write_bytecode = True
p = pathlib.Path(sys.argv[1])
data = p.read_bytes()
assert hashlib.sha256(data).hexdigest() == sys.argv[2]
code = compile(data, str(p), "exec")
sys.argv = [str(p), "--anchor=" + sys.argv[3]]
def audit(event, args):
    if event == "open":
        mode, flags = args[1:3]
        if (isinstance(mode, str) and any(c in mode for c in "wax+")) or (isinstance(flags, int) and flags & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)):
            raise PermissionError("read-only replay")
    if event.startswith(("subprocess.", "socket.", "shutil.")) or event in {"os.system", "os.remove", "os.rename", "os.rmdir", "os.mkdir", "os.chmod", "os.chown", "os.link", "os.symlink", "os.truncate", "os.utime", "os.exec", "os.posix_spawn", "os.fork"}:
        raise PermissionError("read-only replay: " + event)
sys.addaudithook(audit)
exec(code, {"__name__": "__main__", "__file__": str(p)})
'''
runs = []
for name, anchor, expected_code in (("positive", ANCHOR, 0), ("wrong-anchor", "0"*64, 1)):
    result = subprocess.run([sys.executable, "-B", "-c", guard, str(CAND / "verify.py"),
                             digest(CAND / "verify.py"), anchor], capture_output=True, text=True)
    assert result.returncode == expected_code, (name, result.stderr)
    runs.append({"name": name, "exit_code": result.returncode, "stdout": result.stdout, "stderr": result.stderr})
assert before == {str(p): digest(p) for p in protected}
print(json.dumps({
    "anchor": ANCHOR, "independent_manifest_and_exact_directory_authentication": True,
    "owned_files": len(expected), "owned_directories_including_root": len(dirs),
    "pinned_blobs": 31, "fixed_external_files": 4, "mutable_ledger_observed_only": 1,
    "protected_files": len(protected), "all_unchanged_during_verification": True,
    "runs": runs,
    "limits": "Integrity only. Author verifier is not an authentication-first boundary: anchor optional and checked after manifests; pre-seal skips seal. Parent independently authenticates all files/directories before guarded replay. Mutable live ledger only observed before/after this replay. No mathematical executable run."
}, indent=2))
