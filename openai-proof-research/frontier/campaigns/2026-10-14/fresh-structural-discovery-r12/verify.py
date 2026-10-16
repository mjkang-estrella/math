"""Offline, read-only integrity and ONE finite-support replay.
Myeongjin Kang; no affiliation. Original code MIT.
The externally supplied seal anchor must be trusted separately.
"""
from pathlib import Path, PurePosixPath
import hashlib
import json
import subprocess
import sys

BASE = Path(__file__).resolve().parent
META = {"seal.json", "seal.sha256", "inputs-manifest.json", "outputs-manifest.json"}


def digest(b):
    return hashlib.sha256(b).hexdigest()


def inventory():
    result = {}
    for p in BASE.rglob("*"):
        if p.is_symlink():
            raise ValueError("symlink in protected tree")
        if p.is_file():
            b = p.read_bytes()
            result[p.relative_to(BASE).as_posix()] = (len(b), digest(b))
    return result


def member(s):
    p = PurePosixPath(s)
    if p.is_absolute() or ".." in p.parts or p.as_posix() != s:
        raise ValueError("unsafe manifest member")
    return BASE / s


def record_ok(p, rec):
    b = p.read_bytes()
    if len(b) != rec["size"] or digest(b) != rec["sha256"]:
        raise ValueError("size/hash mismatch: " + str(p.relative_to(BASE)))
    return b


def main(anchor):
    seal_bytes = (BASE / "seal.json").read_bytes()
    if len(anchor) != 64 or digest(seal_bytes) != anchor:
        raise ValueError("external seal anchor mismatch")
    if (BASE / "seal.sha256").read_text().strip() != anchor:
        raise ValueError("detached anchor differs")
    seal = json.loads(seal_bytes)
    all_records = {}
    counts = {}
    for name in ["inputs-manifest.json", "outputs-manifest.json"]:
        records = json.loads(record_ok(BASE / name, seal["manifests"][name]))
        counts[name] = len(records)
        for rec in records:
            s = rec["path"]
            if s in all_records or s in META:
                raise ValueError("duplicate/reserved manifest member")
            if (name == "inputs-manifest.json") != s.startswith("inputs/"):
                raise ValueError("wrong input/output classification")
            record_ok(member(s), rec)
            all_records[s] = rec
    if set(inventory()) != set(all_records) | META:
        raise ValueError("exact membership mismatch")
    if digest((BASE / "original-scope.md").read_bytes()) != seal["scope_sha256"]:
        raise ValueError("frozen scope mismatch")
    tree = json.loads((BASE / "inputs/context/preprints-tree.json").read_bytes())
    if tree["truncated"] or tree["sha"] != "df0564b2deaab87e07854b6344d8c2f037682e77":
        raise ValueError("wrong/incomplete source tree")
    blobs = {x["path"]: x["sha"] for x in tree["tree"] if x["type"] == "blob"}
    source_records = json.loads((BASE / "source-records.json").read_bytes())
    for rec in source_records:
        b = record_ok(member(rec["path"]), rec)
        gh = hashlib.sha1(b"blob " + str(len(b)).encode() + b"\0" + b).hexdigest()
        if gh != rec["git_blob"] or blobs[rec["upstream_path"]] != gh:
            raise ValueError("pinned Git identity mismatch")
        prefix = "https://raw.githubusercontent.com/openai/math/"
        expected = prefix + "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/" + rec["upstream_path"]
        if rec["url"] != expected:
            raise ValueError("unpinned source URL")
    checker = BASE / "profile_diagnostic.py"
    checker_hash = all_records["profile_diagnostic.py"]["sha256"]
    runner = r'''
import sys, os, hashlib
def guard(event,args):
    if event == 'open':
        mode, flags = args[1], args[2]
        if (isinstance(mode,str) and any(x in mode for x in 'wax+')) or (isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
            raise PermissionError('read-only finite checker')
    if event.startswith('socket.') or event in {'subprocess.Popen','os.system','os.remove','os.rename','os.mkdir','os.rmdir','os.link','os.symlink','os.truncate','os.chmod','os.utime'}:
        raise PermissionError('write/network/process denied')
sys.addaudithook(guard)
p=sys.argv[1]
b=open(p,'rb').read()
if hashlib.sha256(b).hexdigest()!=sys.argv[2]:
    raise RuntimeError('checker changed after authentication')
exec(compile(b,p,'exec'),{'__name__':'__main__'})
'''
    result = subprocess.run(
        [sys.executable, "-I", "-B", "-c", runner, str(checker), checker_hash],
        cwd=BASE, capture_output=True, timeout=60,
    )
    if result.returncode:
        raise ValueError("authenticated finite checker failed: " + result.stderr.decode(errors="replace"))
    if result.stdout != (BASE / "profile-receipt.txt").read_bytes():
        raise ValueError("immutable stdout mismatch")
    if result.stderr != (BASE / "profile-stderr.txt").read_bytes():
        raise ValueError("immutable stderr mismatch")
    return {"status": "INTEGRITY_AND_ONE_FINITE_DIAGNOSTIC_ONLY",
            "target": "UNRESOLVED_FULL_Q4", "counted": False, "accepted_count": 4,
            "seal_sha256": anchor, "inputs": counts["inputs-manifest.json"],
            "outputs": counts["outputs-manifest.json"], "pinned_git_blobs": len(source_records),
            "own_files": len(all_records) + len(META),
            "historical_or_third_party_code_executed": False,
            "mathematical_or_contribution_PASS": False}


before = inventory()
try:
    if len(sys.argv) != 2:
        raise ValueError("usage: python -I -B verify.py EXTERNALLY_PINNED_SEAL_SHA256")
    answer = main(sys.argv[1])
    if inventory() != before:
        raise ValueError("protected tree changed during verification")
    answer["own_tree_unchanged"] = True
    print(json.dumps(answer, sort_keys=True))
except Exception as exc:
    unchanged = inventory() == before
    print(json.dumps({"status": "REJECT", "error": str(exc),
                      "own_tree_unchanged": unchanged}, sort_keys=True))
    sys.exit(1)
