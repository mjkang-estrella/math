"""Read-only integrity and one bounded local-arithmetic replay.
Myeongjin Kang; no affiliation. Original code MIT.
Trust the detached seal anchor separately. This is not a proof review.
"""
from pathlib import Path, PurePosixPath
import hashlib
import json
import subprocess
import sys

BASE = Path(__file__).resolve().parent
REPO = BASE.parents[3]
FROZEN = REPO / "frontier/campaigns/2026-10-14/fresh-structural-discovery-r12"
META = {"seal.json", "seal.sha256", "inputs-manifest.json", "outputs-manifest.json"}
OLD_ANCHOR = "275a6f95416d1a47f97ecbf65ee4d027ce4d253354af210ffd2fd8c246fcabe3"
SCOPE = "adfa4c4898f9cc592089cf48d4a7ac15c448c15f494a39ccc2b11b0da3159e99"
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"


def digest(b):
    return hashlib.sha256(b).hexdigest()


def inventory(root):
    result = {}
    for p in root.rglob("*"):
        if p.is_symlink():
            raise ValueError("symlink in protected tree")
        if p.is_file():
            b = p.read_bytes()
            result[p.relative_to(root).as_posix()] = (len(b), digest(b))
    return result


def member(root, s):
    p = PurePosixPath(s)
    if p.is_absolute() or ".." in p.parts or p.as_posix() != s:
        raise ValueError("unsafe manifest path")
    return root / s


def checked(p, r):
    b = p.read_bytes()
    if len(b) != r["size"] or digest(b) != r["sha256"]:
        raise ValueError("size/hash mismatch: " + str(p))
    return b


def sealed(root, anchor):
    seal_bytes = (root / "seal.json").read_bytes()
    if len(anchor) != 64 or digest(seal_bytes) != anchor:
        raise ValueError("external seal anchor mismatch")
    if (root / "seal.sha256").read_text().strip() != anchor:
        raise ValueError("detached anchor mismatch")
    seal = json.loads(seal_bytes)
    records, counts = {}, {}
    for name in ["inputs-manifest.json", "outputs-manifest.json"]:
        entries = json.loads(checked(root / name, seal["manifests"][name]))
        counts[name] = len(entries)
        for rec in entries:
            s = rec["path"]
            if s in META or s in records:
                raise ValueError("duplicate/reserved manifest member")
            if s.startswith("inputs/") != (name == "inputs-manifest.json"):
                raise ValueError("input/output classification mismatch")
            checked(member(root, s), rec)
            records[s] = rec
    if set(inventory(root)) != set(records) | META:
        raise ValueError("exact membership mismatch")
    if digest((root / "original-scope.md").read_bytes()) != SCOPE:
        raise ValueError("unchanged scope mismatch")
    return records, counts


def main(anchor):
    own, counts = sealed(BASE, anchor)
    old, old_counts = sealed(FROZEN, OLD_ANCHOR)
    external = json.loads((BASE / "external-inventory.json").read_bytes())
    if external["seal_sha256"] != OLD_ANCHOR or REPO / external["root"] != FROZEN:
        raise ValueError("wrong external root or anchor")
    external_paths = set()
    for rec in external["exact_files"]:
        p = member(REPO, rec["path"])
        if not p.is_relative_to(FROZEN) or rec["path"] in external_paths:
            raise ValueError("external inventory escape/duplicate")
        checked(p, rec)
        external_paths.add(rec["path"])
    actual = {p.relative_to(REPO).as_posix() for p in FROZEN.rglob("*") if p.is_file()}
    if actual != external_paths or len(actual) != 116:
        raise ValueError("external exact membership mismatch")
    if len(old) != 112 or old_counts != {"inputs-manifest.json": 88, "outputs-manifest.json": 24}:
        raise ValueError("wrong final R12 fixture")

    tree = json.loads((BASE / "inputs/context/preprints-tree.json").read_bytes())
    if tree["truncated"] or tree["sha"] != "df0564b2deaab87e07854b6344d8c2f037682e77":
        raise ValueError("wrong or truncated catalogue")
    catalogue = {e["path"]: e["sha"] for e in tree["tree"] if e["type"] == "blob"}
    blobs = json.loads((BASE / "pinned-blobs.json").read_bytes())
    if len(blobs) != 50:
        raise ValueError("wrong pinned blob count")
    for rec in blobs:
        if rec["path"] not in external_paths:
            raise ValueError("unbound external source")
        b = checked(member(REPO, rec["path"]), rec)
        g = hashlib.sha1(b"blob " + str(len(b)).encode() + b"\0" + b).hexdigest()
        if g != rec["git_blob"] or g != catalogue[rec["upstream_path"]]:
            raise ValueError("pinned Git blob mismatch")
        expected = "https://raw.githubusercontent.com/openai/math/" + PIN + "/" + rec["upstream_path"]
        if rec["url"] != expected:
            raise ValueError("unpinned source URL")
    for rec in json.loads((BASE / "retrievals.json").read_bytes()):
        if "error" in rec:
            continue
        p = BASE / "inputs/private/literature" / (rec["name"] + ".pdf")
        checked(p, rec)

    checker = BASE / "junction_diagnostic.py"
    checker_hash = own[checker.name]["sha256"]
    auth = json.loads((BASE / "pre-execution.json").read_bytes())
    if auth["sha256"] != checker_hash or not auth["inspected_before_execution"]:
        raise ValueError("checker pre-execution record mismatch")
    runner = r'''
import sys, os, hashlib
def guard(event,args):
    if event == 'open':
        mode,flags=args[1],args[2]
        if (isinstance(mode,str) and any(c in mode for c in 'wax+')) or (isinstance(flags,int) and flags & (os.O_WRONLY|os.O_RDWR|os.O_CREAT|os.O_TRUNC|os.O_APPEND)):
            raise PermissionError('read-only local diagnostic')
    if event.startswith('socket.') or event in {'subprocess.Popen','os.system','os.remove','os.rename','os.mkdir','os.rmdir','os.link','os.symlink','os.truncate','os.chmod','os.utime','os.exec','os.posix_spawn','os.fork'}:
        raise PermissionError('write/network/process denied')
sys.addaudithook(guard)
b=open(sys.argv[1],'rb').read()
if hashlib.sha256(b).hexdigest()!=sys.argv[2]:
    raise ValueError('checker changed after authentication')
exec(compile(b,sys.argv[1],'exec'),{'__name__':'__main__'})
'''
    result = subprocess.run([sys.executable, "-I", "-B", "-c", runner, str(checker), checker_hash],
                            cwd=BASE, capture_output=True, timeout=30)
    if result.returncode:
        raise ValueError("local diagnostic failed: " + result.stderr.decode(errors="replace"))
    if result.stdout != (BASE / "diagnostic-stdout.json").read_bytes():
        raise ValueError("immutable diagnostic stdout differs")
    if result.stderr != (BASE / "diagnostic-stderr.txt").read_bytes():
        raise ValueError("immutable diagnostic stderr differs")
    return {"status": "INTEGRITY_AND_ONE_JUNCTION_DIAGNOSTIC_ONLY",
            "target": "UNRESOLVED_FULL_Q4", "counted": False, "accepted_count": 4,
            "seal_sha256": anchor, "inputs": counts["inputs-manifest.json"],
            "outputs": counts["outputs-manifest.json"], "own_files": len(own) + len(META),
            "external_frozen_files": len(actual), "pinned_git_blobs": len(blobs),
            "historical_or_third_party_code_executed": False,
            "independent_mathematical_or_contribution_PASS": False}


if __name__ == "__main__":
    before = inventory(BASE)
    frozen_before = inventory(FROZEN)
    try:
        if len(sys.argv) != 2:
            raise ValueError("usage: python -I -B verify.py EXTERNALLY_TRUSTED_SEAL_SHA256")
        result = main(sys.argv[1])
        if inventory(BASE) != before or inventory(FROZEN) != frozen_before:
            raise ValueError("protected trees changed during verification")
        result["own_and_frozen_trees_unchanged"] = True
        print(json.dumps(result, sort_keys=True))
    except Exception as exc:
        unchanged = inventory(BASE) == before and inventory(FROZEN) == frozen_before
        print(json.dumps({"status": "REJECT", "error": str(exc),
                          "own_and_frozen_trees_unchanged": unchanged}, sort_keys=True))
        sys.exit(1)
