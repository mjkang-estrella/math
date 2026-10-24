#!/usr/bin/env python3
"""Read-only exact-selection verifier; every trust anchor is explicit and required."""
import argparse, hashlib, json, os, stat
from pathlib import Path, PurePosixPath

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok, message):
    if not ok:
        raise ValueError(message)
def verify(a):
    packet = Path(a.packet)
    require(packet.is_dir() and not packet.is_symlink(), "unsafe packet root")
    require(stat.S_IMODE(packet.stat().st_mode) == 0o700, "packet root mode")
    anchored = [(Path(a.manifest), a.manifest_sha), (Path(a.selection), a.selection_sha),
                (Path(a.report), a.report_sha), (packet / "FINAL.md", a.final_sha)]
    for p, expected in anchored:
        require(p.is_file() and not p.is_symlink(), "unsafe anchored file: " + str(p))
        require(len(expected) == 64 and sha(p) == expected, "anchor mismatch: " + str(p))
    m = json.loads(Path(a.manifest).read_text())
    selection = json.loads(Path(a.selection).read_text())
    require(m["selection_sha256"] == a.selection_sha, "selection binding")
    entries = m["entries"]
    require([{k: e[k] for k in ("path", "kind", "mode")} for e in entries] == selection,
            "manifest/selection disagreement")
    paths = [e["path"] for e in entries]
    require(len(paths) == len(set(paths)), "duplicate entry")
    for path in paths:
        rel = PurePosixPath(path)
        require(not rel.is_absolute() and ".." not in rel.parts and rel.as_posix() == path,
                "unsafe selected path")
    actual = []
    for directory, dirs, files in os.walk(packet, followlinks=False):
        for name in dirs + files:
            p = Path(directory) / name
            require(not p.is_symlink(), "symlink")
            actual.append(p.relative_to(packet).as_posix())
    require(sorted(actual) == sorted(paths), "extra or missing entry")
    for e in entries:
        p = packet / e["path"]
        require(format(stat.S_IMODE(p.stat().st_mode), "04o") == e["mode"],
                "mode mismatch: " + e["path"])
        if e["kind"] == "dir":
            require(p.is_dir(), "directory kind mismatch")
        else:
            require(e["kind"] == "file" and p.is_file(), "file kind mismatch")
            require(p.stat().st_size == e["bytes"] and sha(p) == e["sha256"],
                    "content mismatch: " + e["path"])
    return {"artifact_check": "PASS", "files": sum(e["kind"] == "file" for e in entries),
            "entries": len(entries), "exact_selection_modes_bytes": True, "mathematical_gate": False}

def main():
    parser = argparse.ArgumentParser()
    for name in ("packet", "manifest", "selection", "report", "final-sha", "manifest-sha", "selection-sha", "report-sha"):
        parser.add_argument("--" + name, required=True)
    try:
        print(json.dumps(verify(parser.parse_args())))
    except (ValueError, OSError, KeyError, TypeError) as exc:
        print("REJECTED: " + str(exc))
        raise SystemExit(1)
if __name__ == "__main__":
    main()
