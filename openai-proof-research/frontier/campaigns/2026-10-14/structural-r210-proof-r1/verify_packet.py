"""Read-only verifier for an exact independent review selection.
All three SHA256 anchors are mandatory. This is an artifact check only.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import stat

FORMAT = "structural210-proof-review-r1-v1"

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def require(condition, reason):
    if not condition:
        raise ValueError(reason)

def inventory(root):
    root = Path(root)
    entries = {}
    def visit(path, name):
        info = path.lstat()
        mode = format(stat.S_IMODE(info.st_mode), "04o")
        if stat.S_ISDIR(info.st_mode):
            entries[name] = {"type": "directory", "mode": mode}
            for child in sorted(os.scandir(path), key=lambda item: item.name):
                visit(Path(child.path), child.name if name == "." else name + "/" + child.name)
        elif stat.S_ISREG(info.st_mode):
            entries[name] = {"type": "file", "mode": mode, "bytes": info.st_size, "sha256": digest(path)}
        else:
            raise ValueError("Nonregular or symbolic-link selection: " + name)
    visit(root, ".")
    return entries

def verify(packet, manifest, manifest_sha256, final_sha256, report, report_sha256):
    packet, manifest, report = map(Path, (packet, manifest, report))
    require(digest(manifest) == manifest_sha256, "Detached MANIFEST mismatch")
    document = json.loads(manifest.read_text())
    require(document["format"] == FORMAT, "Manifest format mismatch")
    expected = document["entries"]
    names = [entry["path"] for entry in expected]
    require(len(names) == len(set(names)), "Duplicate manifest path")
    for name in names:
        path = PurePosixPath(name)
        require(not path.is_absolute() and ".." not in path.parts, "Unsafe manifest path")
        require(name == "." or path.as_posix() == name, "Noncanonical manifest path")
    actual = inventory(packet)
    require(set(actual) == set(names), "Extra or missing selected entry")
    for entry in expected:
        description = {key: value for key, value in entry.items() if key not in ("path", "rights")}
        require(actual[entry["path"]] == description, "Selected byte/type/mode mismatch: " + entry["path"])
        if entry["path"] == "private" or entry["path"].startswith("private/"):
            wanted = "0700" if description["type"] == "directory" else "0600"
            require(description["mode"] == wanted, "Protected entry mode mismatch")
    final = document["final"]
    require(final in actual and actual[final]["type"] == "file", "FINAL absent")
    require(actual[final]["sha256"] == final_sha256, "Detached FINAL mismatch")
    require(not report.resolve().is_relative_to(packet.resolve()), "REPORT must be outside selected packet")
    info = report.lstat()
    require(stat.S_ISREG(info.st_mode), "REPORT is not a regular file")
    require(stat.S_IMODE(info.st_mode) == 0o644, "REPORT mode mismatch")
    require(digest(report) == report_sha256, "Detached REPORT mismatch")
    return {
        "verification": "PASS: exact selected bytes, types, modes and all detached anchors",
        "files": sum(item["type"] == "file" for item in actual.values()),
        "directories": sum(item["type"] == "directory" for item in actual.values()),
        "FINAL_SHA256": final_sha256,
        "MANIFEST_SHA256": manifest_sha256,
        "REPORT_SHA256": report_sha256,
        "protected_modes_verified": True,
        "read_only": True,
        "mathematical_evidence": False,
    }

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("packet", "manifest", "manifest-sha256", "final-sha256", "report", "report-sha256"):
        parser.add_argument("--" + name, required=True)
    args = parser.parse_args()
    result = verify(args.packet, args.manifest, args.manifest_sha256, args.final_sha256, args.report, args.report_sha256)
    print(json.dumps(result, indent=2))
