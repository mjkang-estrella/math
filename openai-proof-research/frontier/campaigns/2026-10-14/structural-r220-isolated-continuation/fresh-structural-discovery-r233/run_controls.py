#!/usr/bin/env python3
"""Tiny copied artifact controls, run before sealing; never mathematical tests."""
import hashlib, json, runpy, shutil, stat
from pathlib import Path
R = Path("frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r233")
W = R / "control-work"
if W.exists(): raise RuntimeError("fresh control directory required")
W.mkdir()
original = W / "original.txt"
original.write_bytes(b"r233 tiny copied control\n")
original.chmod(0o444)
sha = hashlib.sha256(original.read_bytes()).hexdigest()
copydir = W / "copy"
copydir.mkdir()
p = copydir / "copied.txt"
shutil.copyfile(original, p)
p.chmod(0o444)
f = runpy.run_path(str(R / "verify_packet.py"))["verify_payload"]
e = [{"path": "copied.txt", "bytes": original.stat().st_size, "sha256": sha, "mode": "0444"}]
f(copydir, e, ["copied.txt"])
observed = {"unchanged_copy": "accepted"}
def rejects(label, paths):
    try: f(copydir, e, paths)
    except ValueError as exc: observed[label] = "rejected: " + str(exc)
    else: raise AssertionError("control unexpectedly accepted: " + label)
p.chmod(0o644)
p.write_bytes(b"r233 tiny copied CONTROl\n")
p.chmod(0o444)
rejects("changed_copy_bytes", ["copied.txt"])
p.chmod(0o644)
p.write_bytes(original.read_bytes())
p.chmod(0o640)
rejects("changed_copy_mode", ["copied.txt"])
p.chmod(0o444)
rejects("changed_exact_selection", ["copied.txt", "missing.txt"])
assert hashlib.sha256(original.read_bytes()).hexdigest() == sha
out = {"controls": observed, "original_sha256_before_and_after": sha, "original_unchanged": True,
       "copy_size_bytes": original.stat().st_size, "timing": "before one-time seal", "mathematical_verdict": "none"}
(R / "artifact-controls.json").write_text(json.dumps(out, indent=2) + "\n")
shutil.rmtree(W)
print(json.dumps(out, indent=2))
