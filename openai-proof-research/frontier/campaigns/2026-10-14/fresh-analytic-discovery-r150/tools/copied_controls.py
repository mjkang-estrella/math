"""Small independent selected-copy fixture; never modifies incoming originals."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

r = Path("frontier/campaigns/2026-10-14/fresh-analytic-discovery-r150")
c = r / "private/controls/selected"
if c.exists():
    raise SystemExit("refuse to regenerate an existing selected-copy fixture")
(c / "original-prose").mkdir(parents=True)
(c / "protected-source").mkdir()
pairs = [
    (r / "GAPS.md", c / "original-prose/GAPS.md"),
    (r / "private/pinned-source/variance.tex", c / "protected-source/variance.tex")
]
sha = lambda b: hashlib.sha256(b).hexdigest()
original_hashes = {str(a): sha(a.read_bytes()) for a, _ in pairs}
for a, b in pairs:
    b.write_bytes(a.read_bytes())
envelopes = ["FINAL.md", "MANIFEST.json", "REPORT.md"]
rows = [{"path": b.relative_to(c).as_posix(), "size": b.stat().st_size,
         "sha256": sha(b.read_bytes())} for _, b in pairs]
(c / "FINAL.md").write_text("Selected-copy control only. No mathematical gate.\n")
(c / "REPORT.md").write_text("Two selected payloads, own membership manifest; original rights retained.\n")
(c / "MANIFEST.json").write_text(json.dumps(
    {"version": 1, "envelopes": envelopes, "files": sorted(rows, key=lambda x:x["path"])},
    indent=2) + "\n")
# Detached anchors use sha256sum, independently of manifest construction.
anchors = {}
for name in envelopes:
    anchors[name] = subprocess.check_output(["sha256sum", str(c/name)], text=True).split()[0]
base = [sys.executable, "-B", str(r / "tools/verify.py"), str(c)]
for name, option in [("FINAL.md", "final"), ("MANIFEST.json", "manifest"), ("REPORT.md", "report")]:
    base += ["--" + option + "-sha256", anchors[name]]
def snapshot():
    return {p.relative_to(c).as_posix(): (p.stat().st_size, sha(p.read_bytes()))
            for p in c.rglob("*") if p.is_file()}
records = []
def run(name, good, command=base):
    before = snapshot()
    proc = subprocess.run(command, capture_output=True, text=True, timeout=20)
    after = snapshot()
    assert before == after, "verifier wrote to fixture"
    assert (proc.returncode == 0) == good, (name, proc.stdout, proc.stderr)
    records.append({"case": name, "expected_accept": good, "exit_code": proc.returncode,
                    "read_only_snapshot_unchanged": True,
                    "output": (proc.stdout + proc.stderr).strip()})
run("baseline", True)
target = pairs[0][1]; original = target.read_bytes()
target.write_bytes(original + b"\nmutation\n"); run("changed-payload", False)
target.write_bytes(original)
target.unlink(); run("missing-payload", False); target.write_bytes(original)
extra = c / ".extra"; extra.write_text("unexpected\n"); run("hidden-extra", False); extra.unlink()
wrong = list(base); wrong[wrong.index("--manifest-sha256")+1] = "0"*64
run("wrong-detached-manifest-anchor", False, wrong)
run("restoration", True)
assert all(sha(Path(a).read_bytes()) == h for a,h in original_hashes.items())
assert all(a.read_bytes() == b.read_bytes() for a,b in pairs)
out = {"fixture": str(c), "selected_originals": original_hashes,
       "independent_detached_anchors": anchors, "cases": records,
       "originals_unchanged": True, "restored_copies_match": True,
       "not_a_mathematical_gate": True}
(r / "private/controls/results.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps({"copied_control_cases": len(records), "all_expected": True,
                  "read_only": True, "originals_unchanged": True}))
