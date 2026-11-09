"""Administrative preparation, static compilation only; never invokes arithmetic."""
import ast
import datetime
import hashlib
import json
from pathlib import Path
import shutil

ROOT = Path(__file__).resolve().parent
PROJECT = ROOT.parents[2]
assert PROJECT.name == "factoring-research"
assert not (ROOT / "RUN-ONCE.json").exists()
assert not (ROOT / "freeze-manifest.json").exists()
inputs = ["AGENTS.md", "RESEARCH_TEAM.md", "RESEARCH_LOOP.md", "README.md",
          "docs/SPECIFICATION.md", "research/STATE.md", "research/hypotheses/W032.md",
          "research/hypotheses/W031.md", "research/findings/W031-jet-parent-disposition.md",
          "research/findings/W031-reversed-jet-review.md"]
for source in inputs:
    target = ROOT / "inputs" / source
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(PROJECT / source, target)
cases = [{"index": a, "N": 143, "a": a} for a in range(143)]
cases += [{"index": 143 + i, "N": 323, "a": a}
          for i, a in enumerate([1, 2, 3, 5, 7, 11, 13, 17, 23, 31, 47, 61])]
config = {"Rmax": 4, "limits": {"events": 20000, "seconds": 60}, "cases": cases,
          "groups": [{"N": 143, "reference_factors": [11, 13],
                      "matrix_reference_a": [1, 2, 3, 5, 7]},
                     {"N": 323, "reference_factors": [17, 19], "matrix_reference_a": []}]}
(ROOT / "cases.json").write_text(json.dumps(config, indent=2) + "\n")
for path in sorted(ROOT.glob("*.py")):
    tree = ast.parse(path.read_text(), filename=str(path))
    compile(tree, str(path), "exec")
files = []
for path in sorted(ROOT.rglob("*")):
    if path.is_file():
        data = path.read_bytes()
        files.append({"path": path.relative_to(ROOT).as_posix(), "bytes": len(data),
                      "sha256": hashlib.sha256(data).hexdigest()})
manifest = {"frozen_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
            "case_count": len(cases), "candidate_executions_before_freeze": 0,
            "static_source_compilation": "passed; no candidate/reference execution",
            "files": files}
path = ROOT / "freeze-manifest.json"
path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
print(json.dumps({"freeze_manifest": path.name, "files": len(files),
                  "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}, sort_keys=True))
