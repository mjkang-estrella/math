#!/usr/bin/env python3
"""Read-only checks of frozen inputs; only this review directory is written.

Run: python3 -I frontier/campaigns/2026-10-14/p-gradient-manuscript-review-r1/checks/run_checks.py
No git, lake, network, manuscript editing, or publication operation occurs.
These checks do not prove any analytic statement.
"""
from pathlib import Path
import difflib
import hashlib
import json
import os
import re
import subprocess

HERE = Path(__file__).resolve().parent
REVIEW = HERE.parent
CAMPAIGN = REVIEW.parent
ROOT = CAMPAIGN.parents[2]
MANUSCRIPT = CAMPAIGN / "p-gradient-manuscript"
CONSOLIDATION = CAMPAIGN / "p-gradient-manuscript-consolidation"
FORMAL = CAMPAIGN / "formal"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


checks = {}
for receipt, key, base in [
    (MANUSCRIPT / "validation.json", "sha256", MANUSCRIPT),
    (CONSOLIDATION / "outputs.json", "manuscript_sha256", MANUSCRIPT),
    (CONSOLIDATION / "outputs.json", "consolidation_sha256", CONSOLIDATION),
    (FORMAL / "validation.json", "sha256", FORMAL),
]:
    values = json.loads(receipt.read_text())[key]
    for name, expected in values.items():
        path = base / name
        assert sha(path) == expected, str(path)
checks["receipt_hashes"] = "PASS"

for path, expected in [
    (ROOT / "frontier/experiments/i345_lifted_p_gradient_research/analysis.md", "f88c4ad3f983eb405912679864c7b8d5e64e933eb486f6cf1c49a8e9deabaa25"),
    (CAMPAIGN / "p-gradient-parent/proof-repair-addendum.md", "d3ff16a1a09f1b9f8eb265514b17a3ea726e47609c1c8abd1ab31b47dcfe0b02"),
    (CAMPAIGN / "p-gradient-uniformity/lemma.md", "064522733f852069bcc50ac8faf2580a0f4bb2651b520e4437c1799f7c34774e"),
    (MANUSCRIPT / "viscous-appendix.tex", "1685cc94d4a0956debc413a063718b60be68074d4f2152ea167b9852f92c4e65"),
]:
    assert sha(path) == expected, str(path)
checks["four_reviewed_inputs"] = "PASS"

delta = "".join(difflib.unified_diff(
    (MANUSCRIPT / "viscous-appendix.tex").read_text().splitlines(keepends=True),
    (MANUSCRIPT / "viscous-appendix-typeset.tex").read_text().splitlines(keepends=True),
    fromfile="viscous-appendix.tex (frozen reviewed)",
    tofile="viscous-appendix-typeset.tex (consolidated)",
))
assert delta == (CONSOLIDATION / "appendix-final.diff").read_text()
checks["appendix_delta"] = "PASS"

active = ["main.tex", "compact-p.tex", "scales-and-limits.tex", "large-viscosity.tex", "viscous-appendix-typeset.tex", "references.tex"]
tex = "\n".join((MANUSCRIPT / name).read_text() for name in active)
labels = re.findall(r"\\label\{([^}]+)\}", tex)
refs = re.findall(r"\\(?:eqref|ref)\{([^}]+)\}", tex)
assert len(labels) == len(set(labels))
assert not set(refs) - set(labels)
keys = set(re.findall(r"\\bibitem\{([^}]+)\}", tex))
for cite in re.findall(r"\\cite(?:\[[^]]*\])?\{([^}]+)\}", tex):
    assert set(cite.split(",")) <= keys
checks["references"] = {"labels": len(labels), "bibliography_keys": len(keys), "status": "PASS"}

log = (MANUSCRIPT / "output/pdf/main.log").read_text()
warnings = [line for line in log.splitlines() if re.search(r"(?i)(?:^|\s)(?:warning:|LaTeX Warning|Package \w+ Warning|overfull|underfull|missing character|undefined reference|undefined citation)", line)]
assert not warnings, warnings
pdftext = subprocess.run(["pdftotext", "-layout", str(MANUSCRIPT / "output/pdf/main.pdf"), "-"], check=True, text=True, capture_output=True).stdout
assert pdftext == (CONSOLIDATION / "main.txt").read_text()
assert pdftext.count("\f") == 21
checks["pdf_text_and_log"] = "PASS: 21 pages; no diagnostic warnings"

assert (FORMAL / ".lake/packages/mathlib/.git/HEAD").read_text().strip() == "d13f23b723b8a846827a245b89c10fc7d3f11612"
lean = ROOT.parent / "dlp-research/.tools/lean-4.34.1-linux/bin/lean"
assert lean.is_file(), str(lean)
env = os.environ.copy()
env["LEAN_PATH"] = ":".join(str(path.resolve()) for path in (FORMAL / ".lake/packages").glob("*/.lake/build/lib/lean"))
version = subprocess.run([str(lean), "--version"], check=True, capture_output=True, text=True).stdout.strip()
checks["lean_version"] = version
for module, names, target, logfile in [
    ("VectorEllipticity", ["norm_smul_sub_sq", "gram_nonneg", "square_decomposition", "lower_certificate", "bounds", "uniform_bounds", "physical_uniform_bounds"], "VectorAudit.lean", "lean-audit.txt"),
    ("LiftedEllipticity", ["square_decomposition", "bounds", "uniform_lower"], "ScalarAudit.lean", "scalar-lean-audit.txt"),
]:
    source = (FORMAL / "FrontierSupport" / (module + ".lean")).read_text()
    extra = "\n" + "".join("#print axioms FrontierSupport." + module + "." + name + "\n" for name in names)
    audit = HERE / target
    audit.write_text(source + extra)
    result = subprocess.run([str(lean), str(audit)], env=env, capture_output=True, text=True)
    output = result.stdout + result.stderr
    (HERE / logfile).write_text("Source is verbatim " + module + " plus #print axioms; existing package oleans only.\n" + output + "exit=" + str(result.returncode) + "\n")
    assert result.returncode == 0, output
    assert output.count("depends on axioms: [propext, Classical.choice, Quot.sound]") == len(names), output
    checks[module] = "PASS: fresh source elaboration and standard-axiom audit"

(HERE / "run-output.json").write_text(json.dumps(checks, indent=2) + "\n")
print(json.dumps(checks, indent=2))
