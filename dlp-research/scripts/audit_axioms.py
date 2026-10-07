"""Check printed dependencies for every theorem listed in Audit.lean."""
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parents[1]
expected = re.findall(r"^#print axioms (\S+)", (root / "Audit.lean").read_text(), re.M)
text = sys.stdin.read()
allowed = {"propext", "Classical.choice", "Quot.sound"}
for theorem in expected:
    prefix = rf"'{re.escape(theorem)}' "
    if re.search(prefix + r"does not depend on any axioms", text):
        continue
    match = re.search(prefix + r"depends on axioms:\s*\[([^\]]*)\]", text)
    if not match:
        sys.exit(f"Missing axiom report: {theorem}")
    axioms = {s.strip() for s in match.group(1).split(",") if s.strip()}
    if axioms - allowed:
        sys.exit(f"Unapproved dependencies in {theorem}: {sorted(axioms - allowed)}")
print(f"Axiom audit passed ({len(expected)} declarations).")
