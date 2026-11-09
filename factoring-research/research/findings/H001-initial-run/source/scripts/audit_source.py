"""Honest-mistake screen only; the Lean kernel and printed axioms are authoritative."""
import re
from pathlib import Path

root = Path(__file__).resolve().parents[1]
paths = list((root / "Factoring").glob("*.lean")) + [root / "Factoring.lean", root / "Audit.lean"]
for path in paths:
    text = path.read_text()
    # Deliberately includes comments; keep prohibited proof escapes out of sources.
    if re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", text):
        raise SystemExit(f"Review prohibited proof escape in {path}")
print("Lean source escape screen passed (not an adversarial security audit).")

