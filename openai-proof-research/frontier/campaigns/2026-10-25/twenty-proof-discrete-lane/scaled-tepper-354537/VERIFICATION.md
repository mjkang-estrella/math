# Verification result

PASS: clean rebuild with warnings as errors, 3 declarations checked, and all declaration axiom reports accepted.

- Lean: `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`
- Axioms observed: `Classical.choice, Quot.sound, propext`
- Final theorem: `ScaledTepper.mathdb354537`
- Full build record: `formal/build/audit.json`
- Compiler theorem/axiom output: `formal/build/Checks.log`
- Source archive hashes: `sources/manifest.json`

Rebuild with `python formal/rebuild.py` while located in this packet, or use its absolute path from anywhere. No dependency downloads or modifications are performed by the rebuild. The paper is supplied as `paper/main.tex`; no PDF was generated.
