# Focused Hamiltonian affine-span second attempt

Status: **UNRESOLVED**, full original H retained; not nominated or counted.
Read candidate.md for the complete mathematical report, source-contracts.md
for exact input interfaces/read extents, and progress.md for checkpoints.

The original scope/status were created before sustained research. The frozen
r6 package was authenticated first; none of its code was executed.

For integrity and exact finite replay, use Python 3.10+:

    python -I -B verify.py --seal-sha256 <externally-retained-seal-hash>

The external hash is the SHA256 of seal.json, reported in the handoff.
seal.sha256 repeats it locally but cannot independently establish trust.
The verifier authenticates all bytes before checker execution and never
writes any file, on success or failure. No code regenerates receipts during
verification. It checks both this complete tree and the frozen sibling tree
before/after. The two mathematical programs also have no file-write branches.
Their fixtures/receipts are immutable after sealing. The original frozen
r6 generate_probe.py is not imported or run.

Finite replay supports the exact diagnostic formulas and certificates; it
cannot prove the all-graph span identity. No independent proof PASS or
contribution PASS is asserted. Original prose CC BY 4.0; code MIT; author
Myeongjin Kang, no affiliation. Private third-party inputs retain their rights.
