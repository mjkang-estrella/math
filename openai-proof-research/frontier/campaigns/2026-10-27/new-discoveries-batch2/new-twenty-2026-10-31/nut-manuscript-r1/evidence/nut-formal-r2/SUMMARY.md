# MathDB 365943 r2: milestone NOT achieved, zero credit

Part A is incomplete. `endpoint_of_finite` does not exist, `FiniteObstruction`
is only a definition, and `Nut8.Target` has no proof. The assignment says a
partial packet earns zero credit; this packet does not satisfy its acceptance
gate. No counts were changed and no result is self-accepted.

Completed additions:

- A1: `nut_circulant_global_coordinates` constructs V ≃ Fin 8 × ZMod m
  directly from the inherited Nut/Circulant predicates, with m > 0 and the
  generator acting by translation. All inherited Nut.lean bytes are unchanged.
- Periodic integral character representative independence, multiplication,
  sign values and negation. A raw signed graph quotient is defined.
- Quotient symmetry given labelled adjacency translation invariance;
  quotient kernel restriction given the explicit coordinate character formula.
  Deriving these hypotheses from the global graph is still missing.
- A decidable coherent signed-matrix grammar, unsigned absolute-entry quotient,
  trivial-character specialization, and explicit finite obstruction proposition.
  The graph-to-grammar extraction is missing.
- Sparse dimension-indexed determinant evaluation proved equal to Matrix.det
  in every dimension, and proved principal-cofactor evaluation. Four concrete
  actual determinant/cofactor equalities are kernel-checked.

The diagnostic generator without the unsigned pretest yields 194 underlying
catalogue graphs, 669 augmentations and 9,172 normalized signings. Exact integer
arithmetic excludes all: 8,208 nonzero determinants and 964 zero principal
cofactors. This suggests removing the unsigned-pretest proof dependency. The
catalogue and normalization completeness are NOT formally proved. All 9,172
Python witnesses are saved; only four are newly checked in Lean.

The fresh source-only extraction `fresh-extracted` passed strict sanitized
Lean rebuild and separate leanchecker for all eleven modules. The full audit
includes all 95 local declarations (58 over r1), including generated
ones: types, opaque-inclusive bodies, unsafe/partial/axiom flags and transitive
axioms. Only propext, Classical.choice and Quot.sound occur. All three Lean
negative controls were rejected; the fourth control confirmed refusal of
existing oleans. The 25 replay calls used 69.30 summed wall seconds;
peak sampled private memory was 2,426,953,728 bytes. Every call stayed within caps.
The full audit is `fresh-extracted/logs/strict-Audit.log`.

The exact formal gaps are in GAPS.md. In particular, the graph-specific kernel
lift/nullity transfer, local graph grammar, symmetric adjugate support lemma,
conditional endpoint and proved finite normal form are still absent. The Part B
design includes the warning that epsilon = 1 positivity is not preserved by
arbitrary switching; the future proof must use a structural overapproximation.

All 22 assigned/auxiliary inputs were hash-bound before and after and copied
with SHA-256 identity, including the assigned r1 packet hash. No prior-art gate
was repeated. No child agents, git, shared ledger edits, browser tabs, network
requests, publication or external messages were used. Writes are inside this
lane. No background jobs remain at handback.

Source-only deliverable: nut-r2-source.zip. REPRODUCE.md describes its portable
replay. Final source identities are checked against the successful fresh replay;
its source-only provenance is recorded in packet-manifest.json. Root alone may
adjudicate acceptance of a future complete result.
