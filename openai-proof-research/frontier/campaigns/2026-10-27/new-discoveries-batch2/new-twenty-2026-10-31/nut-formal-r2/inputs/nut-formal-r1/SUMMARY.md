# MathDB 365943: partial formalization, zero credit

The requested theorem `no_cubic_8circulant_nut` was NOT completed. No result is
self-accepted, no campaign count changed, and this packet cannot count as a
solution. `Nut8.Target` is only the literal proposition definition.

Proved in Lean 4.34.1 against the assigned pinned mathlib cache:

- Source-faithful cubic and real-nullity nut definitions, plus an integer-power
  cyclic-generator definition with exactly eight equal-sized orbits.
- Equal orbit sizes force the common generator period; local orbit period
  divisibility and a `Fin m` equivalence with each orbit, including singletons.
- Automorphism pullback commutes with the adjacency operator and preserves its
  kernel. A stable one-dimensional real space carries a scalar character.
- A finite-period scalar is +1 or -1; the negative case has even period.
  `nut_sign_character` applies this to a full nonzero nut kernel vector.
- Two kernel-reduced list determinant pilot computations. Their interpretation
  as actual matrix determinants is NOT proved.

The quotient construction, its injective kernel lift, local signed-quotient
constraints, complete symmetry reduction and the final finite obstruction are
still missing. GAPS.md gives the shortest remaining decomposition and measured
case/kernel-cost estimates. In particular, the unsigned pretest excludes cases
not represented by the final certificates, and must also be formalized.

No public resolution was located by the bounded prior-art gate. Current arXiv
has only v1 and the published paper retains the conjecture. Later actual
primary theorem statements were compared. Omega HEAD advanced during this
check; its current Laman–Henneberg commit does not concern nut graphs, but
HEAD-only access does not certify all intervening registry contents. The
Nut digraphs repository PDF returned 403 and was not retried. See PRIOR-ART.md.

Fresh source-only extraction `fresh-extracted-03` passed strict sanitized
`lean -j1 -DwarningAsError=true` rebuild and separate leanchecker for all three
modules. The full module-origin audit printed types, opaque-inclusive bodies,
flags and transitive axioms for all 37 local declarations: 29 in Nut and 8 in
CertificateBench, including generated declarations. Every flag passed; only
propext, Classical.choice and Quot.sound occur. The audit module adds no named
logical declarations. The three Lean negative controls were rejected; an
additional driver control verified refusal of existing oleans. Full receipts
and logs are under `fresh-extracted-03/logs`.

Earlier failed trials remain visible. The initial dense determinant pilot hit
the memory watchdog. The first extracted audit had a counter-type inference
error. The second caught a compiler-generated partial `_unsafe_rec`; making
the kernel-reducible determinant definition noncomputable removed executable
code generation, and the third fresh replay passed the same audit without
weakening it. Final replay sampled peak private memory was
2,374,864,896 bytes and all calls stayed within caps.

All 40 input files were hash-bound before/after and copied with SHA-256 identity.
The originally assigned NUT-ROUTE hash matches. No child agents, git commands,
shared ledger edits, browser tabs, external messages, or background jobs were
used or left running. All writes are confined to this lane.

Source-only packet: `nut-partial-source.zip`.
SHA-256: `3997c9a42ba7839ed33021370ed69838c42254b5aee301369798d2b127191212`.
Replay instructions: REPRODUCE.md. Exact statement mapping:
statement-correspondence.md. Root alone may adjudicate any future full result.
