# Root cellular-automaton lane

Status: period-9 target **EXCLUDED — exact public prior theorem**, credit 0.
Period-formula conjectures remain unproved in this lane.

Primary: Formenti–Kamilya, arXiv:2606.13159v1 (11 June 2026),
EPTCS 445 (2026), 95–103, DOI 10.4204/EPTCS.445.12.
Actual HTML definitions, update table, Sections 3–7 read. Live abs lists only v1.

1. Initial target: Conjectures 2/3, odd/even exact period formulas, MathDB
   375268/375269. Literal-rule simulation agrees for k=0,…,11. No proof and no
   credit from this finite agreement. The C++ scan could not run: no g++ in this
   environment. The independently executable JS bit-mask scan did run.
2. New target: Section 3 Question 1 (are all multiples of 3 finite-configuration
   periods?) and the explicit period-9 gap in Section 7. Candidate theorem:
   every finite initial configuration fixed by the ninth iterate is fixed by
   the third iterate. Hence exact period 9 is impossible, answering Question 1
   negatively. This is one combined prospective result.
3. Two code paths agree: temporal 9-bit rotation/Boolean constraints and tuple
   columns using the literal eight-entry rule table. There are 31 admissible
   temporal columns and 961 pair vertices, with 1816 legal edges. Forward
   reachability from the background pair has 40 vertices, backward reachability
   has 63, intersection exactly (B,B), (B,1), (1,B). All those columns have period
   3. Both inductive invariant lists are emitted in nine-certificate.json.
4. Finite-propagation and periodic-time wrapping must be proved to bridge the
   finite graph to the actual infinite spatial automaton. A generic finite-walk
   proof alone is insufficient for acceptance. Formal work in progress.
5. Initial targeted live searches found the primary paper and derivative
   summaries only; OpenAlex returns zero citers. Neither fact certifies novelty.
   Full prior-art/subsumption and independent review remain outstanding.

No candidate acceptance, ledger credit, manuscript, or final replay yet.

Other root screening this turn: beta-content 367740 is already excluded by the
prior IMC 2024 deterministic theorem; taxicab additive refinement remains held
by unread Ghandehari–Martini 2018 body; intrinsic-volume 369313 has no proved
new deduction. None is credited or silently re-opened as qualified.

## Decisive prior-art update

Primary public predecessor: Korea Superintelligence Labs, *Periods of the
reversible second-order cellular automaton RESOCA 115*, version 1,
https://ideosphere.ai/papers/caperiods-v1.pdf, public source snapshot
2026-08-30 15:34 UTC; ledger snapshot 2026-09-07, commit 801848d7.
Actual theorem bodies read: Theorem 6.2 proves no finite period 9,18,21,24;
Theorem 6.4 proves every 9-periodic state is 3-periodic with no finiteness
restriction. Theorem 6.8 answers squaring negatively. Their graph proof is
the same mechanism, not merely a title/abstract overlap. Therefore the newly
reconstructed 9 obstruction is a rediscovery and MUST NOT be counted.
Their use of native_decide for finite checks does not create novelty for our
standard-axioms certificate; formal-system strengthening is not a discovery.

Two support modules compiled: ColumnCertificate (including finite exhaustive
certificates; first successful compile had two cosmetic warnings) and
SpatialRigidity (clean). A later memory-limited replay failed at 4GB;
16GB-limited compilation succeeded. No source-automaton endpoint was completed
prior to the exclusion. No full formal PASS or manuscript is claimed.

The same predecessor proves an even-k splitting theorem and gives only
conditional all-k period formulas (Theorems 5.5/5.6); those formulas are not
recorded as resolved by this exclusion. Their structural lemmas, finite values,
no-period results and parity-kick mechanism are public prior art.
