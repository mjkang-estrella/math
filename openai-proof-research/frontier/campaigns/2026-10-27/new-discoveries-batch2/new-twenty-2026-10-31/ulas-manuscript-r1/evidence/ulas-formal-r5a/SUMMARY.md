# Round 5A even implementation handoff

EvenInitialization and EvenFormula are proved unconditionally, without proof placeholders, in UlasEven5Invariant.lean. Exactly ONE of the six original endpoint Props closed: EvenFormula. The five odd Props remain open in this packet. Root decides acceptance; no acceptance or credit is claimed.

The new proof supplies the Pell factorization, identifies its polynomial with the actual initial series transfer, proves the Chebyshev coefficient formula, derives the needed Kummer bound, and establishes the full invariant for rho + reduced (2*k) rho at level 3 + 2 nu2(k). The frozen round-4 evenFormula_of_initialization completes the literal universal even formula, including nonzero differences.

UlasEven5Final.lean contains full_theorem, mathdb_342364 and conj61_some conditional ONLY on OddOneBound, OddThreeBound, OddOneEquality, OddThreeEquality and FifteenBound. It does not import parallel lane 5B or presume its results.

All 21 round-4 modules are byte-identical to the supplied archive and original sources, with before/after hashes recorded. Six new modules use UlasEven5 names: Pell, Coefficients, Kummer, Invariant, Final, and Audit. There are 27 source modules in total.

Validation completed:

- Fresh extracted strict serial rebuild, Lean 4.34.1 with -j1 -M3500 -DwarningAsError=true, and leanchecker on all 27 modules.
- Eight declaration-audit shards. The audited set equals the full endpoint import closure: 3,667 modules and 350,168 declarations, including generated declarations and opaque values.
- LOCAL: 556 declarations; unsafe, partial, added axiom, _unsafe_rec, implemented_by and extern counts are all zero. Every LOCAL transitive axiom set is contained in propext, Classical.choice and Quot.sound. The two unconditional even endpoints use exactly those three allowed axioms.
- Upstream metadata is reported separately in results.json: 349,612 declarations. Upstream implementation metadata and unrelated upstream axioms are inventoried; none enters the LOCAL proof dependencies beyond the three allowed axioms. No upstream truth audit is claimed.
- Independent exact Python regression: 4,096 rho coefficients and 512 actual generating-series differences.
- Five negative controls rejected with type mismatch: false even +2 formula, unconditional full refutation without odd hypotheses, incorrect rho constant, equality asserted for colour 15 under FifteenBound, and wrong colour convention.
- Safe archive paths and exact archive/replay source and script equality checked. Full unique build, checker, audit, regression and negative-control logs are under fresh-replay/logs. Development logs are under logs.

No child agents, git operations, network access, uploads, external messages, browser tabs or shared ledger edits were used. Writes and temporary/build/cache paths stayed inside this lane. Every heavy invocation was serial and capped at two CPUs, 120 CPU seconds, 140 wall seconds and monitored RSS about 6 GiB. No background job remains.

See PROOF.md, REMAINING.md, NEXT-ROUND.md, STATEMENT-CORRESPONDENCE.md, REPRODUCE.md, results.json and ulas-source.zip. The full MathDB endpoint remains conditional until the odd lane is integrated and verified by root.
