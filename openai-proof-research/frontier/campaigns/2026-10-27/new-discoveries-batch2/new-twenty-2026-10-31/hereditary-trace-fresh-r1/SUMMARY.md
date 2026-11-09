# Research handback: 321318 and 321413

**Zero accepted solutions. Strongest survivor: 321413, with an exact degree-seven deformation route toward refuting the universal minimality assertion.** This is partial work, not a completed literal Lean result. No ledger, git state, other lane, browser tab or public service was changed.

- **321318 (Borg):** Restored Conjecture 3.1 and all empty/equal-family conventions. Taking every A_i equal to one intersecting A recovers the unrestricted Chvatal conjecture. Live primary bodies now prove Chvatal and stronger weighted/flow/projection statements in September 2026; a Palomar-registered Lean formalization also exists. Those results defeat a claim of new Chvatal progress but were not shown here to imply the exact cross-sum inequality. The precise remaining quantitative inequality is in BORG-ASSESSMENT.md. No casual compression proof was attempted or accepted.
- **321413 (Hoge):** Restored the actual formal trace algebra, invariant specialization, CE, admissible reduction algorithm, fixed word-tuples, and universal quantifier. The relevant ideal is ker(pi restricted to CE), **not ker(R)** as the cached record suggests. Lemma 2.8 proves genericity; Theorem 4.1 and Section 5 prove the presentation for a chosen reduction, not for all choices.

For 321413, exact rational calculation in multidegree (3,2,2) finds a decomposable trace identity q outside the lower-degree fundamental-identity span. Polarizing q gives a legal candidate direction Q for the degree-seven reduction. Its effect on the first displayed tuple is

    Delta = -72 q  modulo products of degree<=6 fundamental identities.

A separate exact QQ matrix check gives ranks 104, 105, 104 for L, (L,q), (L,Delta+72q). Thus a concrete nonconstant direction has been found; this goes beyond the failed genericity and arbitrary-retraction shortcuts. TRACE-ATTEMPT.md explains how the direction could annihilate the first chosen relation and exactly which quotient/interpretation bridges remain to be proved. It does not label those bridges proved or replace them with assumptions in Lean.

Files:

- results.json: keyed dispositions, actual depth, zero credit and missing formal endpoint.
- TRACE-ATTEMPT.md and BORG-ASSESSMENT.md: statements, quantifiers, arguments and limits.
- trace_degree7.py: bounded rational generation, with a 50-second alarm on the quotient/deformation stage; observed total runtime below one second.
- trace-exact-polynomials.json: explicit q and its fundamental-identity certificate, Q, Delta and all 243 lower-product polynomials; exact data separate from commentary.
- verify_exact.py and exact-verification.json: independent SymPy QQ rank verification. No numerical evidence is used.
- source-provenance.json: successful/failed HTTP receipts, exact URLs, UTC dates, SHA256 and saved bodies.
- prior-checks.json: live registry heads, read depth, chronology, access gaps and historical reconciliation.

Current OpenAI math head: 4eaee87548250b2682affda7d05d947c05554bae (2026-10-30). Palomar queries succeeded at revision 651, release ff01fa2bd3240170cedf26fba4b146111e3b132a8c11fe533e5cea0a9fe75287. The preserved Chvatal formalization is c46f715af9d400523eb0d4c9c0d2335abbdc9fdd; the live source head is c19ed3aaac9e42d446f963a862d39d8a09eddbf9. Inspected source bodies and their precise depth are recorded, not inferred from search snippets.

Hoge's 2010 thesis was publicly retrieved from its university repository, and its reduction definitions/algorithm were compared. The 2012 published article PDF returned 403; no bypass or repeat attempt was made. Published-body comparison and stronger same-object trace-theory prior-art clearance remain open. The source-file and registry screens are bounded and are not exhaustive novelty claims.

**Formal/replay status:** no Lean theorem, axiom audit, or clean Lean replay. The finite rational calculation is reproducible, but does not prove the literal MathDB negation by itself. Acceptance requires proving all source-specific bridges and finite certificates in Lean, independent fidelity/significance reviews, and a clean strict replay. No next lead is initiated: 321413 still has the concrete surviving route above.
