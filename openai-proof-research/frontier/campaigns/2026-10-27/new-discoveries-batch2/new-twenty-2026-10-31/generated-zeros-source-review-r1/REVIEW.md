# Independent review: MathDB 358323

Reviewer recommendation: **mathematics PASS; literal source/endpoint fidelity PASS; discovery-credit significance FAIL (routine classical-theorem adaptation)**. Root alone adjudicates acceptance. This reviewer awards zero credit; campaign remains 4/20 beyond 39. No known earlier explicit public refutation was located. The significance objection below is a concrete subsumption bridge, not an assertion of worldwide priority or a rejection because the proof is short.

## Inputs and scope

Read project, second-batch and current-campaign AGENTS.md, administrative ledger/context, author SUMMARY.md, PROOF.md, exact ID-keyed results.json entry, raw/358323.jsonl, Taylor.lean, source receipts, history reports and registry refresh/screen. frozen-before.json verifies all **115/115** manifest bindings before substantive review, without mismatch. frozen-after.json records the final check. Original files were never edited. The assignment is source/math/prior-art/significance review, not the separate full Lean replay/axiom audit. No Lean command was run; reported author replay and 31-declaration audits are not independently re-certified here. Prebuilt upstream dependency cache trust remains explicit.

Primary bodies read: Chung, arXiv:2305.05130v1, Definitions 37–41 printed pp.92–93, Theorem 42 pp.93–94, conclusions and Conjecture 47 pp.118–119; Sokal cond-mat/0012369v3 Theorem 1.5 printed pp.7–8 and Lemma 3.8 statement/proof pp.22–23; Chung–Tran arXiv:2304.12444 Theorems 1–3, Section 2 partial-fraction body and Remark 4; Brown–Otto arXiv:2008.01784 Theorems 1.1/2.1 and the discussion of repeated characteristic roots. This is selected-body coverage, not a claim to audit every proof of these papers.

## Fidelity and mathematical assessment

Conjecture 47 is a universal assertion for nonzero real a,b,c with b²−4ac≤0. Its generating identity starts at m=0 and is exactly 1/((at²+bt+c)(1−tz)). Both quadratic roots have the same modulus in the strict-negative-discriminant case; choosing either as t₁ is allowed. There is no genericity, irrational-angle, nonresonance, excluded origin or deleted finite-root-set condition in the conjecture. Its displayed target is a subset of C. Definitions 37–41 explicitly define zero sets in an open connected domain, upper and lower neighborhood set limits, and their common limit when equal. C is a valid domain here; the global displayed conclusion supplies no domain that omits 0.

Definition 38 requires each neighborhood to meet infinitely many indexed zero sets; Definition 39 requires eventually every indexed zero set to meet it. These agree exactly with Taylor.lean's Upper/Lower ball quantifiers (changing finite initial indices or > versus ≥ does not matter). Definition 41 requires both to coincide with the proposed circle. These are ordinary set limits, not normalized zero-counting measures or just the support of a limiting measure. The text's informal distribution language and its computer experiments do not override its explicit definition. No wording correction is needed to obtain this counterexample.

For a=b=c=1, the discriminant is −3 and both roots of t²+t+1 have modulus 1. As formal series,

    1/(1+t+t²) = (1−t)/(1−t³).

Write c_n=1,−1,0 according to n mod 3. Coefficient convolution with (1−zt)⁻¹ yields

    P_m(z) = sum_{j=0}^m c_(m−j) z^j.

This is a monic polynomial of degree m, including P_0=1; none is identically zero. In particular, this is the actual generated sequence, not an arbitrary sequence with chosen constant terms. Grouping coefficients in triples gives, for every k≥0,

    P_(3k+2)(z) = z(z−1) sum_{j=0}^k z^(3j).

Thus P_(3k+2)(0)=0 for an unbounded set of m. For any N take m=3N+2>N. Every positive-radius neighborhood of 0 meets that zero set. Therefore 0 belongs to the full sequence's upper limit but not the unit circle. This negates the entire universal conjecture by an admissible witness, not just a finite exceptional index. The proof does not require describing the entire replacement limit set.

Generation here produces reversed coefficient sections compared with usual Taylor partial sums in z: P_m(z)=z^m S_m(1/z), where S_m(w)=sum c_j w^j, interpreted polynomially at zero. This explains why substituting statements about ordinary sections without a reciprocal/degree bridge could miss the zero at 0. In this conjecture the generating identity fixes the convention unambiguously. Source title alone must not replace it.

Taylor.lean's F is the inverse full formal denominator, and generating/generated_witness prove its generating identity. Generated quantifies pointwise in z; with c≠0 the series denominator is invertible, so its coefficients are uniquely determined. The ordinary coefficient formula above verifies polynomiality and analyticity of this witness. The final theorem retains every real-parameter, discriminant, generation, root and minimal-modulus hypothesis and negates the universal conclusion. A function-valued representation is faithful to the literal MathDB/source statement's sequence of functions; it does not create a spurious witness. The root definition (−1/2,i√3/2), root_norm and minimal_root cover both equal-modulus roots. I found no semantic defect in this endpoint. Full kernel/transitive-audit validation remains the separate audit task.

Independent finite rational/symbolic checks are reproducible with diagnostics.py (15 exact coefficient/factor/degree checks). They supplement the universal algebraic derivation, not certify it by sampling. No claim against weak normalized zero-counting-measure convergence follows: one persistent zero among degrees tending to infinity has vanishing normalized mass.

## Decisive significance objection: Sokal applies after periodic splitting

The author's direct-application objection is correct but incomplete as a subsumption analysis. For the unsplit sequence the characteristic roots are z and the two reciprocal quadratic roots, constant unit-ratio conjugates of modulus 1. The latter dominate on |z|<1. Sokal Theorem 1.5's no-degenerate-dominance condition therefore fails there; Lemma 3.8(d),(k) explicitly uses this condition. Applying the theorem unchanged to conclude the whole disk is a limiting zero set would be invalid.

However, splitting into the residue class m=3k+2 and **combining** the coincident cubed constant roots resolves this obstruction. On the connected open disk D={|z|<1/2}, put

    A(z)=z(z−1)/(1−z³),
    f_k(z)=P_(3k+2)(z)=A(z)−A(z)z³ (z³)^k.

This identity follows from the finite geometric sum above, whose denominator has no zeros in D. Apply Sokal's actual Theorem 1.5 with

    alpha_1=A, alpha_2=−Az³, beta_1=1, beta_2=z³.

All four functions are analytic on D and none is identically zero. In particular beta_2 may vanish at an isolated point; the theorem excludes identically zero functions, not every function with a zero. The beta ratio is nonconstant, so no constant unit-multiple identity occurs. Index 1 is uniquely dominant throughout D because |z³|<1/8. At z=0, alpha_1(0)=0. **Case (a) of Theorem 1.5 therefore places 0 in both set limits of f_k.** The subsequence lower limit is contained in the full sequence upper limit by the definitions: arbitrarily large k give arbitrarily large m. Since the selected quadratic radius is 1, this refutes Conjecture 47 in its full logical scope.

This is an explicit full-scope negative bridge using a theorem published in 2004 (arXiv first version 2000), before Chung's 2023 conjecture. It requires only an admissible coefficient substitution, geometric-series extraction of one residue class, combination of identical characteristic factors, and the source's own cited theorem. No new asymptotic lemma, general resonance theorem or positive classification remains. The same calculation already proves the zero exactly, so invoking the theorem is unnecessary for correctness; it documents the concrete classical-theorem adaptation relevant to the campaign's exclusion rule. Merely observing periodicity or saying “easy” would not have supplied this bridge.

Accordingly I recommend **exclude this packet from new significant-discovery credit as a routine adaptation**, while retaining the correct source refutation and formal artifact. This is a significance/relative-novelty judgment, not evidence that a previous author printed this exact refutation. A general infinite-family theorem is neither required nor the basis of rejection. Root may contest this classification, but must address this specific subsequence/theorem bridge rather than rely solely on failure of the direct unsplit application.

## Bounded prior-art, versions and chronology

Fresh HTTP /commits/HEAD receipts at 2026-11-01T14:43:41Z and 14:43:44Z give OpenAI/math 4eaee87548250b2682affda7d05d947c05554bae and Omega/the-omega-institute/trureturing 83b70a1d0d6a58bb32521c741805d845d401c5f8. No /commits/main check was used. Response hashes equal the frozen author receipts. Reused complete, nontruncated scoped tree caches: OpenAI preprints 3f56f68a176b4494c346091ea0a319651bc217ec, Omega D5 da7b727392fb95300b19e1759d1f2bcde0b70baf and Problems 0b45ced5e033ab15556c8f7a9177458bc5ad1de6. registry-screen.json records independently computed file hashes and matches. This is scoped path screening, not all registry bodies/history.

Four pinned candidate bodies were retrieved to disambiguate name matches: Omega DebSokalConjectureFourRefutation is a Stirling-row real-root counterexample (explicitly literature-attested there), JensenPolynomialObstruction assumes Jensen/RH analytic bridges, FullSymmetryNonlocalization constructs a quartic with zeta symmetries, and OpenAI's noncoordinate zero-fibre paper concerns Abhyankar–Sathaye. The actual claim/definition/theorem sections read are unrelated to Chung's generating sequence. These are not asserted prior resolutions or reused counterparts. Other broad lexical hits are not claimed body-reviewed. No matching later public counterpart was found to require a discovery-date comparison; being publicly visible in 2026 would not alone establish priority over this project.

The fresh Chung abstract page lists only v1, submitted 9 May 2023 02:23:23 UTC, and no journal reference. The cached PDF identifies v1 and has SHA256 cfd038904f57e9f2f36a9fb8f864e367987790dbc3d04a2141aaed7cbb68f7a6, independently checked in frozen verification. No arXiv replacement or correction is visible on the inspected page. This does not exclude an unindexed thesis/journal correction elsewhere.

An independently located companion by Chung–Tran, arXiv:2304.12444 (24 April 2023; current abstract also lists only v1), has actual Theorems 1–3 requiring ac<0 or positive discriminant; Remark 4 specifically assumes unequal pole moduli and describes the major limiting curve. Its Section 2 partial fractions are related algebraic tools, not a printed full resolution of Conjecture 47. Brown–Otto 2008.01784 (2020), Theorem 2.1, extends BKW to polynomial-in-index amplitudes/repeated characteristic roots while retaining a unit-multiple exclusion. It supplies no direct unsplit resonance clearance. Neither is evidence of an already public exact negative answer.

Seven bounded web-search queries covered exact title, arXiv ID, author/conjecture number, periodic Taylor sections and degenerate BKW/root-of-unity terms; search-notes.json records queries/leads. No explicit previous Chung-47 refutation was found in inspected results. Search snippets are leads, not verified theorem bodies or exhaustive citation coverage. The bounded local screen examined 132 named reports at two fixed directory levels; history-screen.json found no exact ID/title objection there. This does not clear every historical lane or report format.

No retry or bypass was made of denied UCL Sokal, MathDB or Palomar routes. Sokal's already lawfully cached arXiv body was used. MathDB/Palomar live content, subscription indexes, exhaustive citing literature and unindexed updates remain access/coverage gaps; these do not justify inventing an unconditional novelty pass. All live body receipts preserve UTC and SHA256; no hash is invented for search snippets. HTTP source requests were one bounded request per selected lawful route. No browser, external contact, publication, git operation, child agent, shared-ledger edit or long-running job was used.

## Qualified verdicts and next actions

| Gate | Verdict | Concrete basis |
|---|---|---|
| Source and endpoint fidelity | PASS in inspected v1 scope | Explicit Definitions 37–41 and Conjecture 47; actual generating identity; no excluded parameters |
| Ordinary mathematics | PASS | Genuine monic polynomials, exact recurring zeros, origin outside required circle |
| Prior explicit public resolution | NOT FOUND, bounded | Inspected source/companion/theorem bodies and fresh scoped registries; stated access gaps remain |
| Relative novelty/subsumption | FAIL for significant-discovery nomination | Fully instantiated Sokal Theorem 1.5 after residue-class extraction and combination, with all hypotheses checked above |
| Significance | RECOMMEND EXCLUDE AS ROUTINE | Full negative bridge already available from the source's classical theorem by periodic splitting; not proof length or witness size |
| Formal replay/axiom audit | OUT OF SCOPE | Endpoint semantically inspected; no independent Lean execution here |
| Acceptance/credit | ROOT ONLY; zero awarded | Count unchanged |

Next action: root adjudicates the explicit routine-adaptation objection before further manuscript/formal investment. Preserve the packet as a correct refutation/formalization regardless of credit. If root seeks to overturn this recommendation, the precise issue is whether this fully supplied classical-theorem/residue-class bridge constitutes the campaign's excluded routine adaptation; no missing algebraic or asymptotic premise has been left implicit. A prior explicit public refutation has not been proved and must not be reported as one.
