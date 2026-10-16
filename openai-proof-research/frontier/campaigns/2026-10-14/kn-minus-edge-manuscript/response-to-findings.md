# Response to the mandatory prior findings

Section, lemma and page numbers refer to `main.pdf` (SHA-256 in `output-manifest.json`). The claim is not narrowed: Theorem A covers every n ≥ 2 and every edge; Corollary B covers every m ≥ 4 and n ≥ 1 with P_n the path with n edges.

**(1) Lemma 3.1 is sufficient only.** Lemma 3.1 states that the two missing-pair identities (3.2) imply Σ(H) = 0. Remark 3.2, "The conditions are sufficient only", says they are not necessary and gives the reviewer's example H = xy: it violates both identities, yet Σ(xy) = J̃(z_x, z_x) = 0 by skew-symmetry for every drawing. Sec. 1.2 repeats "sufficient, not necessary". No converse, characterization or "iff" statement appears anywhere in the paper or the package. R9 checks the example on random skew forms.

**(2) Proof components preserved.** All are in Sec. 3 with full proofs:
- zero extension and the tensor-kernel proof of Lemma 3.1, with U3 for the boundary;
- dimensions of S_a, S_b and S_a ∩ S_b (Lemma 3.3);
- mixed orthogonality (Lemma 3.4), including the ordered independent edge pairs T, the factor 4 from the four orientation choices, orientation-independence of a_α, and nondegeneracy of the diagonal symmetric form (it is not the skew form J);
- the twisted detector (Lemma 3.5), reduced to the rectangular nonsingularity of U4 on P_{s−1,s−2} × P_{s−2,s−1}, not its square consequence;
- injectivity on S_a and on S_b (Lemma 3.6): localization only at the 2s − 1 vertices with complete stars (the terms i = a, b are never interpreted), Lagrange isolation, degree accounting (every separate degree at most n − 2), root count 2s − 1 > 2s − 4, division by the four cross linear factors, cancellation using the nonzero polynomial C(t_a, t_b, y, v), and descent preserving S_a; S_b by the slot swap;
- small cases: s = 2 gives bound 0 (Proposition 3.7) and s = 3 is closed in the descent step;
- the dimension bound dim W_a + dim W_b ≤ |T| and its count (Proposition 3.7).
R6–R8 check finite instances of these steps.

**(3) Credit.**
- Pinned OpenAI preprint: Premises U1–U6 with labels and the commit; Table 1 shows where each enters; the abstract and Sec. 1 credit the Harary–Hill proof to it.
- Ouyang–Wang–Huang: Thms. 3.1–3.4, Cor. 5.1, Cor. 5.2, Lemma 2.3 credited in Sec. 1.1; the even case is reproduced from their Thm. 3.2 in Sec. 4 and is labelled classical.
- Chia–Lee: Lemma 1, Theorems 1–2, Corollary 1 and Conjecture 1 credited as equivalent results (Sec. 1.1); their cylindrical upper-bound construction is noted in Sec. 5.
- Zheng–Lin–Yang–Cui: credited for the upper bound, equality for n ≤ 8, cr(K_6 □ P_n) = 15n + 3, the lower bound (1.1) and both conjectures. The paper states that their text could not be obtained and that the attributions follow OWH and the CHN survey with exact locators.
- Sadhu: Sec. 1.2 calls it a preprint that appeared before this work, determining cr(K_{m,n} − e) for the bipartite family also treated by Chia–Lee, and states its stated inspiration by the bipartite OpenAI framework. Sec. 7 compares the listed passages only, says neither theorem implies the other, and claims only the specific argument for K_n − e, not the idea of adapting the framework to a deleted edge.
- No global priority claim: Sec. 7 "Limits" says the search was bounded and is not a priority certificate.
- AI assistance and the internal nature of all reviews are disclosed in the acknowledgement.

**(4) Arithmetic types and fail-closed checks.** Table 2 gives the arithmetic of each check: exact integers and rationals (R1–R5, R9), exact rational ranks (R6, R7), exact polynomial identities over Q (R8), the author checker's rationals plus floating-point straight-line geometry plus ranks mod 2^61 − 1, the author mod-p checker's NumPy arithmetic mod 2^31 − 1, and the reviewer checker's integer geometry, rationals and ranks mod 1000003. Nothing is described as all exact rational. `support/run_all.py` fails on any `FAIL` line, including `SOME FAIL` with exit 0, with a self-test. Sec. 8 says the author's invalid-test prints are not enforced negative controls and that R8 and R9 are. Sec. 8 explains that the reviewer's early failures were harness errors, not counterexamples; the logs are referenced by hash in `input-manifest.json`.

**(5) Integer division.** `support/release_checks.py` uses Python integers with `//` and `fractions.Fraction` only; there is no floating point in the file. The contribution reviewer's `gap-check.py` is not reused.

**(6) Formal status.** Sec. 9 states that no machine-checked proof of any statement of the paper exists and none is claimed, describes the intended scope of a separate effort as not implemented or audited, and separates it from the full proof in the paper. `formal-scope.json` records the same with status "pending". The formal task's directory was not read.

**(7) Originals and rights.** Inherited scripts and outputs are byte-identical copies, authenticated by hash on every run; the originals were not modified. Every input is hashed in place in `input-manifest.json`. No upstream file, publisher PDF, web extraction or survey text is in the public allowlist or ZIP; see `RIGHTS.md`.

## Changes relative to the frozen candidate

- Prose rewritten for publication; mathematics unchanged except where a review asked for clarification.
- Remark on necessity removed and replaced by Remark 3.2 (non-converse).
- Lemma numbering differs from `candidate.md`: candidate Lemmas 3.2–3.5 and Proposition 3.6 are paper Lemmas 3.3–3.6 and Proposition 3.7, because Remark 3.2 shares the counter.
- Attribution to Chia–Lee, Zheng et al., Sadhu and the bipartite OpenAI preprint made explicit, as above.
- New checks R1–R9 and a fail-closed runner added; inherited checks retained unchanged.

No new mathematical issue was found while preparing the manuscript.
