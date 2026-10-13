# I288 primary-literature comparison

Research conducted across 2026-10-12–13. **Contribution TECHNICAL; priority UNRESOLVED.** Sources below were read at the stated theorem/proof extents, rather than only through the I285 abstracts. No external theorem is imported as a GAD tree-coercivity premise. Complete external bodies were fetched transiently for extraction/hashing; no full paper or whole external section is a deliverable. Exact response-body and extracted-text SHA256s are in the authentication JSON. No verbatim external excerpts are retained.

## Parity quotients

[Gopalan, O'Donnell, Servedio, Shpilka and Wimmer, Testing Fourier Dimensionality and Sparsity, author-hosted preprint](https://www.cs.tau.ac.il/~shpilka/publications/GOSSW09.pdf). Read Definition 1.1, Section 5 completely (Definition 5.1, Fact 5.2, Theorem 5.3, Lemmas 5.4 and 5.7–5.9 with proofs), and the supporting Propositions 2.9–2.10 with proofs. Extents in the authenticated pdftotext extraction: lines 83–110, 313–377, 588–737; the last range includes the beginning of Section 6 only.

This is the closest inspected structural precedent: a small Fourier-dimensional subspace means dependence on a small parity quotient; translation invariance characterizes that quotient. The tester's soundness proves concentration on a low-dimensional spectrum, then rounds to a Boolean quotient function. It does not use biased amplitudes, a coordinate witness core or a GAD channel. I288's two-representative column-type reduction is an independent elementary derivation, not a theorem attributed to this paper.

## Individual-variable juntas

[Atici and Servedio, Quantum Algorithms for Learning and Testing Juntas, arXiv:0707.3479v1](https://arxiv.org/html/0707.3479v1). Read the Fourier definitions, Lemma II.1, Fact II.2, sampling-oracle definitions, Theorem III.3 and its complete proof. Normalized extraction lines 325–545; this also includes Observation III.4 and the start, not the completion, of Theorem III.5's proof. No full-paper read is claimed.

Theorem III.3 tests individual-variable k-juntas through O(k/epsilon) Fourier samples. The proof uses escape of Fourier mass from any proposed variable set and an expected waiting-time bound. The distinction from parity dependence matters: an arbitrary-support parity has rank one but can involve n physical sites. This theorem does not imply the target and is not the strongest priority comparator here.

## Product states and product phases

[Harrow and Montanaro, Testing product states, quantum Merlin-Arthur games and tensor optimisation, arXiv:1001.0017v6](https://arxiv.org/html/1001.0017v6). Read Theorem 1's statement; Appendix A's Lemma 17 and Theorem 18 with proofs; Appendix B through the complete product-test proof (Lemmas 2, 20–22 and Theorems 3–4); Section 7's Protocol 3 and Theorem 19; Appendix F's Lemma 24 and Theorem 19 with proofs. Normalized extraction lines 1288–1522, 1213–1265, 1713–1748, plus the web-displayed Theorem 1.

Theorem 19 gives soundness for product-unitary testing in normalized Hilbert–Schmidt overlap. Its diagonal-qubit specialization supplies a uniform product-phase comparator, as derived in I288. This is a different test and weight from Q*. The depolarizing-purity identity in Lemma 17 is channel-specific and supplies no GAD transfer.

## Finite character consistency

[Oono and Yoshida, Testing Properties of Functions on Finite Groups, arXiv:1509.00930v1](https://arxiv.org/html/1509.00930v1). Read introduction/model definitions and Section 4 completely: Theorem 4.1, Algorithm 2, Lemmas 4.2–4.4 and 4.6, Corollary 4.5, including proofs. Normalized extraction lines 1–121 and 475–560. Earlier nonabelian harmonic-analysis preliminaries were not read in full; this theorem is a comparator, not an imported premise.

The complex unit-disk homomorphism test uses multiplicative consistency and Fourier coefficients. On an elementary binary group, a nonzero unit-modulus character has sign-valued generators. This is relevant precedent for the relator/sign step, but does not assert I285's finite coordinate selection or Q payment.

## Output-entropy stability and actual GAD literature

[Bae, Gour, Lee, Park and Sanders, Stability theorem of depolarizing channels for the minimal output quantum Rényi entropies, arXiv:1510.07815v1](https://arxiv.org/html/1510.07815v1). Read Section II definitions, Theorem 2's statement, Lemma 5 with its proof, the von Neumann-entropy remark (44)–(45), and Theorem 6 with proof. Normalized extraction lines 107–201 and 294–454. Theorem 2's proof and all intervening auxiliary proofs were not read in this review. The inspected argument uses a closest-product Taylor expansion and weight-one exclusion. Its channel and remainder quantifiers cannot simply be substituted for I285's GAD assertion; no criticism here is a claimed refutation of the paper.

[Khatri, Sharma and Wilde, Information-theoretic aspects of the generalized amplitude damping channel, arXiv:1903.07747v2](https://arxiv.org/pdf/1903.07747v2). Read title/version/abstract and the selected Section VI passages covering (126)–(128), Proposition 5 and its displayed proof, and the beginning of the following capacity-bound discussion. Authenticated PDF extraction lines 1–65 and 917–1022. The two-column extraction interleaves formulas; no omitted optimization or Appendix D proof is claimed read. These are capacity/unital minimum-output precedents, not a correlated-phase entropy-deficit stability theorem.

## Stipulated family 276 and companion coverage

The pinned source is [OpenAI, Classical capacity and entropy inequalities for generalized amplitude damping, paper wrapper](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Classical-capacity-and-entropy-inequalities-for-generalized-amplitude-damping-September-24-2026/build/paper.tex). Read lines 1–275, including `eq:channel`, `eq:v-main`, `thm:main`, and `cor:partner-additivity`. Complete companion sections read: [output](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Classical-capacity-and-entropy-inequalities-for-generalized-amplitude-damping-September-24-2026/build/sections/output.tex), [thermal](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Classical-capacity-and-entropy-inequalities-for-generalized-amplitude-damping-September-24-2026/build/sections/thermal.tex), [partners](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Classical-capacity-and-entropy-inequalities-for-generalized-amplitude-damping-September-24-2026/build/sections/partners.tex), and [special](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Classical-capacity-and-entropy-inequalities-for-generalized-amplitude-damping-September-24-2026/build/sections/special.tex). Principal labels are `lem:partner-branch`, `eq:recursion`, `thm:thermal`, `eq:thermal-table`, `eq:thermal-factors`, `eq:minimum-output-value`, and `cor:unital`. Companion coverage concerns these sections of the actual family-276 manuscript, not a claim to have read every source mentioned by its bibliography.

They provide the channel, branch recursion, endpoint mixture, minimum value and attaining latitude. No bounded-parity phase stability theorem was identified in these inspected passages; this is a scoped observation, not a worldwide priority statement. Fresh raw responses match retained I273 bytes and exact tree blob IDs.

## Search boundary

Four bounded multi-query web calls sought parity/linear juntas and Fourier dimensionality, product-phase/unitary testing, low-complexity phase rigidity, finite character testing, and GAD output-entropy stability. Search leads were used to select primary papers. Generic phase-rigidity queries produced much irrelevant material; snippets and secondary aggregators are not proof evidence. Recent junta and phase-state-learning hits were leads only and were not audited. No result is inferred from search absence. The screen improves materially on I285's two abstracts but does not certify worldwide novelty or an exact published duplicate.
