# Solo adversarial review and disposition

## Finding

**Viable mathematical candidate, not yet eligible for acceptance:** a full finite-dimensional proof of Banica–Nechita Conjecture 6.6 (MathDB 332493), in fact without the two rank-balance assumptions. See `proof.md`. This is one potential outcome, not one per rank or helper. It is unrelated to the accepted first-batch C*-counterexample families: the conclusion is a universal canonical projection-trace inequality, not another example or parameter of their constructions.

The author of this lane has checked the following attacks. This is a self-review, NOT the required independent review.

## Mathematical checks and strongest objections

- **Wrong orthogonalization?** Resolved mathematically by the reduced-SVD appendix: the polar frame U is exactly `(P+R)^{†/2}[p r]`, with zero action on the ambient orthogonal complement. We do not replace the source normalization by Gram–Schmidt or by arbitrary orthogonal projections.
- **Noncommuting functional calculus?** No commuting of G and H is used. They act on different column-coordinate spaces. The identity JGJ=2I−G justifies `J sqrt(G)=sqrt(2I−G) J` by unitary conjugation. Independent eigenbases are used on the left and right of K.
- **A missing sign or factor?** Source right side equals `|| (K+JKL)/2 ||²_HS`, giving factor 1/4. Summing the two contraction bounds gives factor 2. The Gram-defect traces equal twice the source left side. These factors cancel correctly. The entry relation has a plus sign: u*k+v*l=0.
- **Row bounds but not column bounds?** Both are needed and available. K=U*V and K*=V*U are contractions; JKL is also contractive. The Lean spectral core explicitly requires and uses all four collections of bounds.
- **Hidden equal-rank assumption?** None. E and F may have different column counts; the argument and formal core are rectangular. Zero ranks are treated by empty sums or a direct zero conclusion.
- **False scalar lemma?** The coefficient inequality and complex entry inequality have actual kernel proofs under `a²<1,b²<1`. The sum bound is also compiled. There are no numerical constants to exactify.
- **Does this solve general quantum Sinkhorn convergence?** No. It proves the two-column/two-row projection inequality only. Conjectures 5.6, 5.7, 6.5 for general N/p and later general convergence questions are not claimed solved.

Independent numerical implementation of the source matrices and of every proof identity was run on 100 random complex configurations over five rank patterns, including unequal and zero ranks. Identity residuals were at most 4.4e-15 with Gram minimum eigenvalues ≥0.107 in the nontrivial sampled cases. Tiny negative scalar residuals around 1e-31 occurred only in theoretically zero modes. These are diagnostics, not proof. The exact scalar/core Lean proof is independent of these floats.

## Source and bounded prior-art review

- Actual latest arXiv primary source 1602.04456v3 refetched, hash `82ea37c2f43e0f2940ce190891306a08881d05149e98a0e743bbb48be5950fd1`. Read Conjecture 6.6, all six assumptions, definition of all four primed projections, and the S=0 Proposition 6.7. The source does not contain this full proof.
- Publisher version DOI 10.1016/j.aam.2016.09.001 is identified, but the publisher full body returned 403. The author research page links only that DOI and arXiv. This is a material unclosed source-comparison limit, not permission to claim the printed version identical.
- Actual Nechita–Schmidt–Weber 1911.04912v1 Section 3 Lemma 3.1 and Conjecture 3.2 read. It gives the standard square polar orthogonalization fact and leaves generic convergence conjectural. It does not provide the present trace inequality in the inspected section/full-text keyword screen.
- Actual Benoist–Nechita 1608.05811v2 Appendix A Proposition A.1 and its proof inspected: positive-definite block Sinkhorn termination from determinant monotonicity. Its strictly positive blocks and conclusion differ; it does not imply monotonicity of the prescribed quadratic projection potential by the argument given there.
- Actual Weber 2023 published HTML, DOI 10.1007/s11785-023-01335-x, Section 3.4 Problem 3.13 read: still asks convergence. This is contextual evidence only; unresolved general convergence does NOT prove unresolved 6.6.
- Actual de la Salle 2103.14126v2 Theorems 1.1/1.2 read: existence of a nearby PVM with 9ε error, not the specific source polar normalization or sharp four-projection trace comparison. No direct subsumption established. An initial wrong arXiv-id download was recognized as unrelated atomic physics and explicitly excluded in the retrieval log.
- Actual Brannan–Chirvasitu–Freslon published 2020 body, Section 4, Conjecture 4.3 and Corollary 4.9 inspected: resolves inner-faithfulness cases of source Conjecture 5.7, not Conjecture 6.6. Avoid conflating these.
- Additional actual primary PDFs 2510.15586, 2304.09124, 1906.10409 retrieved, titles/introductions and relevant keyword passages screened: hypercube/magic-isometry completion; concrete S4 model polynomial separation; inverse-limit quantum permutation models. No target trace result located. These were relevance screens, not line-by-line proofs of every theorem in those papers.
- Live Semantic Scholar source citation query returned 26 records, including the relevant successors above. Database coverage is incomplete; not all 26 were fully read. Live exact-name/conjecture/id and polar-orthogonalization queries found no posted proof/refutation. Numerical IDs produce many irrelevant results, so absence from those searches is weak evidence.
- Source MathDB live record has no solutions, but this was not used as novelty proof. All URLs, content hashes and access records are in `../sources/retrievals.json` and `../provenance.json`.

No earlier full resolution or immediately subsuming endpoint was found in this bounded review. This is not a worldwide priority guarantee; published-source comparison, broader matrix-analysis prior art, and independent novelty review remain open.

## Formal and acceptance disposition

Eight declarations across two modules compile strictly with the required absolute Lean 4.34.1 binary and pinned mathlib. Only propext, Classical.choice, Quot.sound occur. They establish the entire scalar/finite-array part. **The literal source projection theorem is not yet formalized.** `lean-plan.md` identifies the missing frame, pseudoinverse, spectral and HS bridges and the exact target. Mathematical proofs of these bridges are included in `proof.md`; no unproved bridge was smuggled into an accepted formal endpoint.

Current disposition: retain as the lane's strongest genuine lead, suitable for independent mathematical review and dedicated literal formalization. Credit requested: 0 at this stage. Root alone can accept/count after completing every gate.

## Other lead disposition

372905: previous public refutation means no new credit for p=2.5; prior blowup is a diagnosed optimizer artifact. No further time invested.
352327: exact p=12/23 source statement and source propagation read. Prior saved Pi progress preserved. The alternating-equality Hessian has no negative direction in the tested endpoint even cases, and the off-diagonal entry Hessian reduces to a scalar weight average. No global proof/refutation claimed; untouched unresolved alternative if the projection candidate fails.
