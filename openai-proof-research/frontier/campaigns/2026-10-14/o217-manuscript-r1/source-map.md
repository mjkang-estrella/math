# O217 manuscript proof and source map

The exact original scope and mathematical candidate remain frozen under their external anchors. Manuscript main.tex has no added moment, symmetry, identical-law, temperature-window or tail hypothesis. Its Theorem1.1 is the integrated finite-size result; Corollary1.3 is the conditional consequence, not a second contribution.

| Manuscript interface | Exact basis and scope |
|---|---|
| Equation(1), Gaussian input Proposition1.2 | Pinned217 limiting-law introduction, eq:model and thm:main. Independent standard Gaussians, off-diagonal unordered edges, counting-spin prior, zero field, fixed beta>1. |
| Positive exact variance prefactor | Same thm:moments and completed-pressure definition; independent completion variance beta²/2. Reduction red:prop-moments removes it and uses exact finite-size standardization. |
| Exponent-only companion boundary | Pinned217 scale introduction thm:main supplies n^(1/3+o(1)), not the exact law or prefactor. |
| Lemma2.1, equations(8)–(10) | Full finite Gibbs cumulant partition formula and multivariate chain rule reproduced. Repeated edges allowed; constants uniform in a,c and individual laws. Classical bounded-spin derivative machinery credited. |
| Equations(11)–(14) | Spin-coordinate bijection proves deterministic gauge; derivative sign before deleting edge; product-law reflected-star Taylor comparison is reproduced in full. No random common gauge or law symmetry assumed. |
| Equation(15), mean and smooth-test endings | Full outer coordinate Taylor comparison and exact powers m q⁴, mn q⁶. Classical Lindeberg ancestry credited to Carmona–Hu/Chatterjee; CLSX Prop3.2 is the close matched-third comparator. |
| Section4.1 | Finite hybrid family includes original/reflected/Gaussian coordinate laws. Growth ensures M finite before bootstrap. Restoration is unconditional and uses at most two independently restored coordinates. |
| Section4.2 | Exact square identity and Taylor remainder use fourth moments only. Author-side parent variance assistance credited; no separate contribution. |
| Section4.3 | Full D_e³D_f³(H²) double-binomial product formula; two undifferentiated-H terms; integrable cubic/fourth inner remainder independent of twice-deleted base. |
| Section4.4 | Uniform square comparison, finite maximum quadratic inequality, and exact own-mean variance correction. No circular intermediate variance premise. |
| Section5 | Characteristic functions using bounded sine/cosine tests, Levy continuity, variance ratio and Slutsky. Full sequence and arbitrary triangular arrays, with eventual positivity only. |
| Section1 attribution | EYY1007.4652v4 end6.1 and Lemmas6.5–6.6: anomalously small expected cubic term via row/minor expansion plus local law. Conceptual precedent credited; SK reflected-product gauge implementation distinguished. |
| Section6/formal-support.tex | Human proof versus scoped formal support. The sealed support proves concrete gauge/cubic oddness and scoped scalar algebra; Section6 lists probability/analysis/source-limit omissions. Independent formal audit PASS_SCOPED_SUPPORT adopted with no repairs; no full formalization claimed. |

Source pin: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Exact pinned source URLs and labels are in the PDF bibliography and input receipts. Upstream truth is stipulated, not audited. No third-party bodies are bundled here.

## Exact scoped formal interface

The authoritative inventory is the authenticated sibling o217-formal-v1/coverage.json: 28 theorems, 43 public support declarations (definitions and instances included). Exact types and axiom reports are in that packet's validation/sealed-build/types-axioms.stdout. The following links are semantic mappings, not claims that the full manuscript lemmas are formalized.

| Manuscript interface | Lean declarations and actual boundary |
|---|---|
| Concrete model, gauge and cubic sign | Edge, flipSpinEquiv, hamiltonian_flip, partitionSum_pos/flip, logPartition_flip, logFam_contDiff/flipStar, thirdDerivLog_flipStar_odd and thirdDerivObservable_flipStar_odd. Canonical Fin n pairs i<j correspond to manuscript labels by adding one. q enters the exponential; counting prior/zero field agree. General observable oddness uses total derivatives and supplies no C6 or quantitative bound. |
| Square identity and bound | square_taylor_identity, square_remainder_bound, square_taylor_remainder_H. Exact algebra and fourth-power scalar bound are proved from explicit pointwise quadratic/cubic/quartic remainder hypotheses, not from a formal Taylor theorem or random-variable integrability result. |
| Quadratic bootstrap | sqrt_add_le, quadratic_bootstrap: M,V,C nonnegative and M <= V+C sqrt(M)+C imply sqrt(M) <= sqrt(V)+C+sqrt(C). The finite hybrid maximum and this premise are derived only in the human proof. |
| Mean correction | bootstrap_variance, centered_variance, centered_variance_from_bootstrap. These are scalar inequalities in supplied numbers; no probability variance identity or expectation has been encoded. |
| Size cancellations | edge_card/edge_card_bound, mq4_le, mnq6_le use the actual finite edge cardinality and q=beta/sqrt(n), with n>0 in the real-valued estimates. |

Entirely outside the formal packet: product probability laws/reflection, moment matching and moment inequalities, uniform Gibbs cumulants and all mixed derivative/chain-rule bounds, Taylor's theorem supplying remainder bounds, both Lindeberg telescopes, conditional expectations and integrability, unconditional deleted-coordinate restoration, construction/finiteness of the hybrid maximum, actual random-variable centering identity, stipulated Gaussian law/prefactor and all-integer Levy/Slutsky transfer. Compilation and byte authentication do not establish those human arguments.
