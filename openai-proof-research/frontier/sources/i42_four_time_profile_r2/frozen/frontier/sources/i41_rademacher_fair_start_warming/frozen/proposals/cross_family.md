> Archived exploratory draft. Some claims were corrected, rejected, or left unreviewed. Use [the final index](../README.md) and [screening decisions](../SCREENING.md) for accepted results.

# Cross-family synthesis

Research date: 2026-10-08. Upstream theorems are accepted as true. Revision: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` (`sources/upstream.json`, commit date 2026-10-08T05:20:00Z). Statements below were read from the cached TeX of that revision under `sources/cache/cross_family/`. `sources/tree.json` is truncated and contains no preprint TeX; paths were taken from `sources/preprints-tree.json`, whose recorded tree SHA is `df0564b2deaab87e07854b6344d8c2f037682e77`. No shared index was edited.

This lane asks for a consequence of at least two catalogue families that the catalogue does not already state. One such theorem is proved. Two further candidates were developed and then stopped: one is only partly matched, and one is circular.

| Rank | Proposed result | Families | Assessment |
|---|---|---|---|
| 1 | Good minimal models for globally strongly Q-factorial compact Kähler klt fourfolds with pseudo-effective actual adjoint | 033, 034, 056 | Proved by discharging the three hypotheses of the October 6 conditional theorem. |
| 2 | Simultaneous Artin lower bound for any fixed finite set of prime bases | 029, with a Poisson–Dirichlet input inside 029 | Not proved. Three of four inputs match; the marked Type II input was not fully compared, and the packaging is mostly internal to one family. |
| — | All-dimension Kähler log abundance, then applied to the fourfold nef endpoint | 033, 034 | Rejected as a proof of rank 1. The abundance manuscript cites lemmas from the conditional fourfold paper. |

No computational check is attached. The proved statement is birational, and a numerical sample would not be a proof.

## 1. Unconditional good minimal models

### Statement

Let \(X\) be a normal connected compact Kähler fourfold, and let \(B\) be an effective rational Weil divisor. Suppose that \((X,B)\) is klt, that the actual adjoint \(D=K_X+B\) is \(\mathbb Q\)-Cartier and analytically pseudo-effective, and that \(X\) is globally strongly \(\mathbb Q\)-factorial: every coherent rank-one reflexive sheaf on \(X\) has an invertible positive reflexive power. Then there exist a normal connected globally strongly \(\mathbb Q\)-factorial compact Kähler fourfold \(Y\) and a bimeromorphic map \(\phi:X\dashrightarrow Y\) such that:

1. \(\phi\) extracts no prime divisor, and \(B_Y=\phi_*B\).
2. \((Y,B_Y)\) is klt, and \(D_Y=K_Y+B_Y\) is \(\mathbb Q\)-Cartier and analytically nef.
3. \(a(E;Y,B_Y)\ge a(E;X,B)\) for every prime divisor over the two models, with strict inequality for every prime on \(X\) contracted by \(\phi\).
4. For some integer \(m>0\), depending on the pair, \(\mathcal O_Y(mD_Y)\) is globally generated.

In particular, if such an adjoint is already analytically nef, then \(\kappa(X,D)\ge 0\). Zero boundary, smooth fourfolds, and every numerical dimension are included. Global strong \(\mathbb Q\)-factoriality is a condition on sheaves on all of \(X\). It does not require analytic \(\mathbb Q\)-factoriality of every open subset.

### Source theorems

Pinned blob URLs use the revision above.

**Conditional theorem, family 034.** [Conditional good minimal models, introduction](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Conditional-good-minimal-models-for-compact-Kahler-fourfolds-October-6-2026/build/sections/introduction.tex), Theorem `thm:main`, and [premises](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Conditional-good-minimal-models-for-compact-Kahler-fourfolds-October-6-2026/build/sections/premises.tex). PDF: [paper.pdf](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Conditional-good-minimal-models-for-compact-Kahler-fourfolds-October-6-2026/paper.pdf).

Theorem `thm:main` is the statement above, under Assumptions `hyp:campana`, `hyp:mmp`, and `hyp:effective-abundance`. Theorem `thm:nonvanishing` is the nef nonvanishing clause, under the same three assumptions, for an ordinary klt pair on a normal connected globally strongly \(\mathbb Q\)-factorial compact Kähler fourfold. The introduction says that the projective abundance argument used inside the proof is contained in the appendices, and that Lemma `red:log-iitaka` derives that argument’s logarithmic-Iitaka premise from `hyp:campana`. The projective branch therefore adds no further premise. The manuscript says that `hyp:mmp` gives neither a first plurisection nor semiampleness.

The catalogue still states this theorem as conditional (`sources/CONTENTS.md`, family 034, the October 6 conditional entry).

**Orbifold subadditivity, family 033.** [Introduction](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Orbifold-and-logarithmic-Iitaka-subadditivity-September-26-2026/build/sections/introduction.tex), Theorem `main:orbifold`. PDF: [paper.pdf](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Orbifold-and-logarithmic-Iitaka-subadditivity-September-26-2026/paper.pdf).

Let \(X\) be a smooth compact connected manifold in Fujiki class \(\mathcal C\), let \(\Delta\) be a rational SNC boundary, and let \(f:X\to Y\) be a surjective holomorphic map with connected fibers onto a normal compact irreducible complex space. For a very general smooth fiber \(F\),
\[
\kappa(X,K_X+\Delta)\ge\kappa(F,K_F+\Delta|_F)+\kappa(f\mid\Delta).
\]
A rational SNC boundary means coefficients in \(\mathbb Q\cap[0,1]\), including coefficient one. The invariant \(\kappa(f\mid\Delta)\) is the infimum of \(\kappa(Y',K_{Y'}+B(f',\Delta'))\) over the orbifold-morphism equivalence defined in that section. The inf-multiplicity divisor \(B(f,\Delta)\) is the same formula as `eq:orbifold-base` in the conditional premises.

**Abundance after nonvanishing, family 034.** [Introduction](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Abundance-after-nonvanishing-for-compact-Kahler-fourfolds-September-27-2026/build/sections/introduction.tex), Theorem `thm:main`. PDF: [paper.pdf](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Abundance-after-nonvanishing-for-compact-Kahler-fourfolds-September-27-2026/paper.pdf). Dated September 27, 2026.

Let \(X\) be a normal connected compact Kähler complex space of dimension four, and let \(\Delta\) be an effective rational Weil divisor such that \((X,\Delta)\) is klt and the actual adjoint \(D=K_X+\Delta\) is \(\mathbb Q\)-Cartier. If \(D\) is analytically nef and \(\kappa(X,D)\ge 0\), then some positive Cartier multiple is globally generated. If \(\kappa=0\), a positive multiple may be taken to be the trivial line bundle. Nonvanishing is a hypothesis. Projectivity and \(\mathbb Q\)-factoriality are not hypotheses.

**Finite ordinary MMP, family 056.** [Finite ordinary minimal model programs, October 6, 2026](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Finite-ordinary-minimal-model-programs-on-compact-Kahler-fourfolds-October-6-2026/paper.pdf). The relevant labels are in [03-steps.tex](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Finite-ordinary-minimal-model-programs-on-compact-Kahler-fourfolds-October-6-2026/build/sections/03-steps.tex) and [06-perturbation.tex](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Finite-ordinary-minimal-model-programs-on-compact-Kahler-fourfolds-October-6-2026/build/sections/06-perturbation.tex). The preamble puts theorem, proposition, lemma, corollary, hypothesis, definition, convention, and remark on one counter, numbered within sections. Files `01-introduction` through `07-endpoints` each contain one `\section`, in that input order, so `03-steps` is Section 3 and `06-perturbation` is Section 6.

- Lemma `lem:absolute-support` is Lemma 3.2. On an ordinary rational klt pair whose boundary is \(\mathbb Q\)-Cartier and whose adjoint is a rational line bundle, every adjoint-negative extremal ray \(R\) admits a nonempty relatively open set of nef classes \(\alpha\) with \(\overline{\mathrm{NA}}\cap\alpha^\perp=R\) and \(\alpha-c_1(D)\) Kähler.
- Proposition `prop:ordinary-step` is Proposition 3.4. In dimension at most four, in the global Weil \(\mathbb Q\)-factorial category with canonical sheaf a rational line bundle, every negative extremal ray has a projective contraction to a normal compact Kähler space, of relative line-bundle rank one, with \(-D\) relatively ample and \(f^*\mathrm{BC}(Z)=R^\perp\). A divisorial step pushes the pair forward. A small step has locally finitely generated canonical algebra, and the flip is its relative analytic Proj, with a sufficiently divisible tautological bundle equal to the transformed adjoint. Strong global \(\mathbb Q\)-factoriality is preserved when imposed. No prime is extracted. Log discrepancies weakly increase, strictly for every original prime contracted by the step.
- Proposition `repair:prop:supporting-contraction` is Proposition 6.23. For every negative extremal ray and every Kähler-margin supporting class \(\alpha\), there is a projective contraction and a Kähler class \(\gamma\) with \(\alpha=f^*\gamma\), so \(\overline{\mathrm{NA}}\cap(f^*\gamma)^\perp=R\), and \(-D\) is relatively ample. The count is: 24 shared-counter environments in Section 6, of which two are remarks, placed fifth and ninth; Supporting contractions is environment 23 and Finite ordinary programs is environment 24. The conditional bibliography’s “Proposition 6.23” and “Theorem 6.24” therefore match these labels. In Section 3 the only remark follows Proposition 3.4, so Lemma 3.2 and Proposition 3.4 are unshifted.
- Theorem `repair:thm:reduction` is Theorem 6.24, and the text says that its conclusions imply Theorem `thm:finite`. Every maximal ordinary negative-ray program on a rational klt pair on a normal globally Weil \(\mathbb Q\)-factorial compact Kähler fourfold starts on that fourfold and terminates. Strong \(\mathbb Q\)-factoriality is preserved when imposed. If the adjoint is pseudo-effective, the endpoint is nef, the composite extracts no divisor, and discrepancies do not decrease, strictly increasing for every prime on the original fourfold that is contracted. The proof records that positive-current pullback preserves pseudo-effectivity. The canonical datum may be a specified Weil divisor or the intrinsic canonical rational line bundle.

Definition `def:strong` in the conditional premises is the same strong clause as Definition `def:strong-factoriality` in the MMP introduction: every coherent rank-one reflexive sheaf has an invertible positive reflexive power. The MMP paper states that this implies global Weil \(\mathbb Q\)-factoriality. The conditional premises use that implication explicitly.

### Proof

The conditional Theorem `thm:main` becomes unconditional once its three assumptions are theorems in the stated category. Each identification is by the text above. The conditional proof is not reopened.

**`hyp:campana`.** The displayed inequality, the coefficient range \(\mathbb Q\cap[0,1]\), Fujiki class \(\mathcal C\), connected fibers, very general smooth fibers, and the inf-multiplicity definition of \(\kappa(f\mid\Delta)\) are Theorem `main:orbifold` together with the definitions preceding it. The conditional hypothesis also includes existence of neat models and the identity `eq:neat-formula`, equating the invariant to \(\kappa(S,K_S+B(g,\Gamma))\) on a neat model. The orbifold manuscript, [models.tex](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Orbifold-and-logarithmic-Iitaka-subadditivity-September-26-2026/build/sections/models.tex), attributes that identity to Campana, Definition 3.8, Proposition 3.10, Corollary 4.11, and Remark 6.2, and says that its own proof uses only the inequality \(\kappa(T,K_T+B)\ge\kappa(g\mid\Gamma)\) on allowed smooth models. The same classical package is what the conditional hypothesis writes into its definitional preamble before identifying the displayed inequality with Theorem 1.1 of the orbifold paper. The OpenAI input is that inequality. The neat-model identity remains the cited classical statement, already part of the hypothesis as written.

The conditional text says that `hyp:mmp` is independent of `hyp:campana`. The sentence “Assume `hyp:campana`” at the start of `hyp:mmp` is therefore not an extra premise beyond the orbifold theorem.

**`hyp:effective-abundance`.** The September 27 theorem has the same objects, the same klt and actual \(\mathbb Q\)-Cartier hypotheses, the same analytic-nef and nonnegative-Iitaka hypotheses, and the same global-generation conclusion. It does not need strong \(\mathbb Q\)-factoriality. Its additional \(\kappa=0\) trivialization is not required. The conditional premises identify this assumption with that Theorem 1.1.

**`hyp:mmp`.** Restrict Theorem 6.24, Proposition 6.23, Proposition 3.4, and Lemma 3.2 to a globally strongly \(\mathbb Q\)-factorial starting fourfold whose actual adjoint is analytically pseudo-effective. Strong factoriality supplies the Weil condition and the canonical rational line bundle used by those statements, as the conditional premises say. Lemma 3.2 supplies a Kähler-margin support for every negative ray. Proposition 6.23 realizes that support as \(f^*\gamma\). Proposition 3.4 supplies projectivity, relative ampleness, the divisorial pushforward, the relative-Proj description of the flip, local finite generation, the tautological bundle, preservation of strong factoriality and klt singularities, and the prohibition on extracting a prime. Theorem 6.24 supplies termination for every choice of negative rays, the nef endpoint, preservation of analytic pseudo-effectivity, and the discrepancy inequalities. The program starts on \(X\). This is the list in `hyp:mmp`.

Apply Theorem `thm:main`. The nef model produced by `hyp:mmp` satisfies (i)–(iii). Theorem `thm:nonvanishing` supplies \(\kappa\ge 0\) on that endpoint, and `hyp:effective-abundance` supplies a globally generated multiple. Both steps are inside the conditional theorem once the three assumptions hold, so both conclusions are unconditional in this category.

### Dependency check

The September 26 orbifold bibliography and the September 27 abundance bibliography do not cite the October 6 conditional paper. The conditional bibliography cites those two papers and the October 6 MMP paper; it does not cite the all-dimension Kähler log-abundance manuscript. The MMP bibliography does not cite the conditional paper. Its termination argument uses Corollary `repair:cor:existing` and the October 7 companion on termination of generalized log-canonical flips. The MMP introduction says that this companion uses low-place, relative-program, extraction, and special-termination results proved in the MMP paper, and that the supporting-contraction argument does not use the finite-program theorem. The companion’s own bibliography was not opened.

### Novelty

New relative to this catalogue: family 034 states the fourfold good-minimal-model theorem only under the three assumptions, and states separately the all-dimension Kähler log-abundance theorem under logarithmic Iitaka subadditivity. The unconditional fourfold statement is not an entry.

Literature status, from the manuscripts’ own prior-work sections and one search: Höring–Peternell, arXiv:1304.4013, prove minimal models for non-uniruled compact Kähler threefolds. Their survey arXiv:1701.01653 records good minimal models for terminal \(\mathbb Q\)-factorial compact Kähler threefolds not covered by rational curves, records the projective minimal-model theorem for varieties of general type, and asks whether the Kähler MMP works in general. The October 6 MMP manuscript cites Das–Hacon–Păun for the compact klt result in which the adjoint is already \(\mathbb Q\)-linearly equivalent to an effective divisor. The September 27 abundance manuscript cites Höring–Lazić–Lehn, Theorem 4.1, for semiampleness of nef klt adjoints through dimension four when the Iitaka dimension is positive, and treats Iitaka dimension zero itself under a nonvanishing hypothesis. Those results do not state the pseudo-effective good-minimal-model theorem for a general globally strongly \(\mathbb Q\)-factorial compact Kähler klt fourfold. This is a new-to-project deduction from the pinned manuscripts. It is not a certified first appearance in the literature; the external search was limited to those sources.

### Open gaps

- The multiple \(m\) is pair-dependent. No bound is claimed.
- The adjoint must be klt, effective and rational, actual and \(\mathbb Q\)-Cartier, and analytically pseudo-effective, on a globally strongly \(\mathbb Q\)-factorial compact Kähler fourfold. Log-canonical pairs, non-effective boundaries, and other dimensions are outside the statement. If the adjoint is not pseudo-effective, Theorem 6.24 ends at a Mori fibre space, and no good model is claimed.
- The neat-model identity is Campana’s, cited in common by the orbifold paper and the conditional hypothesis. It is not an OpenAI theorem.
- Theorem `thm:nonvanishing` assumes all three hypotheses, including abundance after nonvanishing. This deduction does not separate nonvanishing from that hypothesis.
- Internal proofs were not re-audited. The October 7 flip companion was not opened. An October 5 conditional manuscript exists in the tree; the text used here is the October 6 manuscript.
- There is no effective algorithm and no numerical certificate.

## 2. Simultaneous primitive roots, not discharged

Family 029 lists [Simultaneous primitive roots](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Simultaneous-primitive-roots-a-conditional-lower-bound-for-prime-bases-October-4-2026/build/sections/01-introduction.tex), Theorem `thm:main`, as conditional on four inputs. The conclusion is: for distinct positive primes \(q_1,\ldots,q_k\) there is \(c_q>0\) such that, for large \(x\), at least \(c_q x/(\log x)^2\) primes in \((x,2x)\) have every \(q_i\) as a primitive root.

Inputs `input:hecke`, `input:block`, and `input:density` match, respectively, Theorem `thm:hecke-zero-free` and Lemmas `lem:block` and `lem:density` of [Primitive roots for every admissible integer base](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/paper.pdf). The block and density lemmas are the first and second theorem-like environments of `11-sieve.tex`. Their section number was not re-counted across every preceding file. Input `input:marked` asks for a coefficient criterion and a rough Type II bound, and the simultaneous text points to Lemma 10.2 and Proposition 10.3 of that companion. The file `08-type-ii.tex` contains Theorem `thm:marked-type-ii` and Lemma `lem:marked-coefficient-transfer` with the same shape of parameters. Those two statements were not compared line by line with `input:marked`, and the section index of `08-type-ii.tex` was not established. The simultaneous theorem is therefore not claimed.

Even a complete match would be a same-family packaging, together with the Poisson–Dirichlet estimate cited inside the primitive-root construction. It is weaker as a cross-family deduction than the fourfold theorem.

## Rejected combinations

**All-dimension Kähler abundance plus the fourfold MMP.** [Log abundance under logarithmic Iitaka subadditivity](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Log-abundance-for-compact-Kahler-spaces-under-logarithmic-Iitaka-subadditivity-October-6-2026/build/sections/01-introduction.tex), Theorem `thm:main`, assumes `asm:log-iitaka`. That assumption is Corollary `spec:logarithmic` of the orbifold paper, including the projective reduced-SNC case. Nefness in the MMP paper is membership in the closure of the Kähler cone, which is the abundance paper’s analytic nefness. The resulting shortcut would turn a pseudo-effective fourfold into a good model. It is not used. In `03-programs.tex` the abundance manuscript imports Lemmas 7.2–7.9, 7.16, and 7.17 of the conditional fourfold paper (`CB`). Feeding that abundance theorem back into the conditional theorem is not an independent discharge. Family 034 already records the abundance theorem as the consequence of logarithmic Iitaka subadditivity, so that theorem is not restated here.

**Special fourfold abelianity.** Family 057 already says that the abelianity theorem yields virtual abelianity for the stated order-two root orbifold of a smooth projective complex fourfold. The conditional half-weight manuscript assumes the companion theorem and repeats that consequence.

**Density-one full Birch–Swinnerton-Dyer.** Family 002 already combines the low-corank formula with Goldfeld’s density theorem.

**Deterministic factoring, and polynomial differences at prime arguments.** The catalogue entries for those algorithms already name the Hecke zero-free theorem and the quasi-Riemann hypothesis as inputs.

**A Dirichlet half-plane \(\operatorname{Re}s>1-10^{-6}\) from the primitive-root Hecke theorem.** Family 003 already gives every Dirichlet \(L\)-function, including \(\zeta(s)\), the stronger zero-free half-plane \(\operatorname{Re}s>7/8\). The factorization of \(\zeta_{\mathbb Q(\zeta_m)}\) through Dirichlet \(L\)-functions does not improve that entry. The same half-plane does not improve Linnik’s constant. The Hecke theorem remains the source of a \(1-10^{-6}\) region for finite-order Hecke \(L\)-functions of cyclotomic fields containing \(\mu_{12}\), which is the statement already in family 029; \(\mathbb Q(\sqrt{-3})\) does not contain \(\mu_{12}\), so family 003 does not replace it.

**Class VII shells and Oka K3 surfaces.** The two manuscripts are a conjunction of classification statements, not a deduced theorem beyond either one.

## Scope of the search

The catalogue headings through the Kähler, abelianity, primitive-root, Birch–Swinnerton-Dyer, quasi-Riemann, and factoring blocks were compared with the combinations above. Withdrawn Weil, Kuga–Satake, and Hodge-for-K3-product manuscripts were not used. Companion papers were checked before a conditional statement was treated as open: the three hypotheses of the fourfold theorem match the three source manuscripts, and the combinations already spelled out in `CONTENTS.md` were excluded.
