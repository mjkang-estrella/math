# I17 six-point spherical Ramsey theorem — final significance and prior-art review R3

**Verdict: TECHNICAL ONLY under this project's substantial, nonroutine-contribution standard. Preserve R2's full proof PASS, without repairs.** The six-point theorem is a useful exact threshold consequence beyond the supplied paper's stated five-point corollary. I found no exact full-scope literature duplicate. The reason for demotion is a concrete reduction: the necessary six-point certificate is the product of two elementary three-point bilinear interpolants, each obtained by the same adjugate lifting and scalar normalization already used in the source. Once the stipulated classification is granted, this construction needs no new local-ring lifting theorem or Ramsey forcing mechanism.

This verdict does **not** mean that short proofs are unimportant, that the theorem is false, or that its statement already appears in the classification. It distinguishes a meaningful new consequence from the nonroutine new bridge required for the ten-finding project. It is neither DUPLICATE nor GAP. No finding number or count change is assigned.

Review date: 2026-10-09. All applicable proofs at **openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb** are assumed true. Worldwide priority remains unverified. The user resumed the target of ten; historical pauses do not control this review. Four accepted findings were supplied in the brief. No agents, candidate edits, shared-index edits, staging, commits, or pushes were performed.

## 1. Exact object and acceptance standard

I read the complete 367-line discovery report, complete 232-line R2 report, original discovery and proof task JSONs and briefs, AGENTS.md, TEN-FINDINGS.md, frontier/README.md, the I16 checkpoint, and the complete I07 and I14 significance demotions. Frozen identities:

- Discovery: SHA-256 `87b86401ed5c1d554715c78fa203e33acb0117fd8255357e495a882842c0feb8`.
- R2: SHA-256 `7c5dd819e5ffccd4b48b1db631c66e62fea5d0931af8b78b2ef62978416e5118`.
- Complete inventory: SHA-256 `eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b`.

The mathematical scope is unchanged: for every nonempty finite set A of at most six distinct points in any finite-dimensional real Euclidean space, A is Ramsey if and only if A is spherical. For every spherical such A and every integer r≥2, some finite D, depending on A and r, forces a monochromatic congruent copy under **every** map R^D→{1,…,r}. All original distances are preserved. The statement includes algebraically dependent coordinates. Singleton conventions are those explicitly recorded in R2. There is no effective or uniform D, measurable-coloring restriction, subtransitive embedding, or canonical Ramsey assertion. With the known/source-relative seven-point negative, seven is the minimum size of a spherical non-Ramsey set.

The applicable standard is stronger than correctness plus an apparently unstated conclusion. The frozen frontier index requires a substantive construction, estimate, or structural lemma beyond a standard transfer from the strongest supplied results. I07 retained proof PASS but demoted the higher-rank theorem after reducing it to cyclic-cover machinery and finite replication; its stronger exact cover classification was still assessed separately. I14 retained proof PASS and found no exact full-scope duplicate, but demoted the result after reducing the changed local input to published estimates and the global construction to the supplied source. Those are the appropriate precedents: inspect what remains after the **strongest proof interface**, not merely the advertised theorem statement, is available.

I16 correctly left the positive tensor lift unproved. Its warnings about fraction-field rank, finite-jet sufficiency, and numerical specialization of entire coordinate fields remain valid. I17 and R2 close that mathematical issue exactly. An earlier unclosed project gap does not by itself establish a substantial new mechanism.

## 2. Complete corpus screen and the actual source

I traversed `sources/preprints-tree.json`, not the truncated root tree: **13,223 entries, 10,373 blobs, 749 manuscript directories, truncated:false**. I independently recomputed byte lengths, SHA-256 and Git blob identities for **all 9,340 text files** in the read-only I14 cache against its manifest and the complete pinned tree. Total text bytes: **141,349,121**. The cache was not modified.

The retained searches normalize whitespace and cover Euclidean Ramsey configurations; six/circle/concyclic/spherical/hexagon contexts; seven/heptagon negative contexts; and bilinear, bidegree, fractional-linear, Möbius, adjugate, interpolation and tensor contexts. The relevant Euclidean-configuration matches are confined to the classification manuscript. Broad algebraic matches also occur in unrelated tensor, determinant, representation, and geometry papers; their occurrence is not a hidden Ramsey corollary. The full patterns, paths, snippets and verified dependency hashes are in [corpus-audit.json](../sources/i17_six_point_ramsey_novelty_r3/corpus-audit.json). This is full-inventory text coverage, **not** a claim to have mathematically read all 749 manuscripts. Absence of phrase matches does not establish novelty.

The decisive manuscript is [A classification of finite Euclidean Ramsey configurations](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-classification-of-finite-Euclidean-Ramsey-configurations-September-23-2026). I read the entire introduction and consequences, the tensor-equivalence/descent interface, the completion of sufficiency, and the bibliography. Exact source statement blocks are frozen and reverified, including:

1. [01-introduction.tex, `thm:classification`, lines 74–88](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-classification-of-finite-Euclidean-Ramsey-configurations-September-23-2026/build/sections/01-introduction.tex). For distinct points affinely spanning R^d, let p_i=(1,a_i), let F be their coordinate field, and B=F⊗_Q F. Ramseyness is equivalent to a matrix P over B satisfying `(p_i⊗1)^T P(1⊗p_i)=0` and multiplied spatial block I_d. No separate multiplied constant-row constraint or matrix symmetry is required. Lines 3–8 fix arbitrary colorings and original-scale congruence.
2. [02-tensors.tex, `alg:equivalence`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-classification-of-finite-Euclidean-Ramsey-configurations-September-23-2026/build/sections/02-tensors.tex). Its proof supplies tensor flip-transpose symmetrization and coefficient descent. It does not assume B is a domain. These clarify the precise interface; the positive certificate below is already defined over the required field.
3. [07-consequences.tex, `cons:spherical` and `cons:quadratic`](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-classification-of-finite-Euclidean-Ramsey-configurations-September-23-2026/build/sections/07-consequences.tex). Spherical necessity includes the singleton case. The positive proposition requires independence of the ordinary quadratic-evaluation rows over F. Its proof uses `z=(det M)b−ι adj(M)Db`, then divides by the **left scalar** `m(det M)`, not by det M in B. Thus the critical adjugate/zero-divisor-safe normalization method is expressly supplied, not an invention of I17.
4. Same consequences file, `cons:quadrilateral`, lines 106–109 and proof: the actual general small-circle result is **at most five**, proved by products of two affine line equations and independent quadratic rows. Six circle rows have rank five, so that proposition does not apply directly to all six.
5. Same file, `cons:transitive`, `cons:kites`, `cons:nine`, and `cons:twelve`: subtransitive sets are already Ramsey; certain non-subtransitive cyclic kites are already Ramsey; generic nine circle points and a twelve-point derivation configuration are already negative examples. None is the six-point theorem. The source itself acknowledges the earlier seven-point literature.
6. [06-groups.tex, final sufficiency proof, lines 345–358](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-classification-of-finite-Euclidean-Ramsey-configurations-September-23-2026/build/sections/06-groups.tex) supplies qualitative finite-dimensional forcing from the exact certificate. This work contributes no replacement for that deep part of the classification.

The newly retrieved GitHub `commits/main` response identifies **the same pinned commit**. Therefore there is no later classification revision at that current branch in this retrieval. This is a dated observation about the retrieved branch, not an assertion about every branch or unpublished revision.

## 3. The decisive elementary reduction

R2 Section 5 must govern the significance comparison. The long, valid residual-Jacobian proof cannot be used to make the remaining contribution appear harder than its fully established polynomial alternative.

Take six distinct t_i in the actual characteristic-zero coefficient field F and independent U_i. For a triple I define, in F[U],

\[
M_I=((t_i,1,-t_iU_i))_{i\in I},\quad D_I=\det M_I,
\quad (N_a,N_b,N_c)^T=\operatorname{adj}(M_I)(U_i)_{i\in I},
\]
\[
G_I(x,y)=(N_cx+D_I)y-N_ax-N_b.
\]

The adjugate identity gives `t_i N_a+N_b−t_i U_i N_c=D_I U_i`, hence **G_I(t_i,U_i)=0 polynomially** for all three labels. At U=t, the determinant is the nonzero scalar `V_I=∏_(i<j in I)(t_j−t_i)`, and the numerator vector is `(V_I,0,0)`. Consequently

\[
G_I(t;x,y)=V_I(y-x).
\]

For I={1,2,3} and I'={4,5,6},

\[
Q(x,y)=\frac{G_I(x,y)G_{I'}(x,y)}{V_IV_{I'}}
\in F[U_1,\ldots,U_6][x,y]
\]

has bidegree at most (2,2), kills all six evaluations, and specializes coefficientwise to `(y−x)^2`. Only the nonzero **F-scalar** V_IV_I' is inverted. Map coefficients through `a↦a⊗1`, `U_i↦1⊗t_i`. The resulting coefficient matrix K satisfies all six tensor equations and `m(K)=J_0`, where

\[
J_0=\begin{pmatrix}0&0&1\\0&-2&0\\1&0&0\end{pmatrix}.
\]

There is no inversion of D_I, D_I', or any mixed tensor element. Arbitrary algebraic dependencies and zero divisors therefore require no additional theorem: polynomial identities survive any ring homomorphism, and a nonzero left field element is a unit.

For clarity about why this is a standard use of the supplied algebraic interface: restrict the source's adjugate lifting argument to the four-dimensional bilinear space `span{1,x,y,xy}` and a triple. On the diagonal its evaluation matrix has rows `(1,t_i,t_i,t_i²)`, rank three. The target `y−x` lies in its diagonal kernel. The source's kernel-correction formula thus lifts this target using a 3×3 minor. G_I/V_I is the explicit formula. Multiplying the two lifted linear diagonal factors lifts their square. The extra observation is the factorization of the desired circle relation and the partition into two triples, rather than trying to make the rank-deficient six-row map surjective.

This is **not** an application of `cons:quadratic` to the six original circle points, nor an assertion that a union of two Ramsey triangles is Ramsey. The multiplication occurs in a bivariate certificate ring, and degrees add correctly. Nor does the argument multiply classification matrices and assume spatial blocks are preserved. Taking coefficients after polynomial multiplication is the specified operation.

The conversion to the source's geometric criterion is explicit. Normalize to a unit circle avoiding the stereographic pole, put `q(t)=(1,t,t²)^T`, and use

\[
p(t)=\frac{Lq(t)}{1+t^2},\qquad
L=\begin{pmatrix}1&0&1\\1&0&-1\\0&2&0\end{pmatrix},\qquad
L^T\operatorname{diag}(-1,1,1)L=-2J_0.
\]

Then `P=−2L^(−T)KL^(−1)` has multiplied matrix `diag(−1,1,1)` and vanishing tensor evaluations. This is precisely the classification input. Pulling a coloring back by the fixed scale restores all original distances, with no regularity assumption. These are coordinate and scalar transformations, not additional forcing results.

All other affine dimensions follow by the already reviewed support argument. A quadratic-row relation on m points of affine dimension e gives a nondegenerate weighted diagonal form with an isotropic affine-evaluation space of dimension e+1, hence `2e+2≤m≤6`. Sphericity excludes e≤1; only six coplanar circle points remain. Otherwise `cons:quadratic` applies. Spherical necessity is imported. Seven-point sharpness is known and also has R2's independent source-relative obstruction. **Neither the support argument nor negative sharpness is a separate contribution.**

## 4. Why the exact threshold does not overturn the reduction

The strongest case for ACCEPT deserves acknowledgment. This settles an actual universal boundary, not only generic coordinates, a numerical sample, or one special hexagon. It crosses a rank drop where the source's stated five-point proof stops. Together with the seven-point counterexample it determines a clean minimum cardinality. The exact polynomial certificate remains useful mathematical documentation; no retrieved source stated it. A good short proof of a sharp result can certainly be publishable or significant.

That case does not establish this project's more specific gate. After accepting the entire classification, the remaining operation is a fixed pair of full-rank three-point adjugate lifts and multiplication of the resulting bilinear factors. The source already supplies the lifting method, including scalar normalization safe for zero divisors. The circle's rational parametrization is also already used in the source's negative example, and the target double diagonal was explicitly identified in I16. The product construction needs no new invariant, estimate, extension theorem, or obstruction analysis. The only choice beyond those interfaces is the elementary factor-and-partition observation.

I do **not** claim that arbitrary six-equation lifting is automatic from dimension count. It is not: the whole point is to display the special factorization that makes it automatic here. I also do not dismiss the algebraic-dependence quantifier. Its preservation is exact, but follows immediately from constructing the identity before tensor specialization. The author performed a correct, longer local-ring construction for something the source's elementary lifting method can supply in two smaller pieces.

Under a broader criterion of “previously unstated sharp consequence with a correct proof,” this is a strong candidate to retain. Under the supplied criterion requiring a **substantial nonroutine bridge beyond all pinned results**, I judge the residual observation a technical application. This is consistent with I07 and I14: meaningful strengthened conclusions did not receive new substantial slots when their supposed new mechanism reduced to finite assembly or an elementary modification of available machinery. The reason is the reduction, not proof length, the number six, unverified priority, or a need to keep the count low.

## 5. Fresh primary-literature comparison

I downloaded current arXiv abstract pages and full HTML manuscripts for eight relevant papers. Exact retrieved bytes, SHA-256, UTC retrieval times, final URLs, text conversions and metadata are retained in [literature/manifest.json](../sources/i17_six_point_ramsey_novelty_r3/literature/manifest.json). The retrieved headers identify the versions below. The 134 extracted theorem/lemma/etc. blocks are a **statement inventory**, not a claim to have proof-audited every block. The decisive statements and selected proofs were read directly.

**Pálvölgyi, A cyclic non-Ramsey heptagon, arXiv:2609.23327v1, 20 September 2026.** The current metadata lists only v1. Theorem 1 gives the non-Ramsey circle set `{(0,0)} ∪ {(j,±sqrt(j(2r−j))):j∈{1,3,4}}` for transcendental r>2. I read its full proof. This negative boundary is prior art. [Primary manuscript](https://arxiv.org/html/2609.23327v1).

The appendix, explicitly unverified by its author, does not establish six-point Ramseyness. A.2 excludes nonzero fixed weighted first-derivative energy identities for ≤6 circle points; A.4 reduces symmetric combinations of first derivations to one; A.11 extends the limitation to small spherical supports using the same isotropic dimension bound. A.15 treats quadratic finite iterates of one derivation. A.16 treats polynomial potentials of degree ≥3 in their highest derivative variable. A.17 restricts colorings to algebraic-translation invariance and configurations to all but one point algebraic. These restrictions prevent any from supplying the arbitrary-coloring positive theorem. A.3 already states a generic seven-point negative result. No unchecked appendix assertion is a premise here; exact contracts preserve their hypotheses. [Appendix](https://arxiv.org/html/2609.23327v1).

**Moore, A pyramid with a Ramsey base is Ramsey, arXiv:2608.09649v1, 10 August 2026; Mirabi, One-point extensions of Euclidean Ramsey sets, arXiv:2608.11736v1, 12 August 2026.** Moore Theorem 1.2 and Mirabi Theorems 1.1/3.2 require the added point outside the base's affine hull (equivalently nonzero new height). They do not adjoin a sixth point to five points in the same circle. Congruence preserves the affine dependence, so raising the ambient dimension does not remove that hypothesis. These are genuine nearby positive theorems, not duplicates or shortcuts for the planar exception. [Moore](https://arxiv.org/html/2608.09649v1), [Mirabi](https://arxiv.org/html/2608.11736v1).

**Ivan–Leader–Walters, Generalised Prisms and Euclidean Ramsey Theory, arXiv:2606.13472v1, 11 June 2026.** Theorem 1 assumes a common finite group acting transitively on the two bases, with nonzero separating height; solubility gives the Ramsey conclusion. Corollary 4 is the corresponding off-hyperplane pyramid statement. Corollary 5 uses regular polygons. These symmetry and height hypotheses do not cover arbitrary six circle points. [Primary manuscript](https://arxiv.org/html/2606.13472v1).

**Behague, Nearly all known Euclidean Ramsey sets are subsoluble, arXiv:2510.15677v3, 4 December 2025.** Theorems 1.5–1.6 cover specified permutation configurations, most regular polytopes, and isosceles trapezia through subsoluble extensions. Their scope does not say every spherical configuration of a given small size is subsoluble. [Primary v3](https://arxiv.org/html/2510.15677v3).

**Leader–Russell–Walters, Transitive Sets and Cyclic Quadrilaterals, arXiv:1012.5468v1, 25 December 2010; Eberhard, Almost all sets of d+2 points on the (d−1)-sphere are not subtransitive, arXiv:1212.1803v1, 8 December 2012.** The former's Theorem 1 and Corollary 2 exclude transitive embeddings for specified cyclic quadrilaterals; the latter excludes even affine subtransitivity generically. Thus one cannot reduce the positive six-point theorem to all sets being subtransitive. These are not non-Ramseyness theorems: the stipulated classification already separates the two properties. [LRW](https://arxiv.org/html/1012.5468v1), [Eberhard](https://arxiv.org/html/1212.1803v1).

**Pálvölgyi, A nearcircumsphere-Ramsey theorem for solvable transitive configurations, arXiv:2608.10865v2, 3 September 2026.** Theorem 2 assumes a solvable group acting transitively and gives a copy on a sphere of every prescribed radius strictly above the circumradius. Corollary 3 handles regular polygons. This stronger host-sphere conclusion for a restricted class does not imply the arbitrary six-point statement. [Primary v2](https://arxiv.org/html/2608.10865v2).

Searches also explicitly tested six-point/six points/concyclic/hexagon and spherical Ramsey phrasing, heptagon comparisons, and interpolation terminology. Many broad search results were irrelevant graph-edge-coloring or geometric-concyclicity hits; those were rejected, not treated as evidence. The retained query records are `search-01.json` through `search-05.json`. The first unretained exploratory batch is not part of the reproducible search evidence. The bounded search found no exact duplicate; it cannot certify worldwide priority, unpublished work, or unindexed formulations. Most importantly, **search absence supplies no reason for the technical-only verdict**: Section 3 does.

## 6. MathDB and problem-priority limits

The frozen frontier standard also asks for an exact MathDB problem and an observed ranking or featured designation. No exact six-point entry or such designation was established. This requirement remains unmet; no score is invented.

The current indexed [one-point extension entry](https://mathdb.com/p/375277/the-one-point-extension-conjecture-for-euclidean-ramsey-sets) explicitly requires an apex outside the old hyperplane. Its “open” label cannot replace the primary Moore/Mirabi theorem statements, and its problem is not the circle boundary. The indexed [transitive-set conjecture entry](https://mathdb.com/p/371018/leader-russell-walters-transitive-set-conjecture-for-euclide) likewise is not a new problem solved by I17: the supplied classification's kite consequence already refutes its necessity direction. Search snapshots are retained in `search-05.json`; they are database metadata, not mathematical authorities.

The six-point result has an intelligible relationship to the historical spherical characterization problem: it supplies the last universal cardinality before known spherical counterexamples. That is its genuine significance. It does not solve the full spherical conjecture anew, prove subtransitivity, establish canonical/diameter Ramsey conclusions, or acquire a verified MathDB ranking through association with a famous problem. The metadata limitation is additional to, and not a substitute for, the mathematical contribution assessment.

## 7. Validation, freeze, and concurrent drift

R2's proof PASS is retained in full. I did not rerun the six R2 proof-audit scripts already reproduced by the parent. I instead verified their sealed bytes and ran a fresh diagnostic of the **specific significance reduction**: two adjugate identities, triple evaluation identities, both diagonal specializations, bilinear degrees, six product evaluations, product specialization, bidegree (2,2), and the circle congruence. All **12 check groups** pass with all twelve t/U parameters formal. This is exact polynomial arithmetic; it is neither a finite sample nor finite-jet sufficiency evidence. The human-readable adjugate argument in Section 3 establishes why it works.

The provenance verification passes for **50 frozen input files, 9 actual classification statement contracts, 16 retained author primary contracts, 134 freshly extracted primary statement blocks, 17 fresh retrievals, the 146-artifact discovery seal, the 174-artifact R2 seal, and all 9,340 corpus text files**. The 17 retrievals are eight abstract pages, eight full primary HTML texts and one current GitHub commit response. These counts distinguish provenance coverage from mathematical reading.

Concurrent shared-index edits occurred. At the recorded verification, `frontier/README.md` changed from SHA-256 `45f5ed73c508dff90abd30d000c8385aa1cec60b195d81e154a7e2a02ae5e2a4` to `4a5a3dd3483108a91075f71794d594a5e661c2c90fd9ea6cea9ee588466f4677`; TEN-FINDINGS.md changed from `adb8d4f584a7bfeeeabb521d517c561d1c698cfa37f5c803f5a897e73968adb8` to `1fad6655a3aadae9d05e4d6a4a870da2bbf8c762d35ad25f1ab25fdd06d560df`. The frozen versions control this audit; live drift is recorded separately in [provenance-verification.json](../sources/i17_six_point_ramsey_novelty_r3/provenance-verification.json). The candidate, R2, rules and pinned mathematical dependencies did not drift. Parent task-status updates are not changes to a theorem premise.

Reproduce from the project root:

```sh
python frontier/experiments/i17_six_point_ramsey_novelty_r3/reduction_check.py
python frontier/experiments/i17_six_point_ramsey_novelty_r3/verify_provenance.py
python frontier/experiments/i17_six_point_ramsey_novelty_r3/seal.py --verify
```

`corpus_audit.py` reproduces the complete verified text screen; `primary_contracts.py` rebuilds the statement inventory from retained HTML. `fetch_primary.py` makes fresh network requests and changes retrieval timestamps, so it is **not** a retained-snapshot verification command. The two pure-Python symbolic wheels are read-only R2 dependencies with hashes in the reduction output and external-dependency seal. No global environment was changed. The seal covers this report, scripts, snapshots, raw captures, search logs, contracts and outputs, and separately verifies external read-only dependencies. Its own manifest and derived seal-verification output are the only excluded files.

**Final disposition: TECHNICAL ONLY; full proof PASS preserved; no exact duplicate established; no new mathematical gap; worldwide priority and exact MathDB ranking unverified.** Retain the six-point theorem and the short polynomial certificate as a correct source-relative threshold consequence. The longer local-ring proof should remain accurately labeled a valid alternative proof, never the basis for overstating the amount of new mechanism.
