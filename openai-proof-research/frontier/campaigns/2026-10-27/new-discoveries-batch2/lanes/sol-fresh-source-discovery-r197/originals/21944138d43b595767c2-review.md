# Independent review: arithmetic ratios and permutation rigidity

Review date: 2026-10-25 (America/Los_Angeles). I read `openai-proof-research/AGENTS.md`, the complete canonical Lean files, both complete canonical papers and their `PROOF.md` files, the exact arithmetic source posts and original HTML/TeX, the rotation source HTML (including Appendix D and its surrounding argument), and Patel's posted proofs/counterexample. I independently compiled each canonical source from text and audited every local declaration. Only this assigned review file was written. No nested agents, Git commands, build writes, or local proof-object outputs were used. PDF visual QA and release integration remain the parent's responsibility.

## Verdicts and count eligibility

| Canonical outcome | Verdict | Count eligibility |
| --- | --- | --- |
| `simple-arithmetic`, MathDB 375256 | **PASS.** The exact Conjecture 3 inequality holds for every integer `n ≥ 2`, `k ≥ 1`, with the actual arithmetic functions and source right-hand side. | **One** full source outcome, as verification of a previously posted proof. |
| `mixed-arithmetic`, MathDB 375257 | **PASS.** The exact fully powered Conjecture 9 inequality holds for every integer `n ≥ 2`, `k ≥ 1`, including all three mixed denominators. | **One** different full source outcome, as verification of a previously posted proof. |
| `permutation-rigidity`, MathDB 368725 | **PASS.** The rational `1 × 3` example satisfies every source hypothesis, has diagonal stationary expression using the actual negative fractional matrix power, and is not a permutation. | **One** full source counterexample outcome, instantiating a previously posted general mechanism. |

There are **three distinct complete source-target outcomes**, if the campaign admits verified prior results. There is no mathematical or formal coverage blocker. They are **not three new resolutions of previously open problems**. The arithmetic files and joint paper are shared certificates for two separately identified source conjectures; neither their duplication across packages nor their helper lemmas earns any additional count. The rotation's smaller dimension and exclusion of signed permutations also earn no additional count. Minor documentation/provenance issues below should be repaired during integration.

## Exact artifacts and fresh Lean verification

Paths in this table are relative to `twenty-proof-campaign/outcomes/`. These are SHA-256 hashes of the canonical files actually reviewed.

| File | SHA-256 |
| --- | --- |
| `simple-arithmetic/formal/ArithmeticRatios.lean` | `63d380780dbaaeac75c7fbf24f2e4857efb31ceb4da0d30ea2292465643ddd36` |
| `simple-arithmetic/main.tex` | `32bb7871455b2ee729999de38509806aa1c4065f5b56533fc4c1c60f4521f01b` |
| `mixed-arithmetic/formal/ArithmeticRatios.lean` | `63d380780dbaaeac75c7fbf24f2e4857efb31ceb4da0d30ea2292465643ddd36` |
| `mixed-arithmetic/main.tex` | `32bb7871455b2ee729999de38509806aa1c4065f5b56533fc4c1c60f4521f01b` |
| `permutation-rigidity/formal/PermutationRigidity.lean` | `4add54f65035e1d512072d7755079f7b74e9dfce814760a1682e276588a4a23c` |
| `permutation-rigidity/main.tex` | `5b289332102c6ee1829fdff87d078756b35a58cfd7a03eecf013e8c44ca384ab` |

The arithmetic Lean files are byte-identical to each other, as are their papers. Concatenating the sibling lane's `formal/RealRatios.lean` and `formal/ArithmeticRatios.lean`, removing the latter's local import, and replacing `RealRatios` with `ArithmeticRatios` reproduces the canonical Lean text modulo whitespace. Thus the merge changes no proof or theorem statement.

For each of the three canonical files separately, I supplied the **complete file text**, followed by `#check Namespace.name` and `#print axioms Namespace.name` for every local `abbrev`, `def`, `theorem`, and `lemma`, to:

```text
/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean -DwarningAsError=true --stdin
```

The working directory was the supplied package directory, and `LEAN_PATH` contained only the existing dependency `.lake/build/lib/lean` paths under:

```text
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
```

Neither an outcome directory, a lane directory, nor a local build directory was in `LEAN_PATH`. Both sources import only `Mathlib`. No `-o` option was used, and no local `.olean` was imported or emitted. The compiler identified itself as Lean **4.34.1**, commit `5045d0056413266e57c625dcd7c365b10e377c52`.

| Canonical file | Complete local inventory | Result |
| --- | --- | --- |
| Simple arithmetic copy | **37 = 7 definitions + 15 theorems + 15 lemmas**, no abbreviations | Exit 0; 37/37 matching axiom reports; empty stderr |
| Mixed arithmetic copy | **37 = 7 definitions + 15 theorems + 15 lemmas**, no abbreviations | Exit 0; 37/37 matching axiom reports; empty stderr |
| Permutation rigidity | **15 = 4 definitions + 11 theorems**, no abbreviations or lemmas | Exit 0; 15/15 matching axiom reports; empty stderr |

Every declaration in all three invocations reports exactly `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry`, `admit`, `native_decide`, custom `axiom`, or `unsafe` tokens in these files. The inventory includes noncomputable definitions, rather than auditing only the final theorem. The returned report names were checked against the independently extracted complete inventory.

The arithmetic inventory is `simple`, `simple_vertical_identity`, `simple_vertical`, `simple_horizontal_identity`, `simple_horizontal`, `simple_normalized_bound`, `mixed`, `certificate`, `mixed_vertical_identity`, `certificate_nonneg`, `mixed_vertical`, `mixed_horizontal_identity`, `mixed_horizontal`, `mixed_normalized_bound`, `psi`, `sigma`, `sigma_eq_sum_divisors`, `psi_one`, `exponent_pos`, `factor_eq`, `self_lt_psi`, `psi_le_sigma`, `psi_euler_product`, `simpleRatio`, `mixedRatio`, `simple_scale`, `mixed_scale`, `simple_normalize`, `mixed_normalize`, `ratio_domain`, `simple_bound`, `mixed_bound`, `power_order`, `power_product`, `power_square`, `mathdb_375256`, and `mathdb_375257`.

The rotation inventory is `L`, `D`, `U`, `stationary`, `active_block`, `stationary_value`, `orthogonal_left`, `orthogonal_right`, `positive_diagonal`, `diagonal_distinct`, `stationary_diagonal`, `has_nonpermutation_entry`, `not_permutation`, `rectangular_diagonal`, and `counterexample`.

The campaign `pins.json` agrees with the supplied formal project's `lake-manifest.json` on mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` and all eight other package revisions. Consistently with the no-Git instruction, I did not independently verify dependency checkout revisions or cleanliness with Git. The result is a fresh compilation against the supplied dependency artifacts. Existing canonical `build/audit.json` receipts agree with the hashes/counts above, but were not substituted for these independent checks. Existing `build/paper-build.json` receipts also name the current TeX hashes; I make no independent rendered-PDF claim.

## Arithmetic: exact source and complete proof

The primary source is S. I. Dimitrov, [*Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III*, arXiv:2606.12484v1](https://arxiv.org/html/2606.12484v1), Section 1 and Conjectures 3 and 9. The archived TeX labels are `Conjecture3` and `Conjecture9`; the HTML anchors are `Thmconjecture3` and `Thmconjecture9`. Both exact MathDB posts agree with those formulas. The source's special cases and neighboring conjectures are not used as assumptions.

Write `x = φ(n)^k`, `y = ψ(n)^k`, `z = σ(n)^k`, `a = (n−1)^k`, and `b = (n+1)^k`. The exact targets are

\[
\frac{x}{y+z}+\frac{y}{x+z}+\frac{z}{x+y}
\geq \frac{4(n+1)^{2k}+(n^2-1)^k+(n-1)^{2k}}
{2((n+1)^{2k}+(n^2-1)^k)}
\]

and, with `A = x(y+z)`, `B = y(x+z)`, `C = z(x+y)`,

\[
\frac{A}{B+C}+\frac{B}{A+C}+\frac{C}{A+B}
\geq \frac{5(n-1)^{2k}+5(n^2-1)^k+2(n+1)^{2k}}
{(3(n-1)^k+(n+1)^k)((n-1)^k+(n+1)^k)}.
\]

The final Lean theorems have only natural parameters `n,k` and hypotheses `2 ≤ n`, `1 ≤ k`. This covers every integer pair in the source domain. It does not weaken the statements to prime `n`, selected powers, asymptotic bounds, or an assumed ordering of three abstract variables. All displayed right-hand-side subtraction is performed in the reals after coercion, so natural subtraction cannot change `n−1` or `n²−1`.

**Actual arithmetic bridge.** The code uses `Nat.totient`, defines `sigma n = ArithmeticFunction.sigma 1 n`, and proves `sigma_eq_sum_divisors` for the sum of positive divisors. It defines

\[
\psi(n)=\prod_{p\mid n}p^{e_p-1}(p+1),\qquad e_p=n.\mathrm{factorization}(p),
\]

exactly as the source does. `exponent_pos` proves `e_p > 0` for every included prime, legitimizing the natural subtraction in this definition. `factor_eq` establishes `p^(e_p−1)(p+1)=p^e_p+p^(e_p−1)`.

For `n ≥ 2`, the prime-factor set is nonempty, all prime-power factors are positive, and each psi factor strictly exceeds its corresponding factor of `n`. `self_lt_psi` therefore proves `n < ψ(n)`; integrality gives `n+1 ≤ ψ(n)`. `psi_le_sigma` uses the actual divisor-sum prime-factorization theorem and retains the last two different indices `e_p` and `e_p−1` of each geometric sum. Nonnegativity of the other terms yields `ψ(n) ≤ σ(n)`. Totient positivity and `φ(n) < n` give `0 < φ(n) ≤ n−1`. `power_order` raises these inequalities to every positive integer `k`, obtaining

\[
0<x\leq a<b\leq y\leq z.
\]

The separate `psi_euler_product` proves the real identity

\[
\psi(n)=n\prod_{p\mid n}(1+1/p)\quad(n\ne0).
\]

It uses the positive exponent identity, the prime-power factorization of `n`, and the nonzero real prime denominators. Thus it is an actual bridge to the familiar Euler product, not an assertion in prose or a redefinition chosen merely to satisfy the inequality. The final inequalities need only the proved integral-product bounds, which is sufficient.

**All denominators.** The bridge gives `x,y,z,a,b > 0`. Hence `y+z`, `x+z`, `x+y`, the three mixed quantities `A,B,C`, and `B+C`, `A+C`, `A+B` are strictly positive. Put `r=x/y`, `q=a/b`, `t=z/y`; then `0<r≤q<1` and `t≥1`. Dividing the simple terms by `y` and the mixed terms by `y²` is valid. In normalized expressions, `1+t`, `r+t`, `r+1`, `rt+r+2t`, `2rt+r+t`, and `rt+2r+t` are positive. Every extra certificate factor `2`, `1+r`, `1+q`, `3r+1`, and `3q+1` is positive too. The target denominators are positive because they equal `2b(a+b)` and `(3a+b)(a+b)`, respectively. No proof relies on Lean's totalized division at zero.

**Simple certificate.** The paper and Lean agree on

\[
S(r,t)=r/(1+t)+1/(r+t)+t/(r+1).
\]

For `v=t−1≥0`, the exact vertical difference is

\[
\frac{v[2v^2+(4+r-r^2)v+r(1-r)(r+3)]}
{2(t+1)(r+t)(r+1)}.
\]

All its factors have the asserted signs: `4+r−r²=4+r(1−r)≥0`. The horizontal difference is

\[
S(r,1)-S(q,1)=\frac{(q-r)[4-(1+r)(1+q)]}{2(1+r)(1+q)}\geq0,
\]

because `r≤q≤1`. Consequently `S(r,t)≥S(q,1)=(a²+ab+4b²)/(2b(a+b))`. The exact identities `ab=(n²−1)^k` and `b²=(n+1)^(2k)` convert this denominator to the source's `2((n+1)^(2k)+(n²−1)^k)`. The coefficient 4 multiplies `b²`, not `a²`, throughout.

**Mixed certificate.** Expanding the exact mixed numerators and denominators after division by `y²` gives

\[
G(r,t)=\frac{r(1+t)}{rt+r+2t}
+\frac{r+t}{2rt+r+t}
+\frac{t(r+1)}{rt+2r+t}.
\]

The vertical difference in the paper and code is exactly

\[
G(r,t)-G(r,1)=
\frac{r(t-1)P(r,t-1)}{(r+1)(3r+1)(rt+r+2t)(rt+2r+t)(2rt+r+t)},
\]

where

\[
P(r,v)=(2r^4+4r^3+7r^2+8r+3)v^2
+(4r^4-5r^3+8r^2+19r+6)v+(1-r)(3r+1)(5r+3).
\]

The potentially problematic coefficient is handled by the exact rewrite
`4r⁴−5r³+8r²+19r+6 = 4r⁴+5r²(1−r)+3r²+19r+6 ≥ 0`.
The horizontal difference is

\[
G(r,1)-G(q,1)=
\frac{(q-r)(3+r+q-5rq)}{(r+1)(q+1)(3r+1)(3q+1)}.
\]

Its numerator is nonnegative since `rq≤r` and `q≥r` give `3+r+q−5rq≥3−4r+q≥3−3r≥0`. The exact rational identity `G(q,1)=(5a²+5ab+2b²)/((3a+b)(a+b))` then gives precisely Conjecture 9. All four difference identities are proved by denominator clearing and exact polynomial algebra in the freshly compiled Lean text; the sign arguments are proved separately.

As an independent boundary sanity check using exact rational arithmetic, `n=2,k=1` has `(φ,ψ,σ)=(1,3,3)`. The simple left side and source bound both equal **5/3**; the mixed left side and source bound both equal **19/12**. This also checks the readily confused factors in the mixed right-hand side. It is supplementary evidence, not the universal proof.

**Prior proof credit.** The exact saved responses identify Shivam Patel's general proofs as solution `90a8e5dc-3f39-4dce-9aac-368dd80cf3b1`, posted `2026-08-20T09:23:55.685018Z`, and solution `584960a7-061b-4274-93d0-422447dcc3cf`, posted `2026-08-20T09:24:38.176644Z`. I read both. They already use this arithmetic ordering, normalization, and endpoint evaluation; the mixed positive polynomial is explicitly Patel's. Replacing derivative steps with rational difference identities is a formal-verification presentation change, not evidence of a first proof. The packages appropriately credit him. Patel's additional equality classification is not claimed or needed by these certificates.

## Rotation: all source hypotheses and actual fractional power

The source is Centorrino, Bullo, and Russo, [*Similarity Matching Networks: Hebbian Learning and Convergence Over Multiple Time Scales*, arXiv:2506.06134v1](https://arxiv.org/html/2506.06134v1), Appendix D, Conjecture 3. The exact MathDB 368725 post agrees. The conjecture says that diagonal

\[
K=U^T L^T(LUDU^TL^T)^{-1/3}LU
\]

forces orthogonal `U` to be a permutation when `L` is rectangular diagonal and `D` is positive definite diagonal with distinct entries. Footnote 5 defines rectangular diagonal as `[L^m | 0]` for `m≤n`. The neighboring Lemma 7 also uses descending diagonal order. Neither the source conjecture nor its context excludes `m=1`; its later Rayleigh-quotient remark explicitly discusses that case.

The canonical matrices are

\[
L=[1\;0\;0],\qquad D=\operatorname{diag}(1,1/2,1/3),\qquad
U=\begin{pmatrix}1&0&0\\0&3/5&-4/5\\0&4/5&3/5\end{pmatrix}.
\]

* `L` has type `Matrix (Fin 1) (Fin 3) ℝ`. `rectangular_diagonal` proves that entries with different row/column values vanish. Its active diagonal is `[1]`, hence positive and of full row rank, satisfying even these stronger contextual requirements.
* `D` is definitionally diagonal. `positive_diagonal` proves `D.PosDef`, and `diagonal_distinct` proves injectivity of `i ↦ D i i`. Its entries obey the stricter descending order `1>1/2>1/3>0` as well; no repeated-eigenvalue escape is used.
* `orthogonal_left` and `orthogonal_right` prove `UᵀU=I` and `UUᵀ=I` by exact rational arithmetic. The rotation block has unit column norms and zero inner product.
* `LU=L`, and `active_block` proves `LUDUᵀLᵀ=I₁=[1]`. The final theorem explicitly proves positive definiteness of this active block. Thus the negative power is evaluated at a strictly positive invertible matrix.
* `stationary` contains the source's entire product, in its original order, with `CFC.rpow (...) (-(1/3 : ℝ))`. The exponent is real negative one-third, not truncated integer division. `open scoped MatrixOrder` selects the standard positive-semidefinite order. In the supplied mathlib, `CFC.rpow` is defined by continuous functional calculus of `x ↦ x^y`; `rpow_eq_pow` only exposes its notation, and `CFC.one_rpow` evaluates the identity. This is the actual spectral real-power operation, not an uninterpreted function or a replacement axiom.
* `stationary_value` proves `K=diag(1,0,0)`. `stationary_diagonal` deduces the required diagonality. It does not use the source conjecture, its disputed implication, or a numerical matrix-power routine.
* `not_permutation` quantifies over **every** `p : Equiv.Perm (Fin 3)` and excludes `U=p.permMatrix ℝ`. The witness entry, zero-based `U 1 1=3/5`, cannot be either 0 or 1. `has_nonpermutation_entry` additionally excludes −1, which proves the paper's signed-permutation claim under the usual definition, although a separate signed-permutation predicate is not bundled in `counterexample`.

`counterexample` bundles rectangular form, diagonal/positive/distinct `D`, both orthogonality identities, active-block positive definiteness, diagonal `K`, and nonpermutation. The explicit `L` also makes the row-rank and ordering observations immediate; they are not unproved assumptions supplied to the theorem. One example meeting these hypotheses refutes the universally quantified source assertion. It does not purport to classify all stationary points or prove/disprove the separate trace-maximization result.

The saved response by Shivam Patel, solution `7b45cbbd-c0dc-469c-9c7c-73272a398aef`, posted `2026-08-20T20:53:25.751507Z`, already exhibits the inactive-block mechanism with a `2 × 4` example and an arbitrary inactive orthogonal block. The present `1 × 3` instance is also the `m=1,n=3` specialization of his displayed family. The canonical paper credits that fact. I read the entire response; its broader corrected classification and trace-maximum argument are outside this certificate's scope and are not assumed true merely because they accompany the verified counterexample.

## Source integrity and minor integration findings

The primary-source snapshots used here have these SHA-256 hashes; paths are relative to `frontier/campaigns/2026-10-25/`:

| Snapshot | SHA-256 |
| --- | --- |
| `arithmetic-ratio-lane/sources/arxiv/Lower_bounds_3.tex` | `6b242f3206cb438885158cca500d5d0b27ded340ef86cd19912b09410ae23373` |
| `arithmetic-ratio-lane/sources/2606.12484v1.html` | `8cb6d6b2802dad5af731b98cb0e2713db2b8a109238c112a892229e4e67d7e75` |
| `arithmetic-ratio-lane/sources/375256.json` | `f03f5fa26008ca6be4ae59595543991fae7a88215fef5a6ebf5d08ab3d89f1d2` |
| `arithmetic-ratio-lane/sources/375257.json` | `e57db7371e31a5c6dcfb8fd912e790a56be889a838c79852b281c262abcab097` |
| `permutation-rigidity-lane/sources/source.html` | `f29702cb3934db34cdef92dd37cf44bb3c828f7021ce697519e63ff24951df58` |
| `twenty-proof-campaign/queued-sources/368725.json` | `5d5c5c9fd73a222047b7c64913106098e377c6bac5bb19800812a5cf7cc76a4d` |

1. **Stale arithmetic paper receipt.** Both canonical `provenance.json` copies still give `paper.tex_sha256` as `52fe325bd8ff80ba8ad15d2d6c9bf1b8e47d44f90166a57cb3ab4c23c5c0c854`. The actual canonical TeX hash is `32bb7871455b2ee729999de38509806aa1c4065f5b56533fc4c1c60f4521f01b`, correctly recorded in the current `build/paper-build.json`. The provenance paper block also describes the development PDF path/hash and earlier visual review. Relabel it as a historical lane receipt or regenerate it for the canonical release; do not treat it as certification of the current PDF. This is a metadata inconsistency, not a proof failure.
2. **Older arithmetic references are genuinely wrong.** The copied 375256 source record still claims three source papers and a 2017 origin, pointing to arXiv:2401.09497 and arXiv:1712.08666. Their saved TeX titles are respectively *Weakly Consecutive Sequences* and *Modular periodicity of the Euler numbers and a sequence by Arnold*. They are not the claimed arithmetic-inequality antecedents. The existing `metadata_correction` and README warning correctly flag this; retain them and never use the old links or first-year metadata to infer priority or novelty. The verified target is the exact 2606.12484v1 statement.
3. **Development-relative paths need labeling.** The arithmetic paper says `formal/Checks.lean` reports every local axiom, but neither canonical `formal/` directory contains that file: the campaign verifier generates `build/Checks.lean`. The development lane's checker also uses the original two namespaces. Update the canonical paper's path or explicitly identify it as the development checker. Similarly, `provenance.json` fields `sources/...`, `pins.json`, and `output/pdf/main.pdf` are inherited layout references rather than all being files in each bare outcome directory. The source hashes are correct; clarify their base directory or point to the packaged locations. I did not run the campaign verifier because it invokes Git and writes build artifacts.
4. **Rotation bibliography initial.** The canonical paper cites “P. Centorrino”; the archived source names **Veronica Centorrino**, so the initial should be **V.** The paper URL, coauthors, Appendix D, and conjecture number identify the right source. This does not affect source matching or the counterexample.
5. **Integration status is still provisional.** The outcome files say `candidate`, the READMEs say review is pending, and arithmetic provenance says implementation self-review only. These are understandable pre-integration records; once this review and the parent's PDF QA are integrated, update the status and review pointer together. The historical MathDB “unverified/open” summaries should remain identifiable as snapshots, rather than silently serving as a current-status or novelty claim.

No further error was found in the canonical mathematical statements or written arguments. The supplied source archive and prior responses establish statement identity and prior credit; they do not establish worldwide priority. Retain the explicit no-novelty, no-equality-classification, and no-corrected-rigidity/trace-maximum claims. This review approves the three mathematical/formal outcomes at the exact hashes above, with the listed documentation corrections and the parent's separate release/PDF checks outstanding.

## Parent integration addendum

The rotation bibliography initial was corrected to V. Centorrino, without changing its mathematical text or proof. Its current TeX hash is `55ee5451843a2062312e0f7afb40ac363a1501b89b636442e1592b213d6dc5ac`. Both rendered pages were re-inspected. Arithmetic provenance now labels its old PDF receipts as historical development records; canonical checks were copied to formal/Checks.lean. The byte-identical joint three-page arithmetic PDF was built for both packages and every page inspected. Independent proof hashes remain exactly those reviewed above.
