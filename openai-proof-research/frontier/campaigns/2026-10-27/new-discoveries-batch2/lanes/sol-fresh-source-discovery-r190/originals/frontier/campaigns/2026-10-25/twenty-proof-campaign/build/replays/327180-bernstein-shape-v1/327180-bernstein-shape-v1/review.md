# Independent review: Bernstein square-sum convexity, MathDB 327180

Reviewed 2026-10-25, America/Los_Angeles. Canonical outcome: `twenty-proof-campaign/outcomes/bernstein-shape`. I read `openai-proof-research/AGENTS.md`, the upstream revision and manuscript catalogue, the complete canonical Lean source, `main.tex`, `PROOF.md`, provenance and outcome metadata, and the relevant original TeX and PDF passages in `../bernstein-shape-lane/sources/`. I independently compiled the complete canonical source through Lean's standard input and checked every local declaration and its axioms. Only this assigned campaign review was written. No nested agents, Git commands, build writes, local Lean object outputs, or edits to the outcome were used. PDF production QA and release integration remain the parent's responsibility.

## Verdict and full-source count eligibility

**PASS — complete source-target proof for MathDB 327180. Eligible for exactly ONE full-source campaign outcome**, under the campaign's policy permitting independently verified known results. There is no remaining mathematical or formal coverage blocker. This is not a newly discovered resolution of an open conjecture: the convexity result was established in 2014, and the canonical text properly credits that fact.

The precise Bernstein square-sum is proved convex on `[0,1]` for every natural `n`; the same polynomial is also proved convex on all of `ℝ`. The certificate includes the defining-polynomial-to-Fourier bridge, rather than assuming a replacement representation. Symmetry, half-line monotonicity, and the exact sharp midpoint minimum are proved too. MathDB **327181 and 327182 are included corollaries and receive ZERO additional outcomes**. Neither the global extension nor a helper lemma earns another count.

The paper's additional positive-coefficient formula has a correct universal mathematical derivation. It is explicitly outside the Lean coverage and is unnecessary for the certified outcome. Minor documentation issues and release limitations are listed below; the parent still needs to finish PDF QA and release checks before declaring the package released.

## Reviewed bytes and independent compilation

These are hashes of the canonical files actually reviewed, not hashes copied from the existing audit receipt.

| Canonical file | SHA-256 |
| --- | --- |
| `formal/BernsteinShape.lean` | `a28d1890152b55dd274c1124677da0bf5b509afa4e7b5a8e9f50831e9def7801` |
| `main.tex` | `d3af82702ea89fc1fbb563e7ae00777389eb089efafc7235cd084dfaa2732c5d` |
| `PROOF.md` | `e9c1a29debfbf14f3b9f7946a80358b91d27e4b4e773f88b74e29be7ffba9cf6` |

Independent invocation:

```text
/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean -DwarningAsError=true --stdin
```

I passed the complete canonical source, unchanged, followed by `#check BernsteinShape.<name>` and `#print axioms BernsteinShape.<name>` for all 20 local definitions, lemmas, and theorems. The working directory was `/tmp`. `LEAN_PATH` contained only the existing dependency `.lake/build/lib/lean` directories under:

```text
/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
```

The source imports only `Mathlib`. Neither the outcome, its `build` directory, nor the development lane was on the import path. No `-o` flag was used. Thus the canonical source was freshly elaborated and kernel-checked; the existing local `BernsteinShape.olean` and `Checks.olean` played no role. Precompiled pinned dependency oleans were used, as requested; this review does not claim to rebuild mathlib itself.

Result: **exit 0, empty stderr, no warnings, 20/20 matching axiom reports**, about 2.806 seconds. Compiler: **Lean 4.34.1**, commit `5045d0056413266e57c625dcd7c365b10e377c52`. The inventory is **2 definitions + 8 lemmas + 10 theorems**. Every declaration below reports exactly `[propext, Classical.choice, Quot.sound]`; none reports an additional axiom.

| Declaration in `BernsteinShape` | Kind | Fresh check and axiom audit |
| --- | --- | --- |
| `basis` | definition | PASS |
| `phi` | definition | PASS |
| `character_conj` | lemma | PASS |
| `character_orthogonality` | lemma | PASS |
| `finite_parseval` | lemma | PASS |
| `character_nat_mul` | lemma | PASS |
| `binomial_fourier` | lemma | PASS |
| `finite_average_identity` | theorem | PASS |
| `convex_norm_affine_power` | lemma | PASS |
| `convexOn_univ` | theorem | PASS |
| `convexOn_Icc` | theorem | PASS |
| `phi_eq_expanded` | theorem | PASS |
| `bernstein_square_sum_convex` | theorem | PASS |
| `symmetry` | lemma | PASS |
| `midpoint_minimum` | theorem | PASS |
| `antitoneOn_left` | theorem | PASS |
| `monotoneOn_right` | theorem | PASS |
| `basis_midpoint` | lemma | PASS |
| `midpoint_value` | theorem | PASS |
| `sharp_lower_bound` | theorem | PASS |

I independently extracted the inventory from every top-level local `def`, `lemma`, and `theorem`, including the noncomputable definitions, and matched the returned report names against it. The source has no `sorry`, `admit`, `native_decide`, custom `axiom`, or `unsafe` token. Inspection finds no alternate local definition of convexity, shadow theorem, imported campaign result, or hypothesis that assumes the desired conclusion.

The dependency HEAD metadata matches all nine revisions in the campaign's `pins.json`: mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, plausible `118aa17ee84656b8bd727fef7c458ee8c833385c`, LeanSearchClient `ddf04cf3949fa556442341e87d47f9f6e6074707`, importGraph `e928b72544873815af278d38681b31c0293588e3`, proofwidgets `106ff4fafc74ef4ac99d81dbf3ab399118f497a5`, aesop `355695d523e41d0554926416cba2a2b3544fbbc9`, Qq `6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259`, batteries `f2effa3d803fda822b1f97b806c47cf2adfbcbc2`, and Cli `e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204`. This was a read of metadata, not a Git command or a fresh dependency build; I did not independently audit dependency working-tree cleanliness or object provenance.

## Exact source, historical status, and scope

The original source is Gonska, Raşa, and Rusu, [arXiv:1401.7908v1](https://arxiv.org/pdf/1401.7908v1), whose PDF header identifies 30 January 2014. I compared the actual TeX around the Bernstein operator and Conjectures 3.2–3.4 with PDF printed pages 10–12, including the available page images. The source defines

\[
b_{nk}(x)=\binom nkx^k(1-x)^{n-k},\qquad
\varphi_n(x)=\sum_{k=0}^n b_{nk}(x)^2,
\]

and Conjecture 3.2 asks for convexity on `[0,1]`. This is precisely the function and interval in `bernstein_square_sum_convex`; there is no normalization, missing factor, changed exponent, restricted class of `n`, or substitute function. `source.json` matches the target formula. The original operator involves `k/n`, hence ordinarily positive degrees; the canonical polynomial statement additionally includes `n=0`, with no need to define that operator at degree zero.

The original TeX's labels `c1`, `c2`, `c3`, and `lc3` correspond to Conjectures 3.2, 3.3, 3.4, and Lemma 3.5. Printed page 11 explicitly credits Thorsten Neuschel for the midpoint lower bound; the proof continues on page 12. Thus the frozen MathDB 327182 assertion that the source provides no resolution is inaccurate. The canonical paper and provenance correctly disclose this, preserving rather than silently revising the source snapshot.

Nikolov's [arXiv:1402.6539v1](https://arxiv.org/pdf/1402.6539v1), PDF header 26 February 2014, states the same square-sum convexity problem as Conjecture 1 on printed page 2. Theorem 2 reformulates it via a Legendre-polynomial ratio inequality, and Theorem 3 supplies an ultraspherical estimate. **Corollary 4 on printed page 3 confirms Conjecture 1.** The TeX labels are `con`, `thm:1`, `thm:2`, and `cor:1`. The canonical paper cites the right corollary. This companion paper also records that Neuschel had established the weaker minimum and monotonicity claims; these are not fresh source problems to count separately.

The [publisher abstract and section snippets for Gavrea–Ivan](https://www.sciencedirect.com/science/article/pii/S0096300314006596), Applied Mathematics and Computation 241 (2014), 70–74, DOI `10.1016/j.amc.2014.05.003`, confirm both a representation-based convexity proof and use of Parseval's identity. Direct page fetch returned HTTP 403, but the indexed publisher text was accessible and corroborated these limited claims. I did not obtain or inspect that article's complete proof. The canonical disclaimer is appropriately limited: no claim that its particular finite average is a specified numbered identity in that paper, and no theorem or formalization priority claim.

All 12 records in canonical `source-hashes.json` match the corresponding files in the development lane. In particular, the full original TeX/PDF hashes are:

| Source file | SHA-256 |
| --- | --- |
| `1401.7908v1-source.tex` | `7c13aca17c5764cb6c8fbf6f23a511e55ba29c10e74c817201e13a1afc6c24d9` |
| `1401.7908v1.pdf` | `dcf653873b4840eb43e8d17d1c600522f04ea4f60a16549f1cea2f037714d109` |
| `1402.6539v1-source.tex` | `dcaddd27fc8171b61cf41a515489f04c99efd5c68e84ea30916ddc2b5f6181ad` |
| `1402.6539v1.pdf` | `0bdef25a55c01cf5d5584d980ec9cb021f24575d26ffb7b92432dd5f1a462ce5` |

No upstream OpenAI manuscript theorem is needed as a mathematical dependency: the certificate uses only the pinned standard libraries. The repository-level immutable upstream record is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; it is not being presented as the source of this 2014 theorem.

## Complete finite Fourier bridge

**Standard characters, not an arbitrary orthogonality axiom.** `character_conj` uses the actual `ZMod.stdAddChar`. In the pinned mathlib, `Analysis/SpecialFunctions/Complex/CircleAddChar.lean` defines it as the complex-valued circle character; `stdAddChar_coe` identifies its value on an integer residue with `exp (2*π*I*j/N)`. `isPrimitive_stdAddChar` proves its primitivity. Thus the paper's roots of unity are the actual objects underlying the code.

**Nonaliasing is proved at the necessary frequency range.** `character_orthogonality` is quantified over `[NeZero N]` and `k l : Fin N`. After conjugation and multiplication are rewritten as a character of `j*(k-l)`, it invokes `AddChar.sum_mulShift` with the proved primitive standard character. The required residue condition

\[
((k:\mathbb N):\mathbb Z/N)-((l:\mathbb N):\mathbb Z/N)=0
\iff k=l
\]

is proved with `ZMod.natCast_eq_natCast_iff'`, `k.isLt`, `l.isLt`, and reduction modulo `N`. There is no unjustified claim that arbitrary integer frequencies are distinct modulo `N`. Taking `N=n+1` accommodates all coefficient frequencies `0,...,n`; differences lie between `-n` and `n`, so the only multiple of `n+1` is zero. It is the frequencies of the degree-`n` binomial expansion that matter; the squared norm's degree `2n` does not demand `2n+1` sampling points.

**Parseval covers signed real coefficients.** `finite_parseval` proves

\[
\sum_{j\in\mathbb Z/N}\left\|\sum_{k:\operatorname{Fin}N} a_k\chi(jk)\right\|^2
=N\sum_{k:\operatorname{Fin}N}a_k^2
\]

for arbitrary `a : Fin N → ℝ`. It casts the equality into `ℂ`, expands each norm square into the complex product with its conjugate, interchanges finite sums, and applies the exact diagonal/off-diagonal orthogonality result. Real coefficients are fixed by complex conjugation, irrespective of sign. No probability or nonnegativity assumption is inserted, so use outside `[0,1]` is valid.

**The coefficients are the original binomials.** `basis` is exactly `choose(n,k)*x^k*(1-x)^(n-k)` over the reals. `character_nat_mul` supplies `χ(jk)=χ(j)^k`. `binomial_fourier` converts `Fin (n+1)` to `range (n+1)`, applies `add_pow`, and matches every coefficient by ring normalization:

\[
\sum_{k=0}^{n} b_{nk}(x)\chi(jk)=(x\chi(j)+(1-x))^n.
\]

This is a proved identity, not a hypothesis or a new definition of `phi`. Instantiating finite Parseval with these real coefficients, taking norms of powers, and dividing by the proved nonzero real number `n+1` establishes `finite_average_identity` for **every `n : ℕ` and every `x : ℝ`**:

\[
\varphi_n(x)=\frac1{n+1}\sum_{j\in\mathbb Z/(n+1)}
\left|x\chi(j)+(1-x)\right|^{2n}.
\]

Finally, `phi_eq_expanded` proves that this same `phi` is the sum of `choose(n,k)^2*x^(2*k)*(1-x)^(2*(n-k))`. Natural subtraction appears only at indices `k≤n` in the finite sum, as required. The exact expanded formula is the final theorem's function. The chain back to the source definition is complete.

## Actual convexity, endpoints, and all degrees

`convex_norm_affine_power` proves actual mathlib `ConvexOn ℝ Set.univ` for `x ↦ ‖(x:ℂ)*z+(1-x)‖^m`. It composes the convex complex norm, considered over the real scalar field, with `AffineMap.lineMap 1 z`, verifies the affine expression algebraically, and uses `ConvexOn.pow` with norm nonnegativity. The pinned `ConvexOn` definition is the ordinary two-point Jensen inequality for all real nonnegative weights summing to one, together with convexity of the domain. This is neither a midpoint-only condition nor a custom predicate merely named convexity.

`convexOn_univ` sums those inequalities for `m=2*n`, scales by the positive `(n+1)⁻¹`, and rewrites by `finite_average_identity`. `convexOn_Icc` restricts to the convex interval `[0,1]`; `bernstein_square_sum_convex` rewrites to the exact expanded source expression. No positivity of `x` or `1-x` is assumed or needed.

**Degree zero is sound throughout.** For `n=0`, `N=1` is nonzero, `ZMod 1` and `Fin 1` each have one element, and the character identities remain valid. There is no off-diagonal pair. The defining polynomial is `1`; the finite average has one zeroth power and denominator `1`. `ConvexOn.pow` explicitly treats exponent zero as a constant function. The sharp value is `choose(0,0)/4^0=1`, and both monotonicity statements are non-strict. No hidden `n>0` premise or division by `n` excludes this case. The endpoints `x=0,1` are also ordinary polynomial evaluations with the conventional zeroth power.

`symmetry` reflects the index range and uses binomial symmetry. `midpoint_minimum` applies global convexity to `x` and `1-x` with equal weights. `antitoneOn_left` correctly separates equality and midpoint boundary cases before using a strict segment; `monotoneOn_right` follows by reflection. `basis_midpoint`, the standard finite Vandermonde sum `Nat.sum_range_choose_sq`, and elementary power algebra establish `midpoint_value`. `sharp_lower_bound` then has no restriction on the real argument. Strict monotonicity, strict convexity, and uniqueness of the minimizer are not asserted in these Lean declarations or in the canonical paper's stated corollary.

## Independent check of the additional integral derivation

The formula in `main.tex` lines 153–199 is mathematically correct:

\[
\varphi_n(x)=4^{-n}\sum_{j=0}^{n}
\binom{2j}{j}\binom{2n-2j}{n-j}(2x-1)^{2j}.
\]

Expanding the finite binomial Fourier polynomial and integrating its conjugate product gives the continuous average: the integral of `exp(i(k-l)θ)` on `[0,2π]`, divided by `2π`, is the Kronecker delta. Only finite sums are interchanged with integrals. With `t=2x-1`, direct algebra gives

\[
|1-x+xe^{i\theta}|^2
=1-4x(1-x)\sin^2(\theta/2)
=\cos^2(\theta/2)+t^2\sin^2(\theta/2).
\]

The substitution `θ=2u` first yields a normalized integral `(1/π)∫₀^π`; reflection yields `(2/π)∫₀^{π/2}`. The paper's normalization is therefore right. Binomial expansion gives the moments `J_{j,n-j}` displayed there.

For integers `a≥0`, `b≥1`, let `F(u)=sin^(2a+1)(u)*cos^(2b-1)(u)`. Its boundary values at zero and `π/2` vanish. Rewriting `sin²u=1-cos²u` in the integral of its derivative yields exactly

\[
0=2(a+b)J_{a,b}-(2b-1)J_{a,b-1}.
\]

The division is legitimate because `a+b≥1`. Together with `J_{0,0}=1` and symmetry `J_{a,b}=J_{b,a}`, this determines all moments, including the boundary families with one index zero, and gives

\[
J_{a,b}=\frac{(2a)!(2b)!}{4^{a+b}a!b!(a+b)!}.
\]

Multiplication by `choose(n,j)` cancels the `n!` and gives exactly the two central-binomial coefficients divided by `4^n`. This covers `n=0` as well. The `n=2` example `3/8+t²/4+3t⁴/8` is correct. Each coefficient is positive, and each even power of an affine real function is convex; the constant term causes no exception.

As a separate regression, I recomputed all integer coefficients for `n=0,...,32`: after `x=(1+t)/2` and multiplication by `4^n`, I expanded `∑ₖ choose(n,k)^2(1+t)^(2k)(1-t)^(2(n-k))` and compared them to the proposed even-power coefficients, checking all odd coefficients were zero. Every comparison passed. This finite computation is not the universal proof; the preceding moment derivation is.

There is **no Lean declaration for the continuous integral, beta moments, or closed coefficient expansion**. The paper and `PROOF.md` say this explicitly. The formal convexity chain uses finite Parseval and `finite_average_identity`, which were independently compiled in full. Thus this additional derivation is an unformalized supplement, not an unpaid bridge or an axiom behind the certificate.

## Agreement and minor issues for integration

`main.tex`, `PROOF.md`, and the canonical Lean file agree on the defining polynomial, all-degree and all-real quantification, positive finite averaging argument, global convexity, symmetry, non-strict half-line monotonicity, sharp value, historical credit, and separation of the extra integral formula from Lean coverage. No mathematical correction to those three files is required for this verdict.

1. **Relocated provenance paths.** `PROVENANCE.md` line 7 retains the lane-relative `../twenty-proof-campaign/queued-sources/`, which does not resolve from the canonical outcome directory. The actual campaign queue is `../../queued-sources/` from that directory, and the full original inputs reviewed here are in `../../../bernstein-shape-lane/sources/`. The bare local PDF/TeX filenames at lines 18 and 28 and `sources/...` paths in `source-hashes.json` also refer to the external lane, not files shipped at those paths inside this outcome. `README.md` correctly says full third-party sources remain in the lane, and `RIGHTS.md` correctly disclaims redistribution, so this is a location/wording issue, not missing mathematical evidence. Make the provenance's reference root explicit for the canonical checkout and extracted release; preserve the verified hashes.
2. **Version-specific citation precision.** The bibliography identifies `arXiv:1401.7908v1` in text but its clickable abstract URL omits `v1`; the same general issue affects the abstract record for Nikolov. The explicit versioned PDF/source links in provenance and the recorded hashes resolve the review's version question. Prefer versioned clickable links in the final paper to make that precision directly available to readers. This does not change the verified theorem.
3. **Supplement coverage and prior status must remain explicit.** Retain the statements that the integral coefficient formula is not formalized, the main theorem was known in 2014, and the companion MathDB entries do not add outcomes. The present wording is adequate. The historical MathDB `open` fields are snapshots, not current mathematical status.
4. **Pending release evidence is not supplied by this review.** `outcome.json` still labels the candidate and independent review pending parent integration. The existing compile receipts agree with my independently computed proof hash, but I did not regenerate them, run the packager, inspect an extracted archive, or perform production-PDF visual QA. Update those statuses and include this review only after the parent's assigned release steps. The package's `pins.json` and verifier references are release-layout promises, not evidence that an archive was independently rebuilt here.

**Final disposition: PASS for the complete mathematical and Lean outcome; full-source count eligibility = 1 for MathDB 327180; extra count for 327181/327182 = 0.** There are no proof gaps, custom assumptions, degree restrictions, nonaliasing gaps, or missing defining-polynomial bridges. The only remaining items above concern documentation precision and parent-owned release validation.

## Parent integration addendum

The parent made the original-source abstract hyperlink explicitly version1 and clarified the base directory for historical source paths. No mathematical statement or Lean proof changed. The current TeX hash is `47b1fed3f9eec35c4d174d44ab16800f5199eb7172c00bcfe59c5bb671a48c59`; the rebuilt final bibliography page and all other pages were visually inspected. Source copies remain in the development lane, with selected question fields and hashes in the release.
