# I81 — Diophantine approximation and effective arithmetic

Author discovery report, 2026-10-10. **No substantial nomination.** The strongest target, a finite irrationality exponent for Catalan's constant, remains **unproved and unrefuted**. Two actual constructions below give complete, scoped author proofs: a uniform weak rational-separation bound and explicit alternating rational approximants. Both are classified **TECHNICAL** relative to the stipulated lower proof operations. They are not a ninth finding. Independent original-proof and contribution reviews have not occurred. Evidence reproduction is a separate verdict.

All statements and lower operations in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are premises. Nothing below challenges those premises, infers anything from apparent source inconsistencies, or uses separate irrationalities to infer independence. No shared file, old evidence, parent wrapper, other project, git index, commit, or publication was changed. No child agent was launched.

## 1. History, exact domain, and screening

`AGENTS.md` and the four current ledgers were consulted and snapshotted under `sources/i81_diophantine_approximation_discovery/ledgers/` before selection. The snapshots record eight accepted findings, two remaining. The task's more recent exclusion of I76/I79 as a substantial finding is retained. R006/R008/R010, cubic Artin, joint prime neighbors, I73/I75 Selmer, I80 geometric flows, and the spectral branch are excluded.

The initial historical search has 64 lines; the expanded search, adding the first-phase independent reviews and substituting frozen ledger paths, has 83. Exact patterns, file lists, output multisets and hashes are retained. The prior work is decisive:

* F001, `proposals/rotation.md`, `proposals/number_theory.md`, and their reviews already treat π quadrature, small divisors, rational shifts, and singular rotation averages. These are not new targets here.
* F005–F006 and `reviews/diophantine_sums-r1.md` already classify quartic reciprocal sums and noncomputable reals as classical normal-form consequences of single-fold representation. These are excluded.
* The old screening already rejects bounded partial quotients from exponent two and unrestricted inhomogeneous control from homogeneous approximation.

The complete pinned tree has **13,223 entries, 749 manuscript directories, 10,373 blobs**. The search reuses I79's immutable map, consisting of **9,340 corpus files, 776 PDF text representatives, and 257 other bodies**; the original 1,033 outside blobs and their Git hashes are also checked. `rg --files --no-ignore` inventories the corpus. The all-domain content search has 235 split-line records, including PDF form-feed continuations. This is an exact finite lexical search, not a proof that every relevant concept uses these words. The candidate title search and matched-family list are retained separately. Irrelevant matches on “single-fold” or unrelated uses of “Catalan” were not counted as arithmetic companions.

The three starting titles have one manuscript directory each in the complete tree. Their full TeX file sets and PDF bodies are bound. The adjacent fixed-shift Duffin–Schaeffer manuscript has one version. Both September 24 and October 6 H10(Q) directories were checked at version/statement scope: the latter advertises citation updates; ordinary undecidability reductions are already spent. No new consequence uses their arithmetic constructions.

Four distinct exact targets were screened:

1. **C81 (strongest):** find finite constants μ,C>0 and b₀ such that for every a∈Z and b≥b₀, `|G−a/b|≥C b^(−μ)`. An explicitly computable choice would be stronger still. The complete results below fall short of any fixed μ.
2. **P81:** give an algorithm which, on rational ε>0, returns B(ε) such that for all b≥B(ε) and a∈Z, `|π−a/b|≥b^(−2−ε)`. The source gives the eventual bound, not this algorithm. The separated-weight interpolation thresholds precede centers, but the degree threshold can depend on centers; the proof selects several successively large hypothetical approximations before taking the degree limit. Explicit numerical weight inequalities alone do not bound the last exceptional denominator. No claim that effectivization is impossible is made.
3. **S81:** for a fixed single-fold polynomial representing a nonrecursive c.e. set, give a total computable input-wise upper bound on its unique witness when that witness exists. This target is false by the elementary finite-search argument in §6. The lower elliptic height-window operations were inspected: they already give `log g(u)=O((log u)^2)`, complete witness uniqueness, and exact selection of the squared index. Repackaging that sharper upper bound is technical; it bounds a particular total arithmetic gadget, not an arbitrary accepting computation.
4. **D81:** for every fixed γ and finite-valued `0≤ψ(q)≤1/2` with divergent totient-weighted sum, prove for almost every x that `Σ(q≤Q)1{||qx−γ||<ψ(q)} ~ 2Σ(q≤Q)ψ(q)`. The pinned weak Duffin–Schaeffer result asserts infinitely many hits, not this strong law. Its actual lower operations estimate adaptively weighted, selected, and clipped finite arrays, with virtual product marginals. The variance budget does not identify the unweighted original count or sum its covariance error. Its Hausdorff consequence is already printed. D81 is left open here, not refuted; a countable-intersection or Borel–Cantelli transfer is not proposed as a contribution.

No MathDB numerical significance or worldwide priority is claimed.

## 2. Source contracts, including operations below the headlines

Source shorthand C means `preprints/Catalans-constant-is-irrational-September-24-2026/build/`; P means the analogous π directory; S the single-fold directory; D the weak inhomogeneous Duffin–Schaeffer directory. All links below use the immutable revision. `passages.json` binds exact line ranges and their bytes; `relevant-source-files.json` binds all files of the six arithmetic directories, including both H10 versions. The whole search domain is checked independently.

**C foundations.** In [C/sections/foundations.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Catalans-constant-is-irrational-September-24-2026/build/sections/foundations.tex), `eq:parameters`, `eq:rows`, `eq:integer-filter`, and `eq:rational-raw-entry` define n=48N, H=65N, integer Chebyshev rows and an integer column filter. Their contact cancels ζ(2) in each entry. Each filtered entry is an explicitly computable affine polynomial in G with rational coefficients. Define `D_N(X)` by replacing that affine occurrence of G by an indeterminate X. Then `D_N(G)=Δ_N` and `deg D_N≤48N`. This is a polynomial determinant, not an integer linear form in G.

**C finite places.** `prop:two-adic` and its proof bound all full raw minors by a quadratic loss plus `O_G(n log(n+2))`. The proof displays its dependence on G through two discrepancies, not an arbitrary unexplained constant. [C/sections/odd-primes.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Catalans-constant-is-irrational-September-24-2026/build/sections/odd-primes.tex) supplies the operations `lem:odd-digit-reductions`, `lem:odd-central-layer`, `lem:odd-local-elimination` retain both p² and p denominator layers. The resulting nonnegative piecewise-linear loss d has support [0,65] and integral 8609/2. For a large good odd prime ℓ, `v_ℓ D_N(x)≥−N d(ℓ/N)`. This needs x integral at ℓ. One cannot substitute a varying rational x into `prop:finite-lower` and keep its fixed-G asymptotic error unchanged.

**C nonvanishing.** [C/sections/nonvanishing.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Catalans-constant-is-irrational-September-24-2026/build/sections/nonvanishing.tex), `eq:nonvanishing-raw-bridge` through `eq:nonvanishing-factorization`, gives three fixed rational matrices B₀, B₀+B₁, B₀−B₁. Their nonzero determinants are certified modulo 101. At prime scale N=p>260, p-integrality of x makes the x coefficient disappear after multiplying each entry by p². Thus the reduction is independent of the numerator and value of x. The triangular basis has determinant a power of 2 and introduces no new odd exceptional primes. This lower operation, not just the rationality-contradiction wording of the proposition, is used below.

**C real place.** `prop:first-sheet-bound`, `prop:second-sheet-bound`, `prop:energy-reduction`, and [C/sections/certificate.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Catalans-constant-is-irrational-September-24-2026/build/sections/certificate.tex), `prop:real-upper`, give

`limsup n^(−2) log|D_N(G)| ≤ −B`, where `B=2.290939875−(log 2)/2`.

The energy proof controls integration-node collisions uniformly, fixes regularization before the size limit, and then removes regularization. Its certificate concerns D_N(G), not D_N(x) on a real interval and not all cofactors. We never silently extend this estimate to derivatives or to arbitrary rational substitutions.

**P lower operations.** `geom:interpolation` has the precise distinctness hypothesis within each coordinate, successive center-independent weight thresholds, and eventual sufficiently divisible degree. `geom:rees-pushdown` and `geom:serre-vanishing` supply eventual interpolation; `par:weight-margin` chooses actual approximants after dimension. No uniform computable last-exception cutoff is extracted in this report. The already-used `series:generalized` is not resubmitted.

**S lower operations.** `eq:quadratic-sequence`, `eq:square-window`, `prop:growth`, the deterministic first-halt construction, and the complete-witness ledger were checked for the relevant interface. Fixed generator/height constants are existential; inactive witnesses are pinned. Totality of g is proved separately from arbitrary c.e. membership. The source explicitly does not numerically specify its fixed constants. Its uniqueness promise is at most one, allowing no solution.

**D lower operations.** `tab:variance-budget`, `tab:virtual-marginals`, `tab:equidistribution`, and `tab:conditional-reduction` bound a retained weighted finite-block sum, using a virtual dominating sum and controlled discards. The construction's second moment is enough to contradict a positive-measure avoided set. It is not a variance estimate for `Σ1{||qx−γ||<ψ(q)}`. The distinction persists even though the virtual first-mass equidistribution has a displayed `O(1/log log v)` component.

## 3. Construction A: rational specialization with paid denominator dependence

**Theorem A (author proof; technical weak separation).** Under the pinned Catalan source operations, there is a constant C>0 such that, for every a∈Z and b∈N with b≥1,

`|G−a/b| ≥ exp(−C (log(2b))²)`.                 (A)

No numerical value of C, effective asymptotic cutoff, finite irrationality exponent, or badly-approximable constant is asserted. Reduction of a/b is optional. The proof constructs a finite-scale rational test determinant for each fraction; its asymptotic constants are kept existential.

### A1. Uniform finite-place estimate

Let x=a/b be reduced, b≥1, n=48N, H=65N. There are an absolute κ>0 and a function ε_N→0 independent of a,b such that whenever D_N(x)≠0,

`log|D_N(x)| ≥ −A n² − ε_N n² − κ n log b`,    (1)

where `A=8609/4608+(505/4608) log 2`.

Proof. At 2 the proof writes `e₁=4x−M_s(0,0)`, `e₂=−M_s(0,1)`. The smoothed moments are fixed 2-adic numbers, so a fixed c gives `v₂(e_i)≥−v₂(b)−c`. In `eq:exceptional-scalar-bounds` each chosen E or B column costs at most this quantity; there are at most n columns. The repeated-index cancellation, distinct raw indices, and the same minimization therefore give

`v₂D_N(x) ≥ −(505/4608)n² − C n log(n+2) − n v₂(b)`.

This assertion includes zero discrepancies: they delete terms and require no finite valuation assignment.

For odd primes ℓ≤2√H use the displayed coarse entry estimate in the source, whose proof depends on x only through `v_ℓ(x)≥−v_ℓ(b)`. It gives

`v_ℓ F_j(r;x) ≥ −C₀(1+log H/log ℓ)−v_ℓ(b)`.

The row and filter coefficients are integers. The sum of these small-prime losses is at most `O(n√H log H)+n log b`, uniformly in a,b. The O term divided by n² tends to zero.

For `2√H<ℓ≤H` and ℓ∤b, use the entire two-layer argument unchanged: x is locally integral and disappears in the scaled residue formulas. Thus `v_ℓ D_N(x)≥−N d(ℓ/N)`. At a bad prime in this range the coarse estimate instead loses at most `n(3C₀+v_ℓ(b))`, since `log H/log ℓ<2`. Relative to the nonpositive good-prime lower bound, an additional loss of this size is sufficient. Summing the extra terms uses

`Σ(ℓ|b) log ℓ ≤ log b`, `Σ v_ℓ(b)log ℓ=log b`.

This is the missing uniformity step: bad primes of b are allowed inside the large-prime range, and are charged, rather than declared eventually small with a b-dependent threshold.

For odd ℓ>H all rational-array denominators and coefficient denominators are ℓ-integral; only b can contribute, costing at most `n v_ℓ(b)`. Altogether these b-dependent costs are bounded by κ n log b with one absolute κ. Finally the source's weighted PNT limit for the continuous d gives

`N Σ(ℓ≤65N) d(ℓ/N)log ℓ=(8609/2)N²+o(N²)`.

The omitted small primes and 2 only enlarge an independent o(N²) remainder. For nonzero rational D_N(x), the product formula completes (1). All uses are finite-prime inequalities before taking this single N-limit. ∎

### A2. Uniform nonvanishing and an available scale

Let E be the finite set consisting of primes≤260 and primes dividing denominators of the fixed B matrix or numerators/denominators of its three certified nonzero determinants. **E does not depend on a,b.** The source's Frobenius/block argument proves

`v_p D_p(a/b)=−96p` for every prime p∉E with p∤b.       (2)

Indeed the affine x coefficient is p-integral, its p² multiple vanishes modulo p, and the fixed factorization is a unit. This checks nonvanishing at the substituted rational itself; it does not presume D_p(G)≠0.

For any fixed sufficiently large K, and all sufficiently large b, there is such a prime in

`K log(2b) ≤ p ≤ 2K log(2b)`.

To prove this, put X=K log(2b). The prime number theorem gives `Σ(X≤p≤2X,p∉E)log p=(1+o(1))X`. If every such prime divided b this sum would be at most log b. For K>2 that is impossible for large b. This uses all prime factors together; choosing the first prime larger than b would destroy the desired scale. No prime-distribution assertion uniform in an arithmetic progression is needed.

One can select a usable p by finite prime testing and the fixed modular determinant tests. The bound on where such a selection succeeds here is asymptotic, not an explicitly furnished cutoff.

### A3. A paid real perturbation bound

There is a constant C₁ such that for every N≥1,

`sup(|X|≤2) |D_N'(X)| ≤ exp(C₁ n²)`.             (3)

Proof. Let ||·||₁ denote the sum of absolute polynomial coefficients. The Chebyshev recurrence gives `||T_d||₁,||U_d||₁≤3^(d+1)`; multiplication by `(1−t)^(2N)` costs 2^(2N), and the column filter costs 2^(4N). Every d is at most 44N. The scalar moments M(i,j) and Z(i,j) are uniformly bounded in absolute value by their integrable absolute kernel majorants. In the rational decompositions, `0≤c_l≤1`, so M⁰ and Z⁰ are uniformly bounded as real numbers as well. Thus each affine coefficient of a filtered entry has size at most exp(C₂N), with an enlarged fixed C₂. This concerns real size, not its denominator.

Differentiate the permutation expansion. There are n·n! products, each with n factors bounded by `3 exp(C₂N)` on [−2,2]. Absorb `log(n·n!)+n log 3` into C₁n². This proves (3) with no small-cofactor hypothesis. ∎

### A4. Completion of Theorem A

The exact rational certificate for log 2 in the diagnostics confirms `B−A>1/10000`; the source bounds already give a positive gap. Put `δ=(B−A)/8`. For all sufficiently large N, independently of a,b, the ε_N of (1) is at most δ and

`|D_N(G)|≤exp(−(A+7δ)n²)`.

Choose the fixed K in A2 also so large that `κ log b≤δ n` whenever `N≥K log(2b)`. For the selected p, (1) and (2) yield

`|D_p(a/b)|≥exp(−(A+2δ)n²)`.

For large b the preceding upper bound at G is at most half this lower bound. If |a/b|≤2, the segment to `0<G<1` lies in [−2,2], and the mean-value estimate (3) gives

`|G−a/b| ≥ (1/2) exp(−(A+2δ+C₁)n²)`.

Here `n=48p≤96K log(2b)`, proving (A) for all large b. For |a/b|>2 the distance is larger than 1, so the claim is automatic. For the finitely many remaining reduced fractions in [−2,2], use the stipulated irrationality of G to enlarge C. Unreduced fractions have no smaller denominator than their reductions, so the same inequality holds for them. ∎

### What A does and does not achieve

The theorem is stronger than bare irrationality and gives a uniform asymptotic shape, but its exponent `C log(2b)` grows. It does not bound μ(G). The proof pays κ n log b against a gap of order n², requiring n of order log b; the available perturbation estimate then costs order (log b)². A method gap is not a lower bound on every possible method: neither this scale calculation nor the crude derivative estimate proves that a finite exponent is impossible.

The added work is the explicit varying-denominator audit, including bad large primes, and choosing a prime which avoids b at logarithmic scale. The determinant gap, both local denominator layers, and prime-scale nonvanishing are already present in the source. Polynomial perturbation and the prime-product selection are classical. For the task's standard, A is a **technical quantitative extraction**, not a substantial new bridge.

## 4. Construction B: explicit rational approximants from a genuine source row

This construction does not use A or evaluate a polynomial root near G. It uses the central row r=g=4N and first filtered column k=0. Here `D_r(t)=0` and `P_r(t)=(1−t)^(2N)t^(63N−1)`. The actual affine form is

`F_N = M((1−t)^(2N)t^(63N−1), s^(7N)(1−s)^(4N)) = u_N G+v_N`.       (4)

Both u_N,v_N are rational and explicitly computed by the source recurrences. For `c_{d/2}=0` at odd d,

`u_N=4 Σ(h=0..2N)Σ(j=0..4N) (−1)^(h+j) binom(2N,h)binom(4N,j)c_((56N−1+h−j)/2)`,

`v_N=Σ(h,j)(−1)^(h+j)binom(2N,h)binom(4N,j) M⁰(63N−1+h,7N+j)`.

All moment differences in this formula are nonnegative. These are actual rational approximants `r_N=−v_N/u_N`, with no existential coefficient choice.

**Theorem B (author proof; technical row specialization).** For all N≥1, u_N<0 and `sign(r_N−G)=(−1)^(N+1)`. Adjacent r_N are distinct. Set

`η=(7^7 4^4)/(16·11^11)=13176688/285311670611<1`.

For every N≥2,

`0<|G−r_N|≤2^115 √N η^N`.                       (5)

Writing r_N in lowest terms as a_N/b_N with b_N>0, there exists an absolute C₂ such that `b_N≤exp(C₂N)` for every N. No bound with C₂ smaller than `−log η=9.982888…` is proved.

Proof of the coefficient and its sign. The elementary arcsine moment identity

`c_(d/2)=π^(−1)∫(0..π)cos^d θ dθ` (including odd d)

converts the two finite differences exactly to

`u_N=(4/π)∫(0..π) cos^(52N−1)θ (1−cos θ)^(6N)dθ`

`=(4/π)∫(0..1) t^(52N−1)[(1−t)^(6N)−(1+t)^(6N)]/√(1−t²)dt <0`.       (6)

No division by a possibly zero coefficient is hidden.

For N≥2 restrict the last integral to `1−1/N≤t≤1`. On that interval `t^(52N−1)≥4^(−52)`, using `(1−1/N)^N≥1/4`. Bernoulli's inequality gives `(1−1/(2N))^N≥1/2`, hence `(1+t)^(6N)≥64^N/64`. The term `(1−t)^(6N)` is at most half the latter term. The integral of `(1−t²)^(−1/2)` on that interval is at least `1/√(2N)`. As 4/π≥1,

`|u_N|≥2^(−112)64^N/√N`.                       (7)

Proof of the real remainder. The kernel majorant has mass

`K₀=∫(-1..1)∫(0..1) |t|/[√(1−t²)(1−|t|s)] ds dt`

`=2∫(0..1) −log(1−t)/√(1−t²)dt ≤8`.

Also `|(1−t)^(2N)t^(63N−1)|≤4^N` and

`max(0≤s≤1) s^(7N)(1−s)^(4N)=(7^7 4^4/11^11)^N`.

Thus `|F_N|≤8(4·7^7 4^4/11^11)^N`. Dividing by (7) proves (5).

For odd N the integral (4) is strictly positive. For even N, pair t with −t, t>0. The common positive factors leave

`(1−t)^(2N)/(1−ts) − (1+t)^(2N)/(1+ts)<0`,

because `((1+t)/(1−t))^(2N)>(1+ts)/(1−ts)` for 0<t,s<1. Thus `sign F_N=(−1)^(N+1)` for all N. Since `r_N−G=−F_N/u_N` and u_N<0, the asserted sign and strict nonzero error follow. Adjacent errors have opposite signs, so adjacent fractions differ.

Proof of the coarse denominator bound. Let E_N be the least common multiple of the positive denominators of u_N and v_N, computed from the displayed finite formulas. The explicit rational-array formulas bound the valuation loss at an odd prime ℓ≤H by `C(1+log H/log ℓ)` and give no loss at ℓ>H. At 2 their factorial/binomial and recurrence formulas give loss O(H+log H). Consequently

`log E_N ≤ O(H)+Cθ(H)+Cπ(H)log H=O(H)=O(N)`,

using the ordinary PNT already allowed in the source. The crude integral expression (6) gives `|u_N|≤4·64^N`. Since E_Nu_N and E_Nv_N are integers, the reduced denominator b_N divides `|E_Nu_N|`. This proves the stated exp(C₂N) bound. The proof does not assume that clearing denominators preserves analytic decay. ∎

### The exact remaining arithmetic inequality

Let `κ₀=−log η`. If one could prove, for some τ<κ₀ and all large N, `b_N≤exp(τN)`, then (5) would produce small integer forms. More precisely, for any κ′∈(τ,κ₀), (5) gives `|G−r_N|≤exp(−κ′N)` eventually. For a target a/b, choose N of order `log b/(κ′−τ)` so that both errors for N and N+1 are at most `1/(2b exp(τ(N+1)))`. At least one r_j, j∈{N,N+1}, differs from a/b. Rational spacing and b_j≤exp(τj) then give

`|G−a/b|≥1/(2b exp(τ(N+1))) ≥ c b^(−κ′/(κ′−τ))`.

This is a complete conditional finite-exponent reduction, using the proved adjacent noncoincidence. **The inequality τ<κ₀ is not supplied.** An arbitrary exponential denominator bound does not suffice. Our exact finite samples are especially poor compared to existing Catalan constructions, and do not motivate asserting that inequality for this central-row family.

A cofactor or integer-combination variant would instead need a selected rational coefficient vector with paid common denominator and a real remainder that beats it, plus noncoincidence at neighboring controlled scales. The source's full determinant cancellation cannot simply be assigned to each row or cofactor. No such extraction is constructed here. This is the remaining gap, not an invitation to assume small nonzero linear forms from a small high-degree determinant.

## 5. Primary comparison and compatibility limits

External primary literature is **not** a stipulated theorem source. It is used for comparison and to identify hypotheses that have not been paid. HTTP bodies, response headers, retrieval times, final URLs, SHA-256 hashes, version observations and PDF text replays are retained. No external claim is needed to prove A or B.

* Zudilin, [*A determinantal approach to irrationality*](https://arxiv.org/abs/1507.05697), inspected v2 (2016; published 2017), Proposition 2 and §§2,6: positive moment/Hankel determinants allow a quadratic-scale comparison even when the ordinary linear-form criterion fails. His Catalan discussion retains a denominator obstruction. Our determinant-to-weak-separation architecture is in this classical setting; the specific usable gap and arithmetic matrices come from the pinned manuscript.
* Eskandari, [*Improved rational approximations to Catalan's constant*](https://arxiv.org/abs/2609.26354), official record v1 (22 September 2026), actual Theorem 1.1 and §1.2: its 0.62 is a lower bound on the approximation quality of a particular sequence, not an upper irrationality measure. The construction uses integer combinations of controlled hypergeometric integrals. Its denominator statements are not interchangeable with the denominators of (4). Page 2 was rendered and checked visually; the theorem's positive-error condition was retained.
* Calegari–Dimitrov–Tang, [*Arithmetic holonomy bounds and effective Diophantine approximation*](https://math.uchicago.edu/~fcale/papers/ICM.pdf), retrieved author-host 20-page proceedings PDF: Theorem 2.6 requires an independent holonomic family, specified denominator caps, meromorphic presentations and overconvergence data; Remark 2.7 names additional explicit norm/functional-approximation inputs. Theorem 5.1 concerns conductor 3. Footnote 2, equations (5.10)–(5.11), displays an additional π² term in the real Catalan identity that is absent 2-adically. That page was rendered and inspected. Neither their conductor-3 result nor the 2-adic construction supplies the missing conductor-4 real compatibility data.

The related 2408.15403 official record was retained and identifies versions v1/v2; the report does not pretend to have read every page of that longer companion. The ICM's actual relevant statements and real/2-adic distinction were inspected directly. Bounded search observations and author/version records cannot certify the absence of a newer theorem or establish worldwide priority.

In particular, knowing G irrational and μ(π)=2 gives no lower bound on `a+bG+cπ` or `a+bG+cπ²`. The ζ(2) contact cancellation in C is deliberately one-dimensional. Undoing it would introduce a new period and new rank/nonvanishing requirements; no simultaneous approximation theorem is claimed.

## 6. Effective-arithmetic boundary and rejected shortcuts

For S81 choose any fixed single-fold polynomial P(a,w) representing a nonrecursive c.e. set A, as the source permits. If a total computable B(a) bounded every coordinate of w whenever P(a,w)=0, enumerate the finite box `[0,B(a)]^m` and test P exactly. Existence is then decidable, contradicting nonrecursiveness of A. This proof is elementary and deliberately not a nomination.

The qualifier “whenever a witness exists” does not rescue the bound: the finite search returns no on empty fibers. Conversely, for one *supplied total* single-fold graph, unbounded witness enumeration halts on each input and computes its value; that is a different promise. Existence of a representing polynomial with fixed hard-coded coefficients is also different from a numerical compiler supplied by the manuscript. None of these distinctions licenses an effective termination bound for a c.e. relation with empty fibers.

For P81, checking finitely many rational approximations by computation cannot certify the infinite tail from μ(π)=2. The source's ineffective order of choices has not been replaced by a height-uniform interpolation certificate. For D81, neither ordinary Borel–Cantelli nor the weighted virtual-array variance identifies a strong law for original counts. Rational Möbius changes of variables, countable intersections, and elementary uniqueness reductions are classified technical and not developed as new findings.

## 7. Stress tests, corrections, evidence, and verdicts

`experiments/i81_diophantine_approximation_discovery/diagnostics.py` uses only Python's standard library, writes nothing, and tests:

* six exact fractions from (4), independently checking the double-sum u_N against (6)'s finite moment expansion;
* signs and nonzero errors with a certified Catalan interval from 240 terms of Euler's transformed alternating series (positive finite differences, tail at most 2^−240);
* adjacent noncoincidence, exact reduced denominators, and a deliberately coarse finite version of (5);
* the exact area 8609/2, a rational log-2 interval proving the strict arithmetic/real gap, 5,346 bad-prime budget instances, and the n-fold denominator loss;
* observed denominator bit lengths 210,452,663,901,1168,1394 at N=1,…,6. The decimal error/denominator indices lie roughly between 0.065 and 0.082. These finite numbers are diagnostics, not an asymptotic upper bound or a refutation of any general Catalan measure.

The Euler interval is justified by `1/(2k+1)^2=∫(0..1)t^(2k)(−log t)dt`. Its j-th forward alternating difference is the integral with factor `(1−t²)^j`, between 0 and 1. Euler's geometric expansion is therefore positive with tail≤2^−J. This supplies rigorous finite sign checks rather than relying on a floating-point Catalan constant.

Pre-seal failures and corrections are retained in `development-log.md`: family-list postprocessing initially mishandled PDF form-feed continuations after the search itself had succeeded; its explanation was corrected once the actual lines were inspected. The initial historical domain omitted first-phase reviews; a separately named expanded search includes them and frozen ledger paths. The original search outputs remain. The first mathematical diagnostic run passed. No old seal was refreshed, and no failed mathematical assertion was silently replaced.

The exact owned domain is the single report plus the two assigned directories. `seal.json` records every owned artifact except the seal itself, all immutable external references, and the four permitted mutable-ledger comparisons. `verify.py` checks the exact owned path set, bytes, immutable references, complete tree/blob coverage, search multisets, retained response/PDF bindings, passage hashes and diagnostic replay. Verification is **offline and read-only**: no fetching, rewriting, extraction-to-file, resealing, or network library is invoked. PDF replay goes to stdout. It does not execute the acquisition script. The immutable seal's SHA-256 is handed back separately, avoiding a self-hash cycle.

Run from any directory:

`python /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/experiments/i81_diophantine_approximation_discovery/verify.py`

**Author mathematical verdict:** A and B have complete proofs under the stipulated premises; the conditional finite-exponent reduction has its denominator hypothesis displayed. **Strong target verdict:** C81 and P81 remain unproved/unrefuted; S81 is refuted in its stated generality; D81 remains unproved/unrefuted here. **Contribution verdict:** technical partials, no substantial nomination, no count increment. **Evidence verdict:** a passing verifier establishes provenance and finite reproduction only. Parent alone integrates, reviews, counts, commits and publishes.
