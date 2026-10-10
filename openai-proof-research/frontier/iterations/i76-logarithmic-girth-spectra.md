# I76 — Logarithmic-girth spectra: rejection absorption and two source-level continuations

**Disposition: two completed author proof candidates under the pinned corpus premises, submitted for fresh original-proof and contribution review. No acceptance or count change.** The clean conclusion is obtained through a weaker, explicitly reconstructed spectral interface, not by claiming the entire original CS event. The positive-disorder conclusion has a separate proof using spectral averaging. The latter does not prove the former by a disorder limit. The accepted count remains eight.

The new clean step is a rejection-absorption inequality for a measure-preserving marked involution. It changes a putative additive error at each vertex/spectral point into a multiple of that point's *same defect probability*. The denominator tends to one before any union bound. A regularized logarithmic-potential argument then replaces the only downstream use of full eigenvalue rigidity. The disorder proof instead keeps bounded-depth switching errors inside negative powers of the microscopic height and preserves the two observations on the same realized Hamiltonian.

This report uses every invoked statement and lower proof operation of `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` as a true premise. The new conditioning arguments and their interfaces are what require review. Huang–Yau and McKay–Wormald–Wysocka are external primary inputs: the actual maps, conditional probabilities and proofs used below were inspected. The source's DBM, Gaussian insertion and entropy operations are invoked as *corpus premises*, not as newly audited external theorems.

## 1. Frozen scope, evidence and normalization

The entire supplied I76 brief, including the historical I72 assignment and returned report, is frozen in [full-brief.txt](../sources/i76_logarithmic_girth_spectra/full-brief.txt). [inputs.json](../sources/i76_logarithmic_girth_spectra/inputs.json) hash-references AGENTS, the upstream pin, complete tree, catalogue, I72 report, active `seal-v1.json`, and finalized `frontier/experiments/i72-parent-verification.json`. It permits informational drift of exactly `README.md`, `frontier/README.md`, `frontier/TEN-FINDINGS.md`, and `frontier/iterations/README.md`. No old bytes or seals were changed. Immutable source bodies are referenced in place, not recursively copied.

[source-references.json](../sources/i76_logarithmic_girth_spectra/source-references.json) retains the exact raw URL, Git blob, SHA-256 and local reference for the clean and Anderson manuscripts. [passages.json](../sources/i76_logarithmic_girth_spectra/passages.json) binds the used operations to exact line slices. Retaining a source file is not a claim that every proof in it was read. I72's exhaustive inventory and searches are replayed by its existing read-only verifier; this round does not manufacture a second discovery screen or another corpus coverage count.

Fresh requests and their response headers/hashes are in [fresh-responses.json](../sources/i76_logarithmic_girth_spectra/fresh-responses.json). The official HY page still displays **2102.00963v3**, revised 2 February 2025. Its freshly requested PDF is byte-identical to I72's pinned PDF, SHA-256 `615cdcacafd2ff94520910c712f08e64c4ca1c015da0ee1f87f3528c2cadf469`. The MWW author PDF is unversioned; its fresh SHA-256 is `a49fb3dfe8d6ab44f7f5ad1ca1c0c02ea1bfae67f3680692dae43a06420b3b15`, also unchanged. The fresh clean spectral-contract and Anderson local-law raw requests match the pinned revision. No claim about a newer manuscript is inferred from a catalogue title.

Fix `d≥3`, `b=d−1`, `α=1/100`, and

\[
g_n=\max\{3,\lfloor\alpha\log_b n\rfloor\},\quad
\mathcal A_n=\{G:\operatorname{girth}(G)>g_n\},\quad
\mu_n^g=\mu_n(\cdot\mid\mathcal A_n),
\]

where `μ_n` is uniform on simple labelled `d`-regular graphs on `[n]`. All limits use every sufficiently large `n>d` with `nd` even. There is no connectedness, nonbipartiteness or chosen-component conditioning.

MWW's introduction specifies uniform labelled graphs. Its Theorem 2/Corollary 1, under `b^(2g−1)=o(n)`, gives

\[
q_n=\mu_n(\mathcal A_n)=\exp(-\Lambda_{g_n}+o(1)),\qquad
\Lambda_g=\sum_{r=3}^g\frac{b^r}{2r}.
\tag{1}
\]

This is relative accuracy, not an additive Poisson approximation. In its proof, (3.5) is iterated to (3.6), with an error depending only on `n`; summing gives (3.7). The final paragraph of §3 explains why the exceptional cycle class contributes nothing to the zero-cycle event. Here `b^(2g_n−1)=O(n^.02)=o(n)`, and `Λ_g=Θ_d(b^g/g)`. Thus the support is nonempty eventually and

\[
D_n:=\log(1/q_n)=\Theta_d(n^\alpha/\log n),\qquad D_n/n\longrightarrow0.
\tag{2}
\]

The floor only changes bounded factors. No absolute-probability local law is divided by `q_n` below.

Both corpus ensembles use **ordinary adjacency**, not `A/√b`. Eigenvectors have squared norm `n`; microscopic intermediate coordinates are `x_i=n(λ_i−E)`. Normalized GOE has off-diagonal variance `1/n`, diagonal variance `2/n`, and reference coordinates `(n/π)μ_i`. HY uses `A/√b`, so `z=ζ/√b` and `(A−ζ)^{-1}=b^{-1/2}(A/√b−z)^{-1}`. All these are fixed factors, including the lower height threshold.

## 2. Original I72 lemmas: scoped audit, without repair

**Lemma 1: original PASS for its stated fixed-list operation and bound.** On every atom `(G,e_1,…,e_k)` the weight is `1/(|A|(nd)^k)`, including lists with repetition. On the accepted induced-matching states, exchanging two ending endpoints and updating the list has exactly the stated inverse. The endpoint-induced graph remains precisely the new matching; both graphs satisfy the actual girth acceptance test. Rejection is the identity. The acceptance subset is invariant under the actual map and the weights agree. The sufficient separation event is not the acceptance rule and need not be invariant.

Conditional on any input graph, each endpoint of a uniform oriented edge is uniform on `[n]`. Induced-matching failure is `O_(d,k)(1/n)`. For the switched edges the four cross-distance tests fail with probability at most `4V_d(g)/n`, where `V_d(g)=1+d(b^g−1)/(d−2)`. Delete the two old edges first. A new short cycle with one new edge contains an old short cross-path. A cycle with two new edges either contains such a cross-path or uses alternate paths between the two ends of each deleted edge. Those alternate paths have length at least `g`. This proves the original `C_(d,k)b^g/n` bound. Other unswitched marks only enter the induced-matching test. Products of a fixed number of these exact involutions preserve the law, and their failure probabilities sum. No irreducibility assertion is required or obtained.

**Lemma 2: original PASS, including its stated source use.** For a nonnegative type count `N_h`, `E[N_h|A]≤E[N_h]/q`. If `E N_h≤exp(F_h+a_n)` and there are at most `J` types, Markov at `exp(F_h+a_n+log J+log(1/q)+t)` gives conditional probability at most `e^(−t)/J` per type; a union bound proves the assertion. The type set may be overcounted by a deterministic set of all possible histograms. The clean source's half-edge array count, symmetrization and Stirling errors give `a_n+log J=O_d(M^(d+1)log n)` after the positive simplicity factor. Taking the stated sublinear exponential allowance leaves a polynomially small entropy-per-vertex error after adding (2).

These are audits of the **original** two lemmas, not repairs. Their previous use did not establish CS or neighborhood-resampling independence. This report adds a different marked construction below. The original I72 caution about an additive rejection error was correct for that accounting; it is overcome here by retaining its correlation with the same bad event.

## 3. A finite rejection-absorption lemma

Let `(X,S)` have a marked probability law `π(dx)P_x(ds)`. Let `T` be a measure-preserving involution, writing `x'` for the graph coordinate of `T(x,s)`. Let `A` be an event depending on `x`. Define on the conditioned marked space

\[
T_A(x,s)=\begin{cases}T(x,s)&x'\in A,\\(x,s)&x'\notin A.\end{cases}
\tag{3}
\]

The restriction is an exact involution preserving `π(·|A)P_x`. Indeed its accepted subset consists of pairs with both graph coordinates in `A`; `T` interchanges them and preserves their original weights. Its complement consists of fixed points. This uses no resampling until success and no division by an acceptance rate.

Suppose `U⊂V` are graph events, `W` is another graph event, and

\[
\sup_{x\in A\cap U}P_x(x'\notin V)\le\varepsilon_1,\qquad
\sup_{x\in A\cap V}P_x(x'\notin W)\le\varepsilon_2,\qquad
\sup_{x\in A}P_x(x'\notin A)\le r<1.
\tag{4}
\]

Then

\[
\pi(U\setminus W\mid A)\le\frac{\varepsilon_1+\varepsilon_2}{1-r}.
\tag{5}
\]

**Proof.** Set `B=A∩(U\W)`. Split marked states over `B` into rejected states, accepted states whose images are outside `V`, and accepted states whose images are in `V`. The first mass is at most `rπ(B|A)`, pointwise in the graph. The second is at most `ε_1`. Map the third by `T_A`: its image starts in `A∩V` and its original `T` image lies in `B⊂W^c`, so its mass is at most `ε_2`. Measure preservation gives `(1−r)π(B|A)≤ε_1+ε_2`. ∎

In particular, neither `A` nor the rejection event is assumed independent of spectral data. The probabilities in (4) concern the original independent-mark experiment on each fixed input, including marks subsequently rejected by (3).

**Why normalizing admissible marks is different.** If graph `x` has acceptance probability `a(x)`, choosing marks from `P_x(·|accepted)` introduces `1/a(x)`. Reversal changes this to `1/a(x')`; equality of original marked weights does not cancel it. The accepted-move chain has stationary graph law proportional to `π(x)a(x)`, when the original proposal is reversible. An exact three-state/two-mark check below gives output `(3/4,1/4)` from a uniform two-state input after retry-until-success, with stationary law `(2/3,1/3)`. Thus that suggested repair is not used. Formula (5) retains the original fibers and their independence before rejection.

## 4. Clean approach: the conditioned HY experiment

### 4.1 The actual primary map and the girth bill

Choose HY's geometric parameter `c_H=α/8`, radius `R=(c_H/4)log_b n`, and `0<r_H<c_H/32`. Choose its logarithmic exponents `a_H≥12`, `B_H≥25a_H`, with `ℓ` between `a_H log_b log n` and `2a_H log_b log n`, as in Definition 4.1. Integer roundings are harmless for sufficiently large `n`. In particular `4R+O(1)<g_n`, so every radius-`R` ball in an `A_n` graph is a tree. This places `A_n` inside both geometric classes `Ω̄,Ω̄^+` needed below.

For a fixed root `o`, HY exposes `T=B_ℓ(o,G)`, enumerates its boundary edges `(l_a,a_a)`, and independently chooses one uniform oriented edge `(b_a,c_a)` of `G^(T)` for each boundary edge. Repetitions are allowed. Its switchable indices are determined by its radius-`R/4` tree and isolation indicators `I_aJ_a`, not by our girth-separation criterion. At those indices it switches to `(l_a,c_a),(a_a,b_a)`, retaining the updated marks. Propositions 3.3–3.5 prove that this is an involution and preserves the marked measure: it fixes the exposed ball, and the fiber cardinality

\[
|S(G)|=|\vec E(G^{(T)})|^{\mu},\quad \mu=|\partial_E T|,
\]

is constant on each exposed-ball class. The proof verifies preservation of both indicator sets under reversal. We use **this map**, followed by the whole-map girth rejection (3). We do not replace its random marks with independent accepted marks.

For every fixed high-girth input, its probability of leaving `A_n` is at most

\[
r_n\le C_d\,\mu(|T|+\mu)b^{g_n}/n
       \le n^{-1+\alpha}(\log n)^{C_d'}=o(1).
\tag{6}
\]

Here the exponent on the logarithm may depend on the fixed HY choices. To prove the bound, let `B` contain all endpoints of the boundary edges. Require each sampled far pair to have both endpoints at distance greater than `g_n` from `B`, and require distinct far pairs to have their endpoint sets separated by more than `g_n`. Each endpoint marginal under sampling from `G^(T)` is at most `d/(nd−O(d|T|))≤2/n`, precisely the normalization in HY Proposition 5.9. Bounded-degree ball counting, conditional sequential exposure of the independent far pairs, gives the right side of (6).

On this sufficient event, **every subset** of the boundary switches preserves girth greater than `g_n`, so in particular HY's selected subset does. For a proof, delete the relevant old edges and split a prospective new cycle into old paths and inserted edges. If an old path connects a far pair to the base set or to a different far pair, its length exceeds `g_n`. Otherwise, at any visited far pair the cycle must connect its two ends by an old path after their edge was deleted. This path has length at least `g_n`, since adding back that old edge would give an old cycle. Each visited far pair has exactly one inserted edge at each endpoint, so these alternatives exhaust a simple cycle containing an inserted edge. Old cycles were already long. Shared internal boundary vertices cause no problem. The sufficient event is used solely for (6), not as an acceptance/reversal rule.

### 4.2 Concentration and the global spectral grid

HY Propositions 4.6 and 4.8 are statements **for each fixed input graph**:

\[
G\in\Omega(z)\Rightarrow P_G(TG\notin\Omega_o^+(z))\le C_qn^{-q},\qquad
G\in\Omega_o^+(z)\Rightarrow P_G(TG\notin\Omega_o^-(z))\le C_qn^{-q}.
\tag{7}
\]

The number `q` can be fixed arbitrarily large before `n`. This is not a conditional-probability inference from HY Theorem 4.2. The proof of (7) uses independent oriented-edge marks on the *fixed* graph. In particular §6.1.1 defines the independent variables `Z_a` from the unswitched punctured graph, bounds `|Z_a|≤Cε'`, and applies (6.3) with `t=log n`. Equations (6.5)–(6.8) pay the `|E(G^(T))|` normalization and the deletion error. Propositions 5.18/6.3 compare these variables with the switched punctured resolvent; the Schur expansion (6.24) and the branch average (6.34)–(6.37) yield the improved center bounds. Section 5's events control the loss of `O_q(1)` non-switchable indices through independent-sample distance bounds (5.25), not through independence of graph neighbors. These proofs use only the deterministic geometric/spectral input classes and the original fiber distribution. They therefore still give (7) on our fixed high-girth inputs. No claim of independence conditional on acceptance is needed.

Use (5) with `A=A_n`, `U=Ω(z)`, `V=Ω_o^+(z)`, `W=Ω_o^−(z)`. The inclusion `U⊂V` is HY's explicit inclusion. For all sufficiently large `n`, `r_n≤1/2`, so

\[
\mu_n^g(\Omega(z)\setminus\Omega_o^-(z))\le 2C_qn^{-q}/(1-r_n).
\tag{8}
\]

HY's deterministic self-consistency argument following (4.30) proves `Ω∩⋂_o Ω_o^-⊂Ω^-`. It uses the branch-average equation, the choice of `ℓ` avoiding cancellation in `1+m_sc²+…+m_sc^(2ℓ)`, and the two stability regimes (4.34)–(4.35). Our graphs have no exceptional radius-`R` centers, which only improves that average. A union bound gives

\[
\mu_n^g(\Omega(z)\setminus\Omega^-(z))
 \le C_q n^{1-q}/(1-r_n).
\tag{9}
\]

Now perform HY's deterministic continuation: at `|z|≥2d` its Proposition 4.11 puts every graph in `Ω^-`; the stricter bounds in `Ω^-(z)` imply `Ω(z')` at the next mesh point. A first failure anywhere on a vertical mesh path must belong to one of the defects in (9). There are `O_d(n²)` mesh points in the displayed grid in §4.3. Hence

\[
\mu_n^g(\text{some continuation defect})
 \le C_q n^{3-q}/(1-r_n).
\tag{10}
\]

Fill the grid by the same resolvent continuity bounds used there. For any prescribed fixed power of failure probability choose `q` larger by a fixed amount. **There is no `n³r_n` term.** The rejection term was absorbed separately at each defect before the grid was summed. There is also no product of `1/(1−r_n)` over grid steps: (9) bounds a set difference at one spectral point, and the first-failure argument sums these set differences.

This proves HY's weak local-law conclusion (4.6)–(4.7) for the high-girth ensemble, with arbitrarily high fixed polynomial probability. For the clean proof we only need its bulk restriction: uniformly on a fixed closed bulk interval and heights `η≥(log n)^{B_H}/n`,

\[
|n^{-1}\operatorname{Tr}(A-\zeta)^{-1}-m_d(\zeta)|
 \le (\log n)^B\{n^{-c_*}+(n\eta)^{-1/2}+(n\eta)^{-2/3}\}.
\tag{11}
\]

The same estimate holds for entries on each star relative to the regular tree. There are no bad centers once the relevant star neighborhoods fit below girth; taking `r_H` smaller if needed ensures that. The diagonal bulk estimate at an eigenvalue and height `(log n)^{B_H}/n` gives

\[
|u_i(v)|^2\le n\eta\,\Im (A-\lambda_i-i\eta)^{-1}_{vv}
 \le C(\log n)^{B_H}
\tag{12}
\]

for every eigenvector whose eigenvalue lies in that fixed bulk interval, simultaneously over `v` and over any basis of each eigenspace. This in particular covers every eigenvector used in the microscopic proof.

### 4.3 A weaker sufficient interface, with the rigidity replacement proved

We do **not** infer the whole I72 CS event from (11). HY's all-index rigidity theorem also uses its separate §7 fluctuation-averaging estimate, whose conditioned transfer is not asserted here. Instead the sufficient interface consists of (11), (12), `||A||≤d`, exact eigenvector orthogonality, and the following polynomial log-determinant estimate. This is stronger than a macroscopic weak limit and is exactly what replaces the rigidity invocation in clean `03-entropy.tex:254–263`.

For every sufficiently small fixed `a>0`, `η=n^(−a)`, there is `c'>0` such that

\[
\frac1n\sum_i\log|\lambda_i-E-i\eta|
 =U_d(E)+O(n^{-c'}),\qquad
 U_d(E)=\int\log|t-E|\rho_d(t)\,dt.
\tag{13}
\]

**Proof.** Take a fixed `H_0>4d+|E|`, and write `z_0=E+iH_0`. In every graph of girth greater than `g_n`, closed-walk moments through degree `g_n` agree exactly with the regular-tree moments: a closed walk whose lift does not close would yield a nonempty reduced closed walk, hence a cycle of length at most its length. The norm of both operators is at most `d`. The absolutely convergent expansion

\[
\log|t-z_0|=\log|z_0|-\Re\sum_{k\ge1}\frac{t^k}{kz_0^k}
\]

therefore gives a deterministic error at height `H_0` at most `C(d/|z_0|)^(g_n+1)=n^(−c_a+o(1))`, for `c_a=α log_b(|z_0|/d)>0`. For `U_n(u)=n^(−1)Σlog|λ_i−E−iu|`, differentiation gives `U_n'(u)=Im n^(−1)Tr(A−E−iu)^(−1)`; the same holds for the tree integral. Integrate their difference from `η` to `H_0`. On this vertical line the bulk stability denominator is bounded away from zero, and (11), with its fixed-height continuation up to `H_0`, gives an integrated error

\[
C(\log n)^B\left(n^{-c_*}+n^{-1/2}\int_0^{H_0}u^{-1/2}du
                         +n^{-2/3}\int_0^{H_0}u^{-2/3}du\right).
\]

All integrals are finite. The regular-tree replacement of height `η` by zero costs `O(η)` by the source's tree-potential identity. Decrease `c'` to absorb logarithms and the anchor error. This proves (13). ∎

Every use of the clean spectral proposition in later files was searched and checked. In §3 the rigidity exponent occurs in choosing the smoothing scale and in this log determinant; use any small `a` meeting the entropy mesh inequalities and (13) instead. Delocalization is needed only for the selected eigenvectors with `|x_i|≤S_n²`, where `S_n=exp(√log n)`; (12) supplies it. The other §3 use is the smoothed star covariance at height `n^(−a)`, supplied by (11). In §4 the initial trace/star controls at `S_n/n` and `S_n²/n` come from (11), as does `#{|x_i|≤S_n²}=O(S_n²)`. All remaining spectral tail bounds in that file use positive residues and those initial controls, not rigidity of far-away eigenvalues. The finite-matrix regularity in §6 concerns the subsequently inserted matrices and is reconstructed from the limiting transform; it is not an additional finite-graph rigidity requirement.

Thus (11)–(13) replace the spectral proposition at **all** downstream interfaces. This deliberately leaves literal all-index CS unclaimed while closing the original clean GOE target by a sufficient alternative allowed in the brief.

## 5. Clean theorem and completion beyond the spectral input

**Theorem A (author candidate).** Fix `d≥3` and `|E|<2√(d−1)`. Let `G_n∼μ_n^g`, let `λ_i` be all eigenvalues of its ordinary adjacency matrix, and set

\[
\rho_d(E)=\frac{d\sqrt{4(d-1)-E^2}}{2\pi(d^2-E^2)}.
\]

Under the pinned corpus premises, for every nonnegative `h∈C_c(R)`,

\[
\left|\mathbb E\exp\{-\sum_i h(n\rho_d(E)(\lambda_i-E))\}
-\mathbb E_{\mathrm{GOE}}\exp\{-\sum_i h((n/\pi)\mu_i)\}\right|\longrightarrow0.
\tag{14}
\]

**Proof, with all ensemble interfaces stated.** Sections 3–4 give the required finite spectral inputs. Apply the original Lemma 2 to the clean source's type count. Choose the source's quantization parameters with a positive margin: for a fixed list length `l`, `M=n^(2lγ+o(1))`, `2l(d+1)γ<1`, `4lγ+a<1/4`, `0<a<γ`. Its normalized count error is increased by `D_n/n` and a chosen sublinear Markov allowance, still a negative power of `n`. No union over graph-dependent eigenvector choices is necessary: the type count is simultaneous over all labelings, and all ensuing estimates are deterministic on the same graph event.

The Gaussian covariance `Γ=η[πρ((A−E)²+η²)]^(−1)` has deterministic spectrum between constant multiples of `η` and `η^(−1)`. Independent edge samples give the source's average off-block Gaussian covariance estimate; binning and clipping cost negative powers using (12). Formula (13) gives its entropy determinant. The projected-star argument uses the exact eigenvector relation, its residual variance bound `η/(πρ)+S_n^4/n²`, and star covariance convergence from (11). The mean of a selected bulk eigenvector is zero because its eigenvalue differs from `d`, so it is orthogonal to the constant vector even if the graph were disconnected. Orthogonality and the eigen-equation give the exact edge/star second moments. Edge reversal is still exact under a fixed regular graph. Consequently the source tensor-coercivity and finite-dimensional Gaussian-criterion operations give `prop:edge-moments`, with polynomial accuracy uniformly over graph-selected microscopic indices and fixed moment orders.

For clarity the subsequent limiting argument has three further conditioning bills.

**Endpoint bootstrap.** At `z_0=s+iS_n`, (11) initializes `m_n(z_0)≈m_*` and the sampled endpoint compression `M_(n,k)(z_0)≈K_k(m_*)`; here `p=E/d`, `C_k=I+pJ_k`, `K_k(t)=tC_k+d^(−1)J_k`, and `m_*=m_d(E+i0)`. Off-block entries are controlled by the exact conditional Ward identity `E_(v,w)|R_vw|²=Im m_n/S_n`. The positive-residue bound

\[
\left|(x-z)^{-1}-(x-z_0)^{-1}\right|
 \le C S_n/x^2\le C S_n^{-1}\Im(x-iS_n^2)^{-1},\quad |x|>S_n^2,
\]

pays the distant band. Inside it the source fixed-order moment expansion has only `n^o(1)` terms, so polynomial moment errors remain negligible. On a bounded-trace event its square-weight sum is `O(1/Im z)`. The original I72 involution supplies the two-edge scalar identity under the conditioned law, except on an event `O_k(n^(α−1))`. Reject that event before using its algebra; do not bound an unbounded resolvent there. For a fixed list there is one such graph/mark exception; even charging it at each of `O(log S_n)` heights gives `o(1)`. The switched data have exactly the original law. The rank trace bound `|m_hat−m|≤C/y` and the two-by-two identity give `q²−q−m²=o_y(1)`, `q=(1+Em)/d`; its upper-half-plane root is `m_*`. Halving-height continuation yields the source endpoint estimate with failure `C_(k,D)y^(−D)` in `limsup_n`, for every fixed `D`, with deterministic positive error exponent. No growing finite-`n` channel count is used.

**Marked limit and principal values.** Endpoint tightness gives local count and analytic-function tightness. Uniform graph-conditional moment matching identifies independent Gaussian marks, including separate colors for repeated positions, after truncating each finite spectral list. The tail kernel above, now with a large fixed cutoff `L`, and tightness at `iL`, removes imaginary tails and resolvent differences in probability. Passing to the microscopic limit *first*, the arbitrary-power endpoint estimate may be summed over grids of `O(R³)` points with minimum height `R^δ`. Choose `D>4/δ` and use dyadic Borel–Cantelli. The source kernel integration then gives

\[
\nu([v,u])=\rho_d(E)(u-v)+O(R^{1-\chi}),\quad -R\le v\le u\le R,
\]

and hence the **signed** tails `PV Σ_(|x_j|>R)1/x_j=O(R^(−χ))`, `Σ_(|x_j|>R)x_j^(−2)=O(R^(−1))`. Gaussian-centered residues have summable square weights. Large-height comparison fixes the previously invisible real constants, giving exactly

\[
m(z)=\Re m_*+\operatorname{PV}\sum_j(x_j-z)^{-1},\quad
M_k(z)=K_k(\Re m_*)+operatorname{PV}\sum_j
\frac{C_k^{1/2}g_jg_j^\mathsf TC_k^{1/2}}{x_j-z}.
\tag{15}
\]

The imaginary compression is positive definite. It is not legitimate to omit `K_k(Re m_*)` or to replace signed tails by absolute `1/|x|` summability.

**Finite-channel symmetry and insertion.** Any fixed permutation of ending endpoints is a finite product of the audited girth-preserving transposition involutions. The chance that one of those intended moves is rejected is `o(1)`. The determinant/resolvent identities therefore pass to the limit as exact *unconditional* marked-law symmetries. Gaussian conjugation commutes with `C_k` and `K_k(Re m_*)`; conjugates of a transposition are all reflections, and their finite products give the source continuous `O(k)` switch action. This is a symmetry, not neighborhood independence and not invariance conditional on the positions.

Now `n` has already tended to infinity. The source insertion operates entirely on (15) and this symmetry. At fixed discrepancy exponent `χ`, take

\[
k=2r,\quad K=r^{1/100},\quad T=r^\tau,\quad
\theta=(T/r)^{1/2},\quad L=r^{100/\chi},\qquad 0<\tau<\chi/100000.
\tag{16}
\]

Its rotation coefficients satisfy `||β||≤Cθ`, `cT≤s_2=Tr β²≤CT`, `|s_1=Tr β|≤CT`. The first large cutoff uses signed principal-value tails and Gaussian second moments. The weighted far-block Schur estimates remove positions between `K` and `L`; the source bounds include a vanishing term of order `polylog(r)T³/K`. At the retained dimension `m=2ρK+O(K^(1−χ))`, replacing centered Gaussian rank-one summands by GOE has error `O(m^6 rθ³)=O(r^(−.44+3τ/2))`. These are lower operations on the limiting law, so no girth rejection occurs as `r` increases. They yield raw finite matrices

\[
H_r=\operatorname{diag}(x_j:|x_j|\le K)+s_1I+\sqrt{s_2}\,\mathcal W_m
\]

whose point measures converge to `ν`.

For the density check put `a_*=πρ`, `V_*=(a_*/m)(D_I+s_1I)`, `t_*=a_*²s_2/m`. The limiting transform bound and signed tails give regularity at `g=T^(1/2)/m`, `G=m^(−1/8)`. The source time-window ratios are `t_*/(gm^τ)=m^(49τ+o(1))→∞` and `t_*/(m^(−τ)G²)=m^(−3/4+101τ+o(1))→0`. In the free-convolution equation, the truncated **principal-value transform after subtracting `Re m_*`** tends to `iπρ`; hence its physical solution tends to `i`, giving density `1/π+o(1)`. Dilation by `c_r=πρ_(fc,t_*)(0)→1` makes that density exactly `1/π` before applying the corpus DBM input. The resulting coordinates are `c_rρλ_j(H_r)`, tending to the desired `ρx_j`.

Finally use the source GOE compact-count exponential bound and finite inclusion–exclusion brackets to pass from each fixed correlation order to bounded Laplace functionals. The inserted-matrix count control and vague convergence remove `c_r`; bounded convergence removes conditioning on the limiting input. Every subsequential limit has the GOE law, proving (14). All quantities in (16) grow only after the graph-size limit. ∎

## 6. Independent fixed-positive-disorder approach

This proof does not use the clean local law, the rejection-absorption lemma, or a clean/disordered interchange of limits.

**Theorem B (author candidate).** Fix `d≥3`, `0<κ<2√b`, and take the source's sufficiently small `w_0(d,κ)>0`. For every fixed `0<w<w_0` and fixed `E∈[−2√b+κ,2√b−κ]`, let

\[
H_n=A(G_n)+\operatorname{diag}(V_1,\ldots,V_n),\quad
G_n\sim\mu_n^g,\quad V_i\stackrel{\rm iid}{\sim}\operatorname{Unif}[-w,w],
\]

independently. Let `ρ_(d,w)` be the deterministic density of the expected root spectral measure of the same iid-potential operator on the infinite regular tree. Then (14) holds with the eigenvalues of `H_n` and with `ρ_d(E)` replaced by `ρ_(d,w)(E)`. The density is positive and continuous on the source's allowed bulk band. The disorder threshold is fixed before `n` and does not shrink with the finite mark-list length.

### 6.1 Exact marked law, finite-depth surgery and product potentials

Represent graphs by matchings of distinguishable vertex stubs conditioned on simplicity and `A_n`. Every graph has `(d!)^n` realizations. Choose one or two independent uniform base vertices/base stubs, independent finite ordering seeds, and independent uniform outgoing far stubs. These measures are unchanged from the source except for the graph factor. Retain seeds, internal connecting stubs and pending stubs. For each boundary edge `(p,t)` and far edge `(u,v)`, the source map is

\[
(p-t,u-v)\mapsto(p-u,t-v),\qquad
\text{far outgoing mark }u\mapsto t.
\tag{17}
\]

This mark update, not just the adjacency update, makes the reverse instructions exact. Retain the source's collision/simplicity/inverse-applicability tests and in addition require the final graph to lie in `A_n`; otherwise leave the **entire** marked state unchanged. Equivalently restrict its original involution as in (3). For every fixed depth `j`, the number of marks and updated stubs is fixed. The multiedge separation proof of (6), now with bounded sizes, gives failure at most

\[
\delta_{n,j}=C_{d,j}b^{g_n}/n=O_{d,j}(n^{-1+\alpha}).
\tag{18}
\]

Fixed-radius tree failures disappear eventually. Two independent base explorations overlap with probability `O_(d,j)(1/n)` in *every* regular graph by a bounded ball count. If desired require their exposed vertex sets to be more than `g_n` apart; this costs only (18) and makes the same old-path proof apply simultaneously to both bases. Reversal must still use the actual final-graph test, not that sufficient separation event.

At every accepted atom the conditioned graph/stub/seed/far-mark weight is the same before and after. The map does not read or change potentials. Consequently `(G_hat,V)` has exactly the product law `μ_n^g⊗Unif[-w,w]^n`, not merely the correct marginal laws separately. Arbitrary intermediate cut or re-paired matrices also depend only on graph/marks, so their potentials remain iid conditional on that matrix data. No spectral event is used in choosing a modification.

### 6.2 Recursion on the same realized Hamiltonian

The source's arbitrary-real-symmetric-matrix spectral averaging applies conditional on each such graph modification:

\[
\mathbb E\Im G_{vv}\le\pi/(2w),\qquad
\mathbb E\operatorname{Tr}{\bf1}_I(H)\le C_wn|I|,\qquad
\mathbb P(\|G_{SS}\|>D)\le C_{w,k}D^{-1/2}.
\tag{19}
\]

This includes the final strictly dissipative finite-tree Schur inverses. The sampled Ward identity is unchanged: independent graph-conditional uniform vertex marginals give `E|G_vv'|²≤C_w/(nη)`. Positions in two independent ordered nonbacktracking explorations have independent uniform marginals conditional on the graph, without asserting independence within one exploration.

Here are the full ensemble-dependent pieces of the source recursion proof. They are kept in this order to avoid replacing it by an annealed recursion.

* Partition sample coordinates into the two base groups and the independent far-pair groups. Ward makes cross-group entries small. Sequential cuts use `(I+BQ)^(−1)=I−BQ'` and `G'_(UW)−G_(UW)=−G_(US)(I+BQ)^(−1)BG_(SW)`, with (19) controlling every compression factor. For the two endpoints of a **single** cut far edge, introduce a second independent pair, re-pair `(u,v),(a,b)` as `(u,b),(a,v)`, then cut both. The double-cut graph is identical. The constrained re-pairing involution costs (18); in its new representation `u,v` are in different sample groups. This is the required extra operation; Ward alone does not handle neighboring endpoints.
* Restore exterior replacement edges, postponing the present internal tree. In the two-base construction restore the other base's parent edge, because each observed cavity deletes **only its own** edge from the common final Hamiltonian. The same fixed-dimensional Schur update bounds the error on the present input leaves. Attach the internal tree last. Diagonal substitution of its boundary compression gives exactly the source recursion `F_j` with the original independent far-edge empirical inputs.
* The internal potentials initially come from a sampled base. For a fixed product bin their empirical frequency has variance `O_(d,j)(1/n)` conditional on any high-girth graph: disjoint neighborhoods have independent potentials, and the fraction of overlapping pairs is `O(1/n)`. Bin them on a mesh `n^(−a_j)` with `a_j k_j<1/4`. The source maximal bin coupling replaces the empirical internal-vector law by deterministic iid potentials, at a negative-power cost. Conditional on **the realized H**, this coupling uses only base samples and new randomness; far-edge samples are independent of it. Two such couplings use independent base samples conditional on H. The resulting recursion outputs `R_1,R_2` are iid conditional on H, each with the prediction law formed from that same `P_H`.
* For the mixed moment, couple fresh outgoing-stub samples between H and H_hat. They coincide outside finitely many updated stubs, whose sampling probability is `O(1/n)`. Cut their own edges first; Ward, the group-update identities and (19) control the subsequent updates. Use common fresh iid internal potentials. This proves stability of the recursion prediction `E|d_(H_hat)−d_H|` with the same type of bound. Rejected data have `H_hat=H`, so do not add a multiplier-instability error.

More explicitly, for a bounded 1-Lipschitz test `f`, let `a_H` be its actual empirical observation expectation and `d_H` its recursion prediction. The source compression bookkeeping and the above constrained maps give, uniformly in `e∈J`, `0<η≤h`, `y=nη≥y_0`,

\[
\mathbb E|f(\widehat O_i)-f(R_i)|
+\mathbb E|d_{\widehat H}-d_H|
\le C_{w,d,j}(y^{-a_0}+n^{-a_0}+\delta_{n,j}).
\tag{20}
\]

Bounded tests are essential when discarding rejected configurations. There are only a fixed number of resolvent factors; restricting each to `y^ε` via (19) leaves a positive power after multiplication. No bound on an unbounded entry is charged merely by its rejection probability.

The exact marked invariance on the **common** H_hat and conditional independence of the `R_i` on H give

\[
\mathbb E f(\widehat O_1)f(\widehat O_2)=\mathbb E a_H^2,\quad
\mathbb E f(R_1)f(R_2)=\mathbb E d_H^2,\quad
\mathbb E f(\widehat O_1)d_{\widehat H}=\mathbb E a_Hd_H.
\]

Use (20) to replace the last multiplier and then the observation. Since `E[f(R_1)|H]=d_H`, these identities imply

\[
\mathbb E|a_H-d_H|^2\le C(y^{-a_0}+n^{-a_0}+n^{-(1-\alpha)}).
\tag{21}
\]

Because `y≤hn`, each negative power of `n` is bounded by a constant times a sufficiently small negative power of `y`. Thus (21) is `≤Cy^(−a_1)` for `a_1>0`. The source tent partition on the fixed-dimensional disk/augmented-potential space, followed by Markov, gives

\[
\mathbb P\{W_2(P_H,\Phi_j(P_H))>y^{-c_j}\}\le C_jy^{-c_j},
\tag{22}
\]

and the full-root and augmented versions. This is a statement about the two probability laws *inside a single random H*, not merely their ensemble means.

Start at fixed height `h` by polynomial approximation in a sufficiently large fixed tree neighborhood and the small fixed potential perturbation. Every such neighborhood is a tree eventually; the source's initial small-disk condition follows with no graph exception. Descend through `h,rh,r²h,…` using the source one-level and fixed-`l` tree stability, Schwarz–Pick continuity and (22). The sum of exceptional probabilities is

\[
\sum_{\eta_k\ge\eta_*}C(n\eta_k)^{-c}\le C'(n\eta_*)^{-c}.
\tag{23}
\]

The uniform-in-`n,η` absorption of (18) into a height power took place **before** this summation. In particular there is no unsummed `log n` times a fixed error. This proves the same distributional local-law conclusion as the Anderson source, with possibly smaller positive exponents and constants depending on fixed `w`.

### 6.3 Integrability, marked limits and conditional entropy

The augmented laws in (22) identify the large-microscopic-height diagonal jointly with every finite neighborhood of potentials, and then with the full tree environment by measurability and finite-cylinder approximation. Independent empirical samples yield independent tree environments. Formula (19) supplies Wegner tightness for compact point counts and fixed-dimensional compression tails.

Crucially this preserves microscopic second moments. In the source intercept notation `G_vv=(V_v−A_v−iB_v)^(−1)`, the random variable `B_v` is independent of `V_v` even after conditioning the graph. The disk local law and tree inverse-margin moments yield `P(B_v<Y^(−ε))≤CY^(−c)` at large microscopic height `Y`. Harnack gives `B_v(E+(s+iy)/n)≥(y/Y)B_v(E+(s+iY)/n)`. Moreover

\[
\mathbb E[\Im G_{vv}\,\mathbf1_{\{\Im G_{vv}>T\}}]
 \le C_w\mathbb P(B_v<T^{-1}).
\tag{24}
\]

First `n→∞`, then `T→∞`, and finally `Y→∞` prove the source limiting uniform integrability for every fixed microscopic height `y>0`. The domination `Σ_(|x_i|≤L)u_i(v)²≤(1+L²)Im G_vv(E+i/n)` therefore retains exact identity color covariance in almost every limiting empirical law. Finite-radius tree geometry and edge reversal give automorphism invariance and the tree eigen-equation. The deterministic iid environment marginal follows from the conditional graph-independent variance argument above.

**Centering.** Fix a bounded Lipschitz finite-ball test, first supported where the central potential stays inside `(-w,w)`. Use the source smooth bump `b_0` and simultaneous change `V_v→V_v+t b_0(V_v)` for `0≤t≤n^(−2/3)`. Since the graph factor is unchanged, the product-density estimate remains `TV≤C_(w,b_0)√n t=o(1)`, with no `q_n^(−1)` multiplier. The support condition writes `f/√n=B^(1/2)q_f` with bounded norm; scalar spectral averaging for `H+tB` gives `∫_0^a <f/√n,1_I(H+tB)f/√n>dt≤C_f|I|`. With `|I|=2L/n` and `a=n^(−2/3)` the averaged overlap vanishes. Pass finite empirical first moments using the second-moment bounds, exhaust the central support and finite cylinders, and re-root. This proves `E[U_v|ω]=0` inside almost every empirical law. Orthogonality alone was not used as a substitute for this centering.

**Environment-conditioned count.** At fixed radius `R`, environment-bin number `Q` and mark alphabet, prescribed central potential bins have probability exactly `Q^(−n)` independently of the graph. Lemma 2 applied to this combined count therefore adds `D_n` to, but does not remove, the term

\[
n\{H(T)-(d/2)H(S)-\log Q\}.
\tag{25}
\]

Choose, for example, the extra allowance `t=n^(1/2)`; (2) and the fixed-alphabet `O(log n)` errors vanish after division by `n`, with conditional failure at most `e^(−√n)`. Correctness of the entire overlapping environment label only lowers the count. This is uniform over all eigenvector labelings; we do not condition on the eigenvectors when asserting a probability estimate.

Use the source fixed-height smoothing, quantize and unclip marks, remove their mesh, then send `Q→∞` at fixed `R`, and finally `R→∞`. The entropy contribution of the environment is explicitly zero in the limit: with `s_R=Σ_(k=0)^R b^k`, `p_R=Σ_(k=0)^(R−1)b^k`, the star and edge entropies are

\[
(1+ds_R)\log Q-dp_R\log(b!)+o_Q(1),\qquad
2s_R\log Q-2p_R\log(b!)+o_Q(1).
\]

Their combination minus `log Q` cancels. Potential-bin collisions cost `O_R(Q^(−1)log Q)`. The graph spectra are bounded by `d+w`; fixed-height empirical spectral measures converge to the deterministic tree measure by polynomial approximation and the same local potential law. Gaussian block covariance concentration, determinant entropy and the increasing conditioning sigma-fields thus meet all hypotheses of the source conditional-entropy proof. There is no subtraction of infinite continuous-environment entropies. Its relative-entropy formulation justifies the final conditioning limit.

The source's pointwise tree precision identities, `ΣR_i^T A_oi R_i=I` and `A_oi+A_io=I`, now apply to this same iid environment. Its retained-star Jacobian, Gaussian log-potential identity, and finite inverse-margin/logarithmic moments pay the degenerating constraint direction. The Fisher heat-flow equality, edge re-rooting and conditional centering identify Gaussian colors. The continuous independent root potential makes the two endpoint directions nonorthogonal almost surely; environment ergodicity makes the remaining color covariance deterministic. Normalization from (24) fixes it as `I/(πρ)`. Thus at independent sampled roots, conditionally on positions and their independent environments,

\[
b_j=C_k^{1/2}g_j,\qquad
C_k=\operatorname{diag}(\Im m_\alpha^*/(\pi\rho)),
\tag{26}
\]

with independent standard Gaussian vectors `g_j`. The potential marginal was shown deterministic *inside each empirical law*, which is what makes these sampled environments independent of the limiting point process.

### 6.4 Principal values, potential changes and insertion

Wegner and normalized marks give expected scalar and marked imaginary/difference tails `O_(w,k)(L^(−1))`; compression tails give analytic tightness. The slow trace consequence of (22) passes to the limiting Poisson transform. The source coarse dyadic grid with height `Y=R^(1−ε)` and mesh `R^(1−2ε)` is summable when `2ε<c(1−ε)`. Its kernel integration gives count discrepancy with a positive power, and hence both signed principal-value and square-summable tails as in the clean proof. Large-height convergence **jointly with the same environments** fixes the real compression constants, resulting in

\[
m(z)=\operatorname{PV}\sum_j(x_j-z)^{-1},\qquad
M_k(z)=\operatorname{diag}(\Re m_\alpha^*)+operatorname{PV}\sum_j b_jb_j^\mathsf T/(x_j-z).
\tag{27}
\]

Here the scalar `m` is defined by symmetric principal value, not by the uncentered finite scalar trace. The marked real constants depend on the sampled environments. Finite-cylinder approximation to their measurable tree Green functions identifies them on the existing joint probability space.

Resampling one root potential by an independent uniform value leaves the conditioned ensemble exactly invariant. The rank-one identity `(1+DM_1)M_hat_1=M_1`, the `C/y` scalar difference bound, and (26) give the source quadratic with roots `±iπρ`. Restricting the old environment and new potential to a positive-probability event with nondegenerate tree imaginary parts and `|D|≥c_w>0` is legitimate: that event is independent of the old positions. Gaussian moment concentration then yields arbitrary-power implication failures. The source height descent and a summable grid after the microscopic limit give uniform limiting transform regularity. Constants here depend on fixed positive `w`.

For fixed finitely many sampled roots, allow a uniform-measure-preserving potential map selected by its root-excluded environment. At finite `n`, first use disjoint fixed-radius balls and selections from those balls. Conditional on the graph, marks and all noncentral potentials, the selected root potentials remain independent uniforms; the operation preserves the product law exactly. Graph-only girth conditioning affects none of this. Balls overlap with probability `O_k(1/n)`. Approximate arbitrary root-excluded events in probability by finite cylinders **after** the finite-`n` limit. This proves the source unconditional determinant identity for imaginary trace values. No root-dependent selection is smuggled into the conditional-uniform assertion.

Use the source interval-half exchanges at `r` independent limiting environments, active on a fixed positive-probability root-excluded event. For `θ=(T/r)^(1/2)` choose `l_r=w/N_r≈θ`. Then `D_α=±l_r` on active sites and

\[
\beta_\alpha=\frac{c_\alpha D_\alpha}{1+a_\alpha D_\alpha},\qquad
a_\alpha=\Re m_\alpha^*,\quad c_\alpha=\Im m_\alpha^*/(\pi\rho).
\tag{28}
\]

The active event bounds `a,c` and their derivatives and bounds `c` below. Pairing interval halves gives `|Eβ_α|≤C_wθ²`, `Var β_α≤C_wθ²`; independent environments give `c_wT≤s_2≤C_wT`, `|s_1|≤C_wT` with summable failure along `r=2^j`. The scalar mean is retained, not set to zero. At scales (16), with `k=r`, the source first-cut error includes `r^15L^(−χ)=r^(−85)`, the far-block trace cut costs `polylog(r)T³/K=o(1)`, and Gaussian replacement costs `r^(−.44+3τ/2)=o(1)`. These apply conditionally on positions/environments; only after bounded convergence removes that conditioning is ensemble invariance used.

The resulting `H_r=D_I+s_1I+√s_2 W_raw` has raw point measure converging to `ν`. Its density adjustment is exactly the calculation in §5 with `ρ=ρ_(d,w)(E)`, now using (27). In particular no random environment density replaces `ρ`: the asymptotic count coefficient is deterministic and `m_I=2ρK+O(K^(1−χ))`. The regularity/time-window exponents and the dilation to exact density `1/π` are unchanged. The source GOE factorial-count bounds and finite Bonferroni brackets then identify all Laplace functionals. This proves Theorem B. ∎

All limiting orders used here are fixed `d,κ,w,E`; fixed depth, number of observations and tests; `n→∞`; finite-radius/bin/smoothing refinements in the stated order to construct the marked law; growing height and grids in that limiting law; and finally `r→∞` along the insertion sequence. There is no estimate uniform as `w↓0`: (19) contains `1/w`, bump constants depend on the support inside `[-w,w]`, and (28)'s nondegeneracy constants depend on `w`. None of these proves the quantitative joint regime `nw_n→0` needed for microscopic comparison with the clean matrix.

## 7. Contribution assessment and exact limits of the claims

The new clean argument is the composition of (i) the **whole original HY map** restricted by a graph-only event, (ii) the defect absorption (5), (iii) the pointwise multiedge girth estimate (6), and (iv) the log-determinant replacement (13). It uses the original fixed-input HY concentration rather than transferring its final high-probability statement. This pays the formerly missing summability bill without an acceptance-normalized fiber law. The later entropy, Gaussian mark, signed-tail, orthogonal-switch, insertion and density operations are source operations with the interfaces reconstructed above.

The positive-disorder proof is mathematically distinct: it uses arbitrary-graph spectral averaging and a same-realization empirical recursion, with only bounded-depth graph changes. Its new graph-specific work is (17)–(23) and the conditioned version of (25); its centering, environment precision, Gaussian equality case, principal values and potential insertion are the existing stronger source proof. **By itself this is a technical ensemble extension of that proof, not a second substantial finding.** This is a concrete reduction, not an absence-of-a-printed-match novelty argument.

For the clean statement, the author submits the rejection-absorption bridge for fresh contribution review, without self-certifying it as substantial. The bridge has a short abstract proof and may be judged a technical application of rejection/reversibility plus the existing pointwise HY propositions. Its shortness must not be hidden by the length of the downstream interface audit. A reviewer should decide whether paying a superpolynomially rare global constraint by (5) is a substantial deduction relative to the **entire** permitted lower-operation corpus. No worldwide-priority claim is made. Even if both model statements pass proof review, they are not automatically two findings, or even one accepted finding.

Literal CS with all-index rigidity is not asserted here; its untransferred §7 fluctuation-averaging operation is explicitly bypassed by (13). The clean fixed-energy theorem does not imply those stronger prelimit estimates. No polynomial convergence rate in (14), growing finite-`n` channel theorem, crossover in `w`, cycle-removal output law, conditioned-chain mixing theorem, or deterministic high-girth GOE claim is made. No other I72 target or percolation extension was pursued.

## 8. Reproduction and handoff

From `/home/mj-kang/Documents/Dev/math/openai-proof-research` run

```sh
python3 -B frontier/experiments/i76_logarithmic_girth_spectra/verify.py
```

The verifier is offline and read-only. It checks the I76 seal, exact brief/reference/source/passage/response hashes, the displayed HY version, and PDF text replays without temporary files. It invokes I72's existing verifier in read-only mode to replay that seal and its original corpus/search evidence; it also checks the finalized parent-verification bytes. Only the four declared ledgers may drift informationally. It recomputes new finite diagnostics and compares exact JSON. It neither fetches nor refreshes evidence or seals.

The new checks independently enumerate finite involutions with all graph-event triples to test the absorption inequality and exact rejected-law preservation; give a rational counterexample to retry-until-success normalization; check every subset of a six-boundary/two-base switch on separated cube components, including reversals and the girth test; compute exact closed-walk moments with the first beyond-girth discrepancy; and check a genuine triangle-free cube switch's resolvent identity, identical double-cut graph, and preservation of a finite product potential law. The exhaustive absorption loop count is a diagnostic size, not a mathematical accomplishment. None of these finite checks proves HY applicability, the asymptotic theorems or contribution.

The first diagnostic run stopped at an unavailable optional `sympy` import. Its script and empty stdout are preserved. The final version uses only standard-library exact rational Gaussian elimination at a real spectral point outside the spectrum. This is recorded in `failure-provenance.json`, before sealing; no analytic claim or sealed proof was repaired.

**Handoff:** Theorems A and B are completed author candidates under the specified premises; A uses an explicit weaker sufficient interface, while literal CS is not claimed. Original I72 Lemmas 1–2 pass this scoped audit without repairs. New independent original-proof and contribution reviews are required before acceptance. Only the assigned I76 paths were written. No child agent, shared-index edit, staging, commit, publication or accepted-count change occurred.
