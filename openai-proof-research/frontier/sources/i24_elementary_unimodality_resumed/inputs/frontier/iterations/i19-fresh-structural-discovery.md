# I19 — Fresh structural discovery: a signed staircase-band quotient and its limits

Date: 2026-10-09. Assumed corpus: **openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb**. Disposition: **scoped negative discovery record, with a complete technical lemma; no substantial finding proposed for acceptance**. The accepted count remains four. This report neither reviews I15/I17 nor repeats I18's prime-neighbor problem.

The strongest route was the symmetric/exterior refinement of Saxl. There is an actual improvement over I17's screen: the source's cyclic module is flip-stable, its band quotient is flip-equivariant, and the width-two band has an explicit signed decomposition. Thus one can propagate *signed multiplicity lower bounds*, not merely unsplit support. Sections 3–5 prove this precisely. However, both available band quotients are identically blind to a large family of narrow partitions, even if the smaller staircase factors were completely known. The source's dominance argument does not preserve the flip. No replacement signed dominance construction is proved here. The lemma is a checked source extension, not a solution of the refined conjecture and not substantial-count padding.

Two genuinely different targets were also examined in actual manuscript bodies: elementary unimodality of chromatic quasisymmetric functions, and rapid mixing of the positive-edge-weight switch chain for prescribed degrees. The first remains unresolved; an explicit source-root cycle and an abstract Lefschetz countermodel block two tempting shortcuts. The second, with polynomial dependence on binary weight length, is false, even on six vertices. Its counterexample is proved below, and is not claimed as a substantial discovery.

## 1. Scope, frozen inputs, and search record

The complete assignment is retained in [full-brief.txt](../sources/i19_fresh_structural_discovery/full-brief.txt). Rules, upstream pin, catalogue, complete preprint inventory, ledger, frontier index, I13/I17/I18, and the read-only cache manifest were frozen before research in [inputs.json](../sources/i19_fresh_structural_discovery/inputs.json). The complete inventory, not the truncated `sources/tree.json`, was used. The catalogue's historical headline says 719 manuscripts; the complete inventory has 749 manuscript directories. Retained inventory and cache searches are discovery aids, not assertions that every manuscript was read.

The cache's 9,340 text records were searched for the recorded strings. [corpus-search.json](../sources/i19_fresh_structural_discovery/corpus-search.json) retains paths, terms, line numbers, and contexts. The search found the direct Saxl companion, chromatic paper, switch-chain paper, universal-square companion, and the prescribed-degree corollary in the general perfect-matching paper. Forty-three selected source files were copied into this iteration, each checked against both the cache SHA-256 and its pinned Git blob identity. The rest of the cache was not copied or modified. [pinned-manifest.json](../sources/i19_fresh_structural_discovery/pinned-manifest.json) supplies each immutable raw URL, Git SHA-1, SHA-256, and byte count.

[theorem-contracts.json](../sources/i19_fresh_structural_discovery/theorem-contracts.json) records exact source statement blocks and line locators; [read-locators.json](../sources/i19_fresh_structural_discovery/read-locators.json) distinguishes the proof passages used from merely retained companions. [literature/queries.json](../sources/i19_fresh_structural_discovery/literature/queries.json), retained raw later search results, primary manuscript bytes, version pages, and [primary-contracts.json](../sources/i19_fresh_structural_discovery/primary-contracts.json) record the literature comparison. This is a bounded search, not a worldwide-priority check.

Only this report and the assigned I19 source/experiment directories were written. No agents were spawned and no index, accepted finding, other project, stage, commit, or push was changed. Live shared-index drift is distinguished from a changed frozen dependency by the verifier.

## 2. Three targets and their contracts

### A. Flip-sensitive Saxl — strongest, developed in full to the actual remaining gap

**Exact target.** Let `rho_m=(m,m-1,...,1)` and `N=m(m+1)/2`, initially `m>=3`. Prove that `Sym² S^{rho_m}` contains every irreducible except sign when `m=2 mod 4`, and that `Λ² S^{rho_m}` contains every irreducible except `(N)`, `(N-1,1)`, `(N-2,2)`, sign when `m!=2 mod 4`, and additionally `(2,2,2)` when `m=3`. Small `m=1,2` are handled literally instead of interpreting overlapping exceptional labels.

**Actual corpus input.** *A Cyclic Polytabloid Proof of Saxl's Conjecture*, `build/sections/dominance.tex`, `thm:cyclic-saxl`, gives every irreducible inside the specified cyclic module `W_m=C[S_{B_m}](v_R⊗v_C)`. Its `prop:dominated` covers partitions dominated by the staircase. `band-quotient.tex`, `prop:band-quotient`, is a surjection onto the full induced module from `W_{m-s}⊠U_{m,s}`, for `s in {1,2}`, `m-s>=1`. `path-band.tex`, `prop:two-band`, gives every partition of `2m-1` of length at most four in the specified cyclic band `U_{m,2}`, for `m>=3`. These statements concern ordinary support, but their maps are explicitly available.

**Bridge attempted.** Keep the *same physical tensor flip* through position transpose, the high/low projection, and the direct coordinate-sector induction. Identify the band's two Specht factors as the same submodule of one word space, so that a known symmetric/exterior decomposition applies to the actual flip. This last identification prevents an arbitrary isomorphism between two abstract Specht copies from silently changing the sign question.

**Why the target would be substantial.** It would settle a separately stated refinement with sharp exceptions, giving constituent information not supplied by positive Kronecker coefficients. The bridge actually obtained is much smaller: it refines an existing source projection by a commuting involution.

**Primary comparison.** Bessenrodt–Bowman, [arXiv:2202.03066v3](https://arxiv.org/html/2202.03066v3), Conjecture 10.2 states exactly the target. Their Theorem 7.11 already computes the split of the almost-balanced two-row square; it is an input here, not an I19 discovery. Theorem 6.1/Corollary 6.2 already locates sign, and Proposition 2.5 gives a symmetric-square semigroup property. We exclude rediscovery of these assertions. The source's *Universal Tensor Squares for Symmetric Groups*, especially `balance.tex`, supplies ordinary support through projected components and a classical `Sym^a(Sym² E)` even-row decomposition. That symmetric power is a different operation from the staircase-factor flip. Its displayed separation argument does not assert the refined Saxl statement.

**Disposition.** Prove the signed quotient and explicit lower bounds below; do not claim the conjecture. A precise family inaccessible to either band shows why further induction without a different base mechanism will not finish it.

### B. Elementary unimodality — unresolved after checking the actual wall system

**Exact target.** For every natural unit interval graph on `[n]`, specified by a weakly increasing integer function `i<=h(i)<=n`, write

`chi_G(X;q)=sum_lambda c_lambda(q)e_lambda(X)`, `M=|E(G)|`.

Prove `[q^{j+1}]c_lambda >= [q^j]c_lambda` for all `0<=j<M/2` and every partition `lambda` (together with the already-known symmetry about `M/2`).

**Actual corpus input.** *Elementary Positivity of Chromatic Quasisymmetric Functions*, `01-introduction.tex`, `main:theorem`, constructs a terminating partition-valued permutation witness proving `c_lambda(q) in N[q]`; it explicitly makes no unimodality assertion. `main:hessenberg` gives an abstract degreewise Young-permutation-module decomposition and explicitly does not supply cup-product compatibility. The stronger working interface is `05-triangle.tex`, `tri:monomial`, with `02-graphs.tex`, `graph:kernel`:

`c_lambda(v²)=v^M [X_u] Theta_{x_lambda}^{H_-}`.

Here the roots are forward differences in the triangular chart, not the original positively ordered vertex vectors. `03-reordering.tex`, `alg:reordering`, and `04-walls.tex` prove positive graded coefficients via explicitly shifted shuffle quotients and positive wall factors. Positivity of graded dimensions is not a Lefschetz operator.

**Bridge attempted.** Show these particular theta coefficients are nonnegative sums of centered `sl_2` characters, or construct a raising operator on fixed-shape histories. Products and sums of such centered characters would preserve the required unimodality. Merely replacing dimensions by a presumed hard-Lefschetz structure is not valid.

**Why substantial.** This is the separate unimodality part of the Shareshian–Wachs conjecture, not a parameter change in positivity. Shareshian–Wachs, [arXiv:1405.4629v2](https://arxiv.org/pdf/1405.4629v2), Conjecture 1.3 separates these requirements. Davison–Mandel, [arXiv:1910.12915v3](https://arxiv.org/html/1910.12915v3), Theorems 1.5 and 3.14 establish the relevant Lefschetz property in acyclic cases, with the latter requiring the specified initial pairing matrix to be acyclic and nondegenerate. Their general Lefschetz assertion is Conjecture 3.13. Foster Tom, [arXiv:2311.08020v2](https://arxiv.org/html/2311.08020v2), proves the K-chain case by a signed expansion and cancellation. Restricted known families are not proposed as new results.

**Disposition.** The source's forward-difference quiver already has an oriented three-cycle when `D=3`; nondegenerate enlargement alone leaves that cycle. This does not rule out a useful mutation or another theorem, but no such identification is established. The source permutation-module statement plus an abstract equivariant Lefschetz action is also insufficient, as Section 6 proves. No proof or disproof of general graph unimodality is claimed.

### C. Arbitrary positive edge activities for the degree-preserving switch chain — false in binary complexity

**Exact target screened.** On the complete simple host `K_n`, with graphical degrees `d` and positive rational edge activities `w_e` given in binary, give the source's lazy proposal its Metropolis acceptance `min(1,w(G')/w(G))`, where `w(G)=prod_{e in G}w_e`. Ask for a mixing bound polynomial in `n`, the full activity bit length, and `log(1/epsilon)`, uniformly over all starts and degree vectors.

**Actual corpus input.** *Polynomial Mixing of the Switch Chain for Every Graphical Degree Sequence*, `introduction.tex`, `thm:main`, proves `t_mix<=2n^8` and gap at least `[24 n² binom(n,4)]^-1` for the **uniform** law. With probability one half the chain stays; otherwise it picks a four-set and one of its six ordered distinct matching pairs uniformly. `setup.tex`, `rows.tex`, `slice.tex`, and `disjoint.tex` use uniform conditional slices and an aggregate projection inequality. Arbitrary external activities alter those conditional inner products. `cor:exact-sampling` is exact uniform sampling in expected polynomial time, not a weighted mixing theorem. The matching companion's `cor:prescribed-degree` explicitly uses an explicitly listed simple **unweighted** host; its internal sampler activities do not change that theorem contract.

**Bridge attempted.** Replace each uniform two-vertex conditional slice by its weighted conditional law and prove a weighted version of the aggregate projection estimate before doing comparison. A successful unrestricted result would give a direct local sampler for all binary-encoded prescribed-degree Gibbs laws. One cannot infer it from reversibility or from efficient counting by another chain.

**Primary comparison.** Dyer–Müller, [*Counting Perfect Matchings and the Switch Chain*](https://eprints.whiterose.ac.uk/id/eprint/137388/7/Dyer%20NonbipartiteSIDMA-final.pdf), Sections 2 and 4, distinguish ergodicity and rapid mixing of host-restricted switch chains and exhibit slow classes. Their Section 2 discussion of chordless alternating cycles explains the zero-activity boundary relevant here. It does not by itself state a positive-weight complete-host bound. The six-vertex soft version in Section 7 supplies the exact counterexample needed for this screened scope.

**Disposition.** Reject the unrestricted target by a proof, not by a missing bound. Bounded total energy oscillation gives only the usual comparison-type perturbative regime; no such routine restriction is submitted for counting. The counterexample does not rule out weighted counting or a different sampler.

## 3. A fully signed band quotient

All representations below are finite-dimensional and over `C`. Tensor rearrangements are ordinary and have no super signs. Put

`B_m={(i,j): i,j>=1, i+j<=m+1}`, `G_m=S_{B_m}`,

and let `t_m` be the position involution `(i,j)->(j,i)`. Let `v_R` be the product of the source's ordered row alternations, and `v_C` its column counterpart, with letters `e_1,...,e_r` on a block of length `r`. Define `w_m=v_R⊗v_C` and `W_m=C[G_m]w_m`. Let `F(x⊗y)=y⊗x`.

### Lemma 1: the physical flip acts on the specified cyclic module

The two single-layer submodules are equal as actual subspaces of `E_m^{⊗B_m}`:

`V_m=C[G_m]v_R=C[G_m]v_C`.

They are the source copy of `S^{rho_m}`. Moreover `W_m` is `F`-stable and

`W_m^epsilon=ker(F-epsilon)|_{W_m}=C[G_m](w_m+epsilon Fw_m)`

for `epsilon in {+1,-1}`. In particular these are submodules of `Sym² V_m` and `Λ² V_m` respectively.

**Proof.** Transpose sends each increasingly ordered row to an increasingly ordered column, preserving the displayed letter ordering on every block. Therefore `t_m v_R=v_C`, `t_m v_C=v_R` with scalar exactly one. This proves equality of the two orbit subspaces. It also gives `Fw_m=t_m w_m`, where `t_m` acts diagonally. Since `F` commutes with every diagonal position permutation, `F(gw_m)=g t_m w_m in W_m`. Apply the idempotent `(1+epsilon F)/2` to the cyclic span to obtain the claimed span and eigenspace. ∎

The identity is on the generator. It does **not** say `F=t_m` on all of `W_m`; generally `g t_m` and `t_m g` are different. No character value at `t_m` is substituted for a multiplicity-space flip trace.

### Lemma 2: flip-equivariant induction through the source projection

Fix `s in {1,2}`, `h=m-s>=1`, `D=B_h`, `A=B_m\D`, and `H=S_D×S_A`. Let `U=U_{m,s}` be the source cyclic band module, with physical flip `F_U`, and let `F_h` be the smaller flip. There is a surjection of `G_m×C_2` modules

`W_m --> Ind_H^{G_m}(W_h ⊠ U)`,

where the generator of `C_2` acts in the target by

`g⊗(x⊗y) -> g⊗(F_h x ⊗ F_U y)`.

Consequently, for either `epsilon`, there is a surjective `G_m` map

`W_m^epsilon --> Ind_H^{G_m} [ (W_h^+ ⊠ U^epsilon) ⊕ (W_h^- ⊠ U^{-epsilon}) ].`  (SQ)

**Proof.** The sets `D` and `A` are transpose-invariant. The same ordered-block argument as in Lemma 1 shows the band row and column vectors lie in the same actual single-layer submodule and that their tensor cyclic span is flip-stable.

Use the source projection `P_s=p_s^{⊗B_m}` that retains a pair letter precisely when its two indices are both at most `s` or both greater than `s`. Its local condition is symmetric in the two indices. Thus `P_s F=F P_s` on the entire ambient two-layer word space, not just on the generator.

The source proves, with its signs and unique high-position set accounted for,

`P_s w_m = tilde(w_h) ⊗ u_{m,s}`,

high exactly on `D`. The smaller letters are shifted by `s` in both layers. This letter shift commutes with flip. On the regrouped tensor, the physical global flip is exactly `F_h⊗F_U`, because it exchanges the two letters at every position. It does not exchange the position sets `D,A`.

For every high-position set `J` of size `|D|`, let `T_J` be the coordinate sector with high letters precisely on `J`. The source's sector decomposition is direct, and flip preserves every sector. In the induction map `Phi(g⊗z)=gz`, apply flip:

`F Phi(g⊗z)=gFz=Phi(g⊗Fz)`.

The balanced tensor relation is respected since `F_h⊗F_U` commutes with `H`. The source's inverse sector map also commutes with flip: each coordinate projection onto `T_J` does, as does the action of its chosen coset representative. Hence the source quotient is an actual `C_2` intertwiner, independent of those representatives.

The `epsilon` eigenspace of `W_h⊗U` is the displayed direct sum: eigenvalues on a tensor multiply. Induction is a direct sum of vector-space copies indexed by cosets, so taking an eigenspace commutes with induction. Finally a surjective intertwiner remains surjective on an eigenspace: given an `epsilon` eigenvector in the target, lift it arbitrarily and project the lift with `(1+epsilon F)/2`. This proves (SQ). ∎

Every ingredient needed for the sign statement has now been checked. No inference from ordinary Kronecker positivity to a chosen sign occurs.

## 4. Identify the signed bands and obtain honest lower bounds

For `s=1`, both band layers are the same constant word, hence

`U_{m,1}^+=S^{(m)}`, `U_{m,1}^-=0`.

For `s=2`, `m>=3`, each layer has `m-1` alternating two-blocks and one singleton with letter `e_1`. The source's `lem:polytabloid` identifies its position span with `S^{(m,m-1)}`. Transposing band positions maps the row vector to the column vector, so their spans are the same subspace `V_band`. In particular `U_{m,2}` is a flip-stable submodule of **the actual square** `V_band⊗V_band`.

The known Bessenrodt–Bowman Theorem 7.11 says that, padding a partition `eta` of `2m-1` to four parts with zeroes,

`Sym² S^{(m,m-1)} = direct_sum_{len(eta)<=4, o(eta)=1} S^eta`,

`Λ² S^{(m,m-1)} = direct_sum_{len(eta)<=4, o(eta)=3} S^eta`,  (B)

where `o(eta)` is the number of odd parts; zero is even. The two parts together are multiplicity-free and contain exactly all partitions of length at most four. The source's `prop:two-band` says `U_{m,2}` contains every one of them. A submodule of a multiplicity-free complex module that contains every constituent equals that module: decompose the ambient module into its pairwise nonisomorphic irreducible summands and use semisimplicity, or compare their dimensions. Therefore

`U_{m,2}=V_band⊗V_band`

as an actual subspace, and (B) is also its flip decomposition. This use of the known two-row theorem needs both actual same-space identification and the source's generator-specific full support; arbitrary abstract isomorphisms or bare support in a different ambient space would not suffice.

Let `a_m^epsilon(lambda)` be the multiplicity of `S^lambda` in `W_m^epsilon`, and let `c_{nu,eta}^lambda` be the ordinary Littlewood–Richardson coefficient. Complete reducibility and (SQ) yield, separately,

`a_m^epsilon(lambda) >= sum_nu c_{nu,(m)}^lambda a_{m-1}^epsilon(nu)`,  (L1)

and, for `m>=3`,

`a_m^epsilon(lambda) >= sum_{nu,eta:len(eta)<=4} c_{nu,eta}^lambda a_{m-2}^{epsilon epsilon_eta}(nu)`,

`epsilon_eta=(-1)^((o(eta)-1)/2)`.  (L2)

In (L2), `nu` has size `N_{m-2}` and `eta` has size `2m-1`. These are multiplicity lower bounds, not only support rules. The right sides from different `s` must **not be added**: the quotient maps need not have independent images inside `W_m`. Taking their maximum is valid.

The base `W_1` is trivial with positive flip. For `m=2`, the source's cyclic support plus the multiplicity-free `S^{(2,1)}` square gives `W_2=V_2⊗V_2`; its positive types are `(3),(2,1)` and its negative type is `(1,1,1)`. The trivial and sign constituents of every `W_m` can also be seeded from cyclic support, because they each have multiplicity one in the full square and their locations are already known (BB Corollary 6.2). These known seeds carry no new significance.

Exact rational character calculations and independent Littlewood–Richardson tableaux enumeration verify these recursive lower bounds against the full squares for `m=3,4,5`. With just the specified seeds, positive lower bounds cover respectively 9, 38, 159 symmetric types and 5, 29, 150 exterior types; actual full-square counts are 11, 42, 176 and 6, 38, 172. This is finite diagnostic evidence, not an induction proof of those full supports at arbitrary `m`.

## 5. A structural obstruction to finishing with these bands

### Proposition 3: an entire width range is inaccessible

If `lambda` is a partition of `N_m` with

`lambda_1 < m` and `4 lambda_1 < 2m-1`,  (W)

then **neither** width-one nor width-two induced quotient contains `S^lambda`, even if the smaller modules are replaced by arbitrary sums of all irreducibles of the appropriate degrees. This assertion is about the quotients, without a sign restriction.

**Proof.** By Pieri, `c_{nu,(m)}^lambda>0` would require a horizontal `m`-strip inside `lambda`, which has only `lambda_1` columns. Thus it is impossible if `lambda_1<m`.

If `c_{nu,eta}^lambda>0` and `len(eta)<=4`, a Littlewood–Richardson tableau of `lambda/nu` has entries in `{1,2,3,4}` and strictly increasing columns. Every skew column therefore has at most four boxes. There are at most `lambda_1` columns, so `|lambda/nu|<=4lambda_1`. But in the width-two quotient that size is `2m-1`. This contradicts (W). Every LR coefficient in either quotient vanishes, proving the result. ∎

For every `m>=5`, the nonsign partition

`lambda=(2^{floor(N_m/2)}, 1^{N_m mod 2})`

satisfies (W). It is not an exceptional constituent in the refined conjecture. For `m=5`, exact character arithmetic gives symmetric/exterior multiplicities **54 and 49**, whereas both quotient bounds are zero. Thus the issue is not that the desired constituents are absent, nor merely that the smaller induction hypothesis is weak. The two source bands cannot see them at all.

### Why the source dominance argument does not fill the signed gap

The source supplies those ordinary constituents using a row-subgroup signed average and a sign intertwiner on **one** tensor factor. It produces an isomorphic image of `W_m⊗sgn` containing the repeated-row cyclic vector `v_R⊗v_R`, then projects onto `M^{rho_m}`. That proves ordinary support for dominated targets.

After identifying the two Specht subspaces, write a sign intertwiner as `J:V_m -> V_m`, with `J rho(g)=sgn(g)rho(g)J`. One-factor twisting has the elementary identity

`F (id⊗J) = (J⊗id) F`,

not `(id⊗J)F`. Unless extra information is supplied, that operation does not send a prescribed flip eigenspace into either prescribed flip eigenspace. The repeated-row vector is symmetric only *after* the one-factor twist. The permutation-module quotient therefore does not say which sign of the original staircase square contains a given constituent.

This is visible already for the standard representation of `S_3`: symmetric square is `1 ⊕ standard`, exterior square is `sgn`. Twisting the total module by sign sends the trivial symmetric type to the sign exterior type, while the standard type remains symmetric. There is no uniform preserve-sign or reverse-sign rule for this twist. Consequently neither conjugating partitions nor reusing `prop:dominated` is a valid repair of (W).

**Precise unfinished construction.** To complete this approach one needs actual maps or nonzero pairings on `W_m^epsilon` for the missing dominated partitions, compatible with the source's signed averaging and one-factor sign intertwiner; alternatively, a different projection with wider signed band support that reaches (W). An ordinary dominance statement, complete ordinary support of `W_m`, or a lower bound on `a_m^+ + a_m^-` does not provide that datum. This report proves (SQ), (B), (L1), (L2), and (W); it does not assume the missing signed statement and call the resulting reduction a finding.

The independent primary comparison also keeps the significance limited: the band split itself is known, and the new quotient is obtained by checking a commuting involution on existing maps. It is useful progress over the previous screen, but does not meet the requested substantial standard by itself.

## 6. Two precise limits on the unimodality route

### 6.1 The initial root quiver is cyclic

Take the source triangular chart with `D=3` and ordered times

`d1=1, b11=3/2, d2=2, b22=9/4, b12=11/4, d3=3`.

The phase order is exactly `(2,2);(1,1);(1,2)`. Adjacency is time difference less than one. Let the six listed vertex vectors be `a0,...,a5` and the five simple roots `c_i=a_{i+1}-a_i`. The source convention is `Omega(b,a)=1` for a later adjacent vertex `b`. Bilinearity gives

`Omega(c_i,c_j)=Omega(a_{i+1},a_{j+1})-Omega(a_{i+1},a_j)-Omega(a_i,a_{j+1})+Omega(a_i,a_j)`.

The exact matrix is

```
 0 -2  0  1  0
 2  0 -1 -1  1
 0  1  0 -1 -1
-1  1  1  0 -1
 0 -1  1  1  0
```

Thus `c0 -> c3 -> c1 -> c0` is a directed cycle when positive entries orient arrows; reversing every arrow still gives a cycle. Passing to the source's symplectic enlargement changes none of these entries. Therefore the acyclic hypothesis in the direct Davison–Mandel application is not satisfied. A bounded exploratory mutation search also did not find an acyclic chart; its finite bounds are retained, and **no mutation-invariant impossibility is inferred**. Even a successful change of seed would require checking the exact theta/normalization and coefficient transport hypotheses, not merely changing this matrix.

### 6.2 Degreewise permutation structure plus Lefschetz is not enough

Consider the formal symmetric function

`F(X;q)=(1+q²)e_2(X)+q e_{1,1}(X)`.

It is coefficientwise elementary-positive and palindromic about degree one. Since `e_2=s_{1,1}` and `e_{1,1}=s_2+s_{1,1}`, it equals

`F=(1+q+q²)s_{1,1}+q s_2`.

This is Schur-Lefschetz: its two coefficient polynomials are centered irreducible `sl_2` characters after the usual degree centering. More concretely, `omega F` is the graded character of a trivial `S_2` representation tensored with the three-dimensional `sl_2` irreducible, plus a sign `S_2` representation tensored with its one-dimensional irreducible in the middle degree. Each degree is a Young permutation module: `h_2` in degrees zero and two, `h_{1,1}` in degree one. The two actions commute, and the raising operator gives all required Lefschetz isomorphisms. Yet the elementary coefficient of `e_2` is `(1,0,1)`, not unimodal.

This is not the chromatic function of a claimed counterexample graph or a constructed Hessenberg variety. It shows exactly that those *abstract* positive decomposition and Lefschetz properties do not force the desired coefficient inequalities. The missing datum is an `sl_2` action preserving the individual elementary/Young multiplicity spaces, or an equivalent centered-string decomposition of each source history polynomial. The corpus's freely chosen graded sections and rank-based packet matchings do not supply such an action in their stated contracts. The general graph target remains open in this report.

## 7. Positive-weight complete-host switch counterexample

For each integer `L>=1`, take `n=6`, all degrees equal to one, and `delta=2^{-L}`. On the complete host `K_6`, assign activity one to the six edges of the cycle `0-1-2-3-4-5-0` and activity `delta` to every other edge. All activities are strictly positive rationals with total binary encoding length `O(L)`. The state space is the 15 perfect matchings of `K_6`.

There are exactly two matchings using only cycle edges, the two alternating cycle matchings, each of weight one. Starting from either one, any accepted nontrivial switch must introduce a noncycle edge: the other all-cycle matching differs on all six vertices and cannot be reached by a four-vertex switch. Therefore every proposed move away has Metropolis acceptance at most `delta`. The source proposal is one-half lazy, so its total one-step probability `q_exit` of leaving this state satisfies `q_exit<=delta/2`. The stationary mass of the state is at most `1/2`, since the second weight-one state also exists.

For any integer `t>=0`, the probability of never leaving during the first `t` steps is `(1-q_exit)^t >= 1-t q_exit`. Thus, using the singleton starting state as a total-variation test,

`||P^t(M,.)-pi||_TV >= 1-t q_exit-pi(M) >= 1/2-t delta/2`.

At every integer `t<1/(2delta)`, this is strictly greater than `1/4`. Hence

`t_mix >= ceil(1/(2delta)) = 2^{L-1}`.

This is exponential in input bit length with `n` fixed. Irreducibility is not at issue: all complete-host switches retain positive acceptance and the ordinary perfect-matching switch graph is connected. The stationary law is exactly the intended product-activity law by symmetric proposal and Metropolis detailed balance.

The finite enumerator additionally obtains

`Z(delta)=2+3delta+6delta²+4delta³`,

and `q_exit=(3delta+3delta²)/(12 binom(6,4))=(delta+delta²)/60` for the source's exact convention. The crude bound above already proves the result and does not rely on enumeration. It also identifies why the uniform conditional-projection argument cannot give a universal polynomial weighted gap. This is the familiar softening of a disconnected zero-weight limit; no novelty or counting credit is asserted.

## 8. Validation and reproducible handoff

Run from the project root:

```sh
python frontier/experiments/i19_fresh_structural_discovery/check.py
python frontier/experiments/i19_fresh_structural_discovery/verify.py
```

The standard-library exact diagnostic performs 111 two-row split checks, 458 signed recursive multiplicity comparisons, and 434 character orthogonality checks. It uses Murnaghan–Nakayama with literal connected border-strip enumeration and exact rational character inner products; LR coefficients are independently counted by lattice-word skew tableaux. Orthogonality and the symmetric/exterior dimension identities help catch implementation errors. These calculations are finite verification, not a replacement for the representation-theoretic proof.

Five source-generator projection cases expand the literal alternating words for `m<=4`, verify the transpose/flip relation, compare every retained coefficient with the factored generator, and check the projected flip identity. The largest two cases each inspect 82,944 input pair words. The graph diagnostic enumerates all 15 matchings and checks stationary masses and escape probabilities at 12 exact dyadic activities. It also checks the displayed root matrix and formal unimodality countermodel. All assertions pass; results are in [results.json](../experiments/i19_fresh_structural_discovery/results.json).

The artifact seal covers this report, scripts, raw literature, extracted contracts, search evidence, source copies, and frozen inputs. The verifier checks source SHA-256 and Git blob identities against the complete frozen tree, literature retrieval hashes, source-statement slices, and the seal. Frozen-input corruption is a failure. A difference in a live shared input is reported separately as concurrent drift; it does not rewrite the frozen evidence or silently change the mathematical premise. Final offline verification passes for 10 frozen inputs, 43 pinned sources, 117 source contracts, 10 primary retrievals, and 10 primary contracts; the exact diagnostic JSON reproduces after JSON key normalization. The live ledger and frontier index changed concurrently, and both are explicitly reported as drift while their frozen copies remain intact. Neither a proof-review PASS nor a separate significance PASS is claimed.

**Handoff:** the source band construction does support a signed quotient, so a future Saxl attempt should use (SQ) and the known explicit band signs rather than repeat I17's generic missing-flip objection. It must solve the signed dominance/narrow-partition problem, not merely iterate the same two bands. General elementary unimodality has not been proved, and the unrestricted binary-weight mixing target is false. No substantial finding is ready for acceptance, and no count or shared-index change is requested.
