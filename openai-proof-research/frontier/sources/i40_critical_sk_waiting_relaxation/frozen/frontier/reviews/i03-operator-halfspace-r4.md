# Round 4 independent audit: explicit reflection half-spaces

Date: 2026-10-08. **Verdict: PASS for the ordinary invariant half-spaces of every specified $T_a=S+M_aV$, $1\leq a\leq2$ a.e. No substantive correction to that proof is required. FAIL for the candidate as an ordinary-ISP counterexample or as a substantial new-theorem success.** The entire specified family has nonzero proper closed invariant subspaces, explicitly of infinite dimension and codimension. Provider completion or failure was not used as mathematical evidence.

The original report is unchanged. I read `AGENTS.md`, `sources/upstream.json`, the iteration instructions, both requested round-2/3 reports, and the full round-3 half-space report. I independently checked the actual source definitions and the arguments below, reproduced the original experiment in an assigned-directory copy, and added independent exact checks. No agents, commits, staging, or shared-index edits were made. All writes are this review and `frontier/{sources,experiments}/i03_operator_r4/`.

## 1. Exact source contract and normalizer: PASS

The accepted revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The source is *Backward intertwiners and a transitive commutant*, `build/sections/weights.tex` and `intertwiner.tex`, especially `eq:a-plus`, `eq:a-minus`, `eq:bilateral-a`, the definition of $w_j$ inside `prop:fibers`, `eq:b-recursion`, `lem:normalization`, `eq:commuting-coefficients`, `eq:V-definition`, and `prop:V`. The actual `thm:direct-model` and companion `thm:main` were also read. Upstream theorem truth is an accepted premise, not the target of this review.

Use $E=L^2(\mathbb Z_2)$, $H=\ell^2(\mathbb Z;E)$, and write $M_g$ for base multiplication. For each fixed integer $j$, the dyadic formula makes $a_j$ bounded, hence $\beta_j=e^{-a_j}$ and its reciprocal bounded. The finite products
\[
 w_n=\prod_{k=0}^{n-1}\beta_k,\qquad
 w_{-n}=\prod_{k=-n}^{-1}\beta_k^{-1}\quad(n\geq1)
\]
therefore give boundedly invertible multiplication operators at every fixed coordinate. In particular $w_{-1}=e^{10}$, $w_1=e^{-10}$. This does **not** make their direct sum a bounded invertible operator on $H$.

The actual source normalizer is
\[
 L(x)=\sup_{j\in\mathbb Z}\widetilde b_j(x),\qquad
 b_j(x)=\widetilde b_j(x)/L(x)\quad(x\in X_*),
\]
with $1\leq L<\infty$ on the translation-invariant conull set $X_*$, and every $b_j=0$ off it. Nothing in the audit replaces $L$ by a finite maximum. All pointwise identities are enforced on a common conull set, taking countable translates when needed.

There is no output/input multiplier error:
\[
 (Tf)_j(x)=\beta_{j-1}(x)f_{j-1}(x)
   +a(x)b_{j+1}(x-1)f_{j+1}(x-1).
\]
Indeed $SM_a=M_aS$, because $S$ leaves the base unchanged, and $SV=VS$, so $S(M_aV)=(M_aV)S$. One must not infer $M_aV=VM_a$, which generally fails.

## 2. All-index normalization and boundary: PASS

Set
\[
 R_j(x)=\frac{b_j(x)w_j(x)}{w_{j-1}(x+1)}.
\]
The two recurrences give $R_{j+1}=R_j$ for **every integer** $j$. At $j=0$, $R_0=e^{-10}/L$. Thus the report's identity (4) has the right sign, base translation, constant, and negative-index convention.

Define
\[
 C=M_qU,\qquad (Ug)(x)=g(x-1),\qquad
 q(x)=\frac{e^{-10}a(x)}{L(x-1)}.
\]
Then $0<q\leq2e^{-10}$ a.e.; $C$ is bounded and injective, and $C^*=U^*M_q$ is injective, so $C$ has dense range. The same statements hold for positive powers. Surjectivity or a bounded inverse is not needed (and does not hold; see Section 7 below).

Writing $h_j=M_{1/w_j}f_j$ coordinate by coordinate gives exactly
\[
 k_j:=M_{1/w_j}(Tf)_j=h_{j-1}+Ch_{j+1}.
\]
No unweighted square summability of $h$ is assumed. For $h_{-j}=C^jh_j$, the negative coordinate at $j\geq2$ is
\[
 k_{-j}=C^{j+1}h_{j+1}+C^jh_{j-1}=C^jk_j.
\]
The separate boundary is essential and correct:
\[
 k_{-1}=h_{-2}+Ch_0=C^2h_2+Ch_0=Ck_1.
\]
The equality uses only powers of the single bounded operator $C$, not commutation of $C$ with the coordinate multipliers.

## 3. Closure, properness, orbit equality, and companion: PASS

Let $\Lambda_jf=M_{1/w_{-j}}f_{-j}-C^jM_{1/w_j}f_j$. Each $\Lambda_j:H\to E$ is bounded. Thus
\[
 \mathcal M_+=\bigcap_{j\geq1}\ker\Lambda_j
\]
is closed, without a uniform bound in $j$. It contains the full central coordinate $E\otimes e_0$, so is infinite-dimensional. The map $\Lambda_1$ is onto: set $f_{-1}=w_{-1}g$ and all other coordinates zero. Since it vanishes on $\mathcal M_+$, it induces a surjection $H/\mathcal M_+\to E$. This proves properness and infinite codimension. Boundedness of $T$ ensures the coordinate calculation actually gives $T\mathcal M_+\subseteq\mathcal M_+$ in $H$.

For orbit equality, the formula for a central input is the finite identity
\[
 h_{n-2\ell}={n\choose\ell}C^\ell g,\qquad0\leq\ell\leq n.
\]
Let $P_j(g)$ have normalized coordinates $g$ at $j>0$ and $C^jg$ at $-j$, and let $P_0(g)=g\otimes e_0$. Opposite coefficients match because
$C^{n-2\ell}{n\choose\ell}C^\ell g={n\choose\ell}C^{n-\ell}g$. The outer pair is $P_n(g)$; subtract the smaller pairs already obtained inductively, counting a central term only once. Hence every $P_n(g)$ is in the algebraic span of the central orbits. Symmetric coordinate truncation preserves the graph relations and converges in the **original** $H$-norm. This proves (8) exactly, with no finite-to-infinite cyclicity inference.

For
\[
 \mathcal M_-=\{f:h_0=0,\ h_{-j}=-C^jh_j\ (j\geq1)\},
\]
closedness follows in the same way. The free coordinate-one graph gives an infinite-dimensional subspace, and the surjective central-coordinate map annihilates it, giving infinite codimension. The boundary checks are
\[
 k_0=h_{-1}+Ch_1=0,\qquad k_{-1}=-C^2h_2=-Ck_1.
\]
The remaining indices obey the signed version of the previous calculation. Thus it is an invariant half-space, not merely $T^2$-invariant.

If $f$ is in both spaces, $h_0=0$ and $2C^jh_j=0$, so injectivity gives $f=0$. For density of their sum, approximate any negative normalized coordinate $v$ by $C^jr$ and split a desired positive coordinate $u$ into $(u+r)/2$ and $(u-r)/2$. These generate a plus and a minus pair whose sum is $(u,C^jr)$. Fixed-coordinate $w_{-j}$ preserves convergence. Approximate finitely many pairs and then use density of finite-coordinate vectors. No norm bound uniform in $j$, nor a bounded inverse of $C$, enters this argument.

## 4. Lattice and hyperinvariance assertions: PASS

Iterating $C$ gives exactly the coefficient in (7):
\[
 K_j=M_{w_{-j}}C^jM_{1/w_j},\qquad
 (K_jg)(x)=\frac{e^{-10j}w_{-j}(x)}{w_j(x-j)}
  \prod_{r=0}^{j-1}\frac{a(x-r)}{L(x-r-1)}\,g(x-j).
\]
For positive $a$, $K_j|g|=|K_jg|$, so $\mathcal M_+$ is closed under modulus and is a closed vector sublattice. The positive pair $f_1=1, f_{-1}=K_11$ belongs to it, whereas keeping only the negative coordinate gives a nonzero dominated vector outside it. Thus it is not an ideal.

Since $S\in\{T\}'$, hyperinvariance would imply $S$-invariance. But $S(g\otimes e_0)$ has only normalized coordinate $h_1=g$; for $g\ne0$, injectivity gives $Cg\ne0$, violating the graph. The nonhyperinvariance claim is exact. The companion also fails $S$-invariance: shifting its nonzero coordinate-$-1$ component produces a forbidden central component.

The optional $y=2x+j$ observation is consistent: a forward step adds one to $y$, and a backward/base-translation step changes it by $2-1=1$. It is not used as a claimed invertible global parameterization.

## 5. Noncommuting operator-valued extension: PASS, with scope explicit

Let $E\ne\{0\}$ be a Hilbert space. Assume $A,D\in B(\ell^2(\mathbb Z;E))$ are respectively forward/backward shifts, each forward block $A_j\in B(E)$ is boundedly invertible, and $AD=DA$. Set $W_0=I$, $W_{j+1}=A_jW_j$, extending backwards with the actual inverses. All fixed $W_j$ are boundedly invertible, even if their norms or inverse norms are unbounded in $j$.

The correct order of multiplication is
\[
 A_{j-1}D_j=D_{j+1}A_j,\qquad
 W_j^{-1}D_{j+1}W_{j+1}
 =W_j^{-1}A_{j-1}D_jW_j
 =W_{j-1}^{-1}D_jW_j=C.
\]
Thus $C=W_{-1}^{-1}D_0W_0$ is bounded and independent of $j$. The same coordinate formula $k_j=h_{j-1}+Ch_{j+1}$ follows. Neither pairwise commutation of the $A_j$, nor commutation of $C$ with $W_j$, is needed.

The closed invariant plus graph and its orbit equality therefore hold for arbitrary such $C$, including zero or singular $C$. The minus graph is also a closed invariant half-space. Even if $E$ is finite-dimensional, infinitely many independent finite pairs give infinite dimension; the first $N$ defect maps jointly surject onto $E^N$, giving unbounded finite codimension and hence infinite codimension. For the original infinite-dimensional $E$, the report's shorter single-coordinate arguments suffice.

**Scope guards, not errors in the stated result:** trivial intersection additionally needs injectivity of $C$; dense sum additionally needs dense range of $C$; lattice assertions require an order structure and modulus-preserving coefficients. Do not copy those supplementary claims into an unrestricted operator-valued theorem. The report only extends the construction (6), and is correct as written.

## 6. Ancillary analytic and literature checks

The noncompactness, non-Dunford–Pettis, and non-AM-compactness arguments in Section 6 pass. For the powers, the unique all-forward path supplies the coordinate $m$ multiplier $w_m$, bounded below at each fixed $m$, on a weakly null orthonormal base sequence.

The compact-domination arguments also pass. A positive compact block dominated by $M_dU$, after composition by the positive isometry $U^{-1}$, is compact and dominated by $M_d$. Support preservation forces it to be multiplication by $b=B1\in L^\infty$; a nonzero multiplier on nonatomic $L^2$ is not compact. Conversely a positive compact corner dominating $e^{-10}I$ contradicts compactness on a weakly null sequence of normalized disjoint positive indicators. The measurable-kernel obstruction for the identity follows using a countable generating algebra. None of these excludes all possible auxiliary commuting operators, as the report correctly warns.

The independent primary-source screen confirms the restrictions in the locally cached [Gillet paper](https://arxiv.org/abs/2409.14481v1), definition and Theorem 1.1/Corollary 1.2, and [Hu–Ji paper](https://arxiv.org/abs/2306.00387v1), Proposition 1.2 and following paragraph. Positivity relative to a specified basis is an extra condition; growth subspaces need not be closed. Search-indexed primary text of [Troitsky's Theorem 1](https://www.math.ualberta.ca/~vtroitsky/papers/math/done/positive-non-qnilp-is/positive-non-qnilp-is.pdf) confirms its compact-domination hypothesis. Direct opens of that PDF and the two cited publisher pages returned 403. I do not certify unavailable full texts or turn abstract-only access into full-text review; [primary_screen.json](../sources/i03_operator_r4/primary_screen.json) records the limits.

The pinned companion's `thm:main` concerns invariant projections in its specified factor. Its introduction explicitly distinguishes arbitrary invariant subspaces of the Hilbert representation. No duplicate reflection formula was found in the source sections actually read. A bounded external search did not identify an exact prior statement, which supplies no evidence of priority. The elementary commuting-shift argument remains a candidate obstruction, not a substantial new ISP theorem.

## 7. Additional proved refinement: the dense sum is not closed

This strengthens an issue left open by the report; it is not needed to repair it. For $m\geq1$, take the positive-measure cylinder
\[
 F_m=\{x:T_m(x)=2^m-1\},\qquad n=8^m.
\]
Every block $I_s$, $s\leq m$, wraps under $x\mapsto x+1$ on this cylinder. Thus $\Delta a_k=-100(2^s-1)$ on $I_s$. The exact source formula `eq:b-positive` yields
\[
 \log\widetilde b_n(x)
 =-\sum_{k=0}^{n-1}\Delta a_k(x)+a_{n-1}(x+1)-10
 \geq100(2^m-1)|I_m|
 =700(2^m-1)8^{m-1}.
\]
The boundary term is nonnegative; all omitted blocks contribute nonnegatively. Intersecting $F_m$ with $X_*$ preserves its positive measure. Consequently $\operatorname{ess\,sup}L=\infty$.

For every $1\leq a\leq2$, this forces $\operatorname{ess\,inf}q=0$. The multiplier $M_q$, and hence $C=M_qU$, has dense range but is not onto: otherwise its bounded inverse would force a positive essential lower bound for $q$. Since
\[
 K_1=e^{20}C,
\]
$K_1$ is likewise not onto. Choose $v\in E\setminus\operatorname{ran}K_1$ and let $f$ have only coordinate $f_{-1}=v$. Any sum $u_++u_-$ has coordinate
\[
 (u_++u_-)_{-1}=K_1((u_+)_1-(u_-)_1)\in\operatorname{ran}K_1.
\]
So this $f$ is not in $\mathcal M_++\mathcal M_-$. That sum is dense by Section 3 and proper by this argument; therefore it is **not closed**. In particular these spaces cannot be complementary eigenspaces of a bounded involution. This is an elementary additional deduction, with no literature-novelty claim.

## 8. Concrete next construction, with its remaining gap

A coordinate-dependent backward coefficient evades the mechanism just audited. Define a positive diagonal operator $R$ by
\[
 (Rf)_j=d_jf_j,\qquad d_j=\begin{cases}1,&j\leq0,\\2,&j\geq1,\end{cases}
 \qquad Q=S+RV.
\]
This uses the **actual** normalized $V$. It is bounded and positive. Its normalized formula is
\[
 k_j=h_{j-1}+d_jC_0h_{j+1},\qquad
 C_0g(x)=\frac{e^{-10}}{L(x-1)}g(x-1).
\]
Here $S$ and $RV$ do not commute: their coordinate-$j$ commutator contains $(d_{j-1}-d_j)\beta_{j-1}(x)b_j(x-1)$, nonzero at $j=1$. Thus this is outside the commuting-shift theorem.

It actually defeats the previous graphs, not just a hypothesis check. For the plus pair $h_2=g, h_{-2}=C_0^2g$, other coordinates zero, the output has $k_{-1}=C_0^2g$ but $C_0k_1=2C_0^2g$; the minus pair fails with the corresponding sign. More generally, suppose a graph ansatz $h_{-j}=B_jh_j$ allows every finite pair and arbitrary $h_0$. The central input forces $B_1=C_0$; a coordinate-two pair forces $B_2=2C_0^2$; a coordinate-one pair, tested at output $-2,2$, forces $B_2=C_0B_1=C_0^2$. Injectivity of $C_0^2$ contradicts these requirements. This excludes that entire centered full-pair graph ansatz, not all invariant-subspace constructions.

A useful property survives **without commutation**. In the positive-operator order,
\[
 0\leq Q\leq S+2V=T_2,\qquad0\leq Q^n\leq T_2^n.
\]
Using the previously audited Gaussian estimate for $T_2$, norm monotonicity on $L^2$ gives
\[
 \|Q^n\|\leq e^{5000}3^n e^{-n^2/2}.
\]
Hence $Q$ is norm-quasinilpotent. The no-invariant-ideal argument also survives: a $Q$-invariant closed ideal is invariant under $S$ and $RV$ by positivity and solidity, hence under $V$ by the bounded diagonal $R^{-1}$; accepted transitivity then makes it trivial.

These are proved initial properties, not an ISP answer or an established new substantial case. The empty-point-spectrum arguments have not been re-established here for $Q$, nor have arbitrary invariant half-spaces been classified or excluded. The next decisive task would be an ordinary invariant-subspace analysis of this exact $Q$, including graph or cyclic-closure constructions beyond the excluded ansatz. It would be invalid to infer success from Gaussian decay, absence of ideals, or failure of one reflection construction.

## 9. Reproducibility and disposition

Run from the repository root:

```sh
python frontier/experiments/i03_operator_r4/reproduce_original.py
python frontier/experiments/i03_operator_r4/independent_checks.py
python frontier/experiments/i03_operator_r4/verify_sources.py
```

The original script copy is byte-identical and its [output](../experiments/i03_operator_r4/output.json) reproduces byte-for-byte: 76,864 integer-log identities, 21 block identities, 70 reflection relations, and 11 central orbits. It writes only inside the review's assigned directory.

The [independent script](../experiments/i03_operator_r4/independent_checks.py) uses source drift formulas to check 262,432 all-index log identities for bases $-16,\ldots,15$ and indices $-4100,\ldots,4100$, including both signs and block boundaries through (4096). It also checks four explicit lower bounds for $L$, and five **bounded periodic** operator-valued models with truly noncommuting weights, including invertible, singular, nilpotent and zero $C$: 315 block identities, 770 reflection relations, 110 boundary cases, 65 original-coordinate orbit identities and 65 triangular extractions. Both newly reached outer coordinates are retained. The asymmetric-coupling failure is also checked exactly. Results: [independent_output.json](../experiments/i03_operator_r4/independent_output.json). These are transcription/adversarial tests; the universal and infinite-dimensional conclusions rest on the proofs above.

All 18 round-3 manuscript files match their SHA-256 hashes, Git-blob hashes, and `sources/preprints-tree.json` entries. Fresh downloads from all 18 immutable URLs match byte-for-byte. Both successful literature PDFs match their hashes and sizes; all five prior recorded input hashes matched at verification time. [verification.json](../sources/i03_operator_r4/verification.json) records each comparison; [input_manifest.json](../sources/i03_operator_r4/input_manifest.json) records the reviewer inputs as observed. Source sections are cached in the assigned directory under the manifest's pinned filenames. The parent updated frontier/iterations/README.md after source verification; the other recorded inputs, including the original report, remained byte-identical at the final check. These records concern the bytes actually reviewed.

**Exact correction list:** no mathematical correction is needed for (1)–(10) or the stated abstract extension. Preserve the extra hypotheses when extending intersection/density/lattice claims, and do not use the failed provider status as evidence either for or against the proof. Section 7 above additionally settles nonclosedness of the sum. The report's stray escaped dollar before its proof square is only typographical.

**Integration decision:** close the ordinary-subspace question for the exact $T_a$ family as resolved affirmatively. Do not increase the substantial-new-finding count. The asymmetric $Q$ is a concrete subsequent research target with a clearly stated unclosed ordinary-subspace gap; the broader research objective remains open.
