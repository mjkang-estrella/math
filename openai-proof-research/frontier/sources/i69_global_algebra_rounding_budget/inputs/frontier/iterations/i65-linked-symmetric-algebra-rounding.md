# I65 — linked symmetric algebra rounding after R014

**Disposition: AR remains unproved and unrefuted. No candidate for acceptance or count increment.** This report develops two constructions, a linked channel/positive-algebra approach and global-maximizer deflation, against an actual fully symmetric normalized family. The family disproves three proposed intermediate estimates, including a constant adaptive associator charge for greedy deflation. It is explicitly close to an odeco tensor in normalized distance, so none of these is a counterexample to AR. A separate compression construction and an approximate-normalization rounding lemma are proved below; both are technical partials, not a substantial finding.

Author analytic conclusions and reproducible evidence are separate. The proofs below are author claims checked by direct derivation; they have not received the parent's fresh independent proof/significance reviews. `verification.json` reports only provenance and finite diagnostic PASS. It cannot certify a universal theorem or novelty.

## 1. Contract, premises, and precise targets

The immutable source revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. All its statements **and lower proof operations** are stipulated true. Nothing here audits their truth. The authoritative tree contains 13,223 entries and 749 manuscripts; the fixed ignored corpus contains 9,340 files. The tree has 10,373 blobs in total: the 1,033 outside the fixed corpus are separately listed in `tree-outside-corpus.json`. Corpus search coverage is not claimed for those extra PDFs, scripts, and other files. The older truncated tree/catalogue is not authoritative.

The exact full I65 assignment, including the original I61/I59/I53 assignments and objections, is frozen in `../sources/i65_linked_symmetric_algebra_rounding/brief.txt`, extracted without rewriting from the frozen parent task JSON. Full I61, I59, I53, I55, I56, I63, I64, and R014 acceptance are frozen in `inputs/`. Prior evidence is hash-referenced in `prior-hashes.json`, not recursively copied. Only the four designated front-page ledgers are treated as mutable. No prior seal was refreshed. No shared file, prior report, index, commit, stage, or publication was changed by this task; no agent was spawned.

Let (V=\mathbb R^m), (T\in\operatorname{Sym}^3V), and
\[
 (T_x)_{ij}=T(e_i,e_j,x),\quad B_T=\sum_{r=1}^mT_{e_r}^2,
 \quad E(T)=\sum_{r,s=1}^m\|[T_{e_r},T_{e_s}]\|_F^2.
\]
All matrix/tensor Frobenius norms are unnormalized, and all ordered pairs (r,s) are included. Put
\[
 \beta(T)=\|B_T-I\|_F^2,\quad \varepsilon(T)=(\beta(T)+E(T))/m,
 \quad d(T)^2=\inf_{(u_i)\text{ ONB}}\left\|T-\sum_i u_i^{\otimes3}\right\|_F^2.
\]
Signs are part of the orthonormal basis. **AR\(_K\)** asks, for every fixed finite (K>0), for a function \(\rho_K(t)\to0\) as \(t\downarrow0\), independent of (m\ge1), such that (B_T\le KI\) implies (d(T)^2/m\le\rho_K(\varepsilon(T))\). Exact (B_T=I) is a genuinely useful restricted target. This report proves neither target. For (K<1), arbitrarily small deficit is impossible since \(\beta/m\ge(1-K)^2\); the interesting small-deficit range includes (K\ge1\).

Three screened mechanisms were:

1. Round the linked rank-(m) Kraus-span projection to a dephasing using positivity, an approximate unit, or a low-rank PPT theorem. The linkage is used throughout §4; two strong intermediate estimates fail on the actual linked family.
2. Greedily split global cubic maximizers and charge every mixed term to the original associator. Section 5 computes the complete restriction chain, without reinstating (B=I\); a constant charge fails by a logarithm.
3. Construct a global basis from a nearly square coordinate dilation. Section 6 gives a full estimate if that dilation is supplied. Producing such a dilation for a general AR tensor is unpaid, and is not inferred from a matrix-family theorem.

The accepted CE result is not reopened. R014 consists of CE61's compatibility bridge, with the cap-preserving repair technical and included in the same finding. I63's original-proof PASS and I64's substantial verdict, and the parent's reproduced checks, are accepted at their actual scopes. I53's fixed-dimensional result and I56's local transverse estimate are not renamed or nominated.

## 2. Input applicability and primary/source comparison

### 2.1 Inherited interfaces, independently checked as used

For full symmetry, (B_T) is also the Gram matrix of the slices. With \(\Delta x=T_x\), this says \(\Delta^*\Delta=B_T\). Define maps on **all** (m\times m) matrices
\[
 P_T(X)=\sum_r\langle T_r,X\rangle_F T_r=\Delta\Delta^*(X),
 \qquad \Phi_T(X)=\sum_rT_rXT_r.
\]
The contraction identities give
\[
 \|P_T\|_{\rm HS}^2=\|\Phi_T\|_{\rm HS}^2=\operatorname{tr}B_T^2,
 \qquad \|\Phi_T-P_T\|_{\rm HS}^2=E(T).                 \tag{2.1}
\]
For example, expanding a commutator gives (2\operatorname{tr}(T_r^2T_s^2-T_rT_sT_rT_s)\); summing matches the expansion of the last norm. At (B=I), \(P_T\) is an orthogonal rank-(m) projection and \(\Phi_T\) is a self-adjoint unital trace-preserving completely positive contraction. These identities receive **analytic applicability PASS**, not a new finding. The independent rational checks include every matrix unit and the partial-transpose indexing below.

I61's spectral projection \(R=1_{[1/2,\infty)}(\Phi_T)\) and bounds \(\|R-P_T\|_{\rm HS}\le7\sqrt E\), \(|\operatorname{rank}R-m|\le49E\), are used only as motivation. Neither positivity nor multiplicative closure of (R\) is inferred. The inherited near-dephasing implication at (B=I\) is superseded only for approximate normalization by the technical §3 lemma. The inherited maximizer identities are derived again for the entire exact family in §5.

**Other input verdicts:** I59 retained slack/Hodge/Mills coefficient inputs and I61 cap repair/entropy reduction are accepted via R014 and I63 at the smooth source class and fixed-cap scopes actually reviewed. No fresh independent re-review of the whole CE proof is claimed. I55's original PASS does not make I53 dimension uniform. I56's local total-distance entrance does not bound normalized distance in growing dimension. These scope restrictions are preserved.

### 2.2 Actual pinned operations

`pins.json` records SHA-256, Git blob, and exact pinned raw URL for 26 source files. `passages.json` freezes the actual read passages with line ranges. In particular:

* The sharp-entropy `rigidity.tex` uses exact compatibility jets to force slice commutation and one common basis, and uses compactness/forward Lipschitz operations at their stated scope. The retained matrix slack and nonlinear normalization do not contain a dimension-uniform algebra-rounding operation. The full original I59/I61 reductions preserve this distinction.
* Mahler `06-linear-equality.tex`, equality passage, identifies a normalized spectral moment with a sum of commutator squares; **vanishing** gives one simultaneous eigenbasis and then coordinatewise projection. Its cone deficit and exact equality operation are not a quantitative AR entrance.
* Universal strong Kadison–Kastler `02-foundations.tex` uses cb/Haagerup multiplication estimates near an already supplied von Neumann algebra and representation. AR supplies normalized Hilbert–Schmidt error of a linked tensor, not cb closeness of an associative multiplication. The relevant source operation is true, but its entrance is missing.
* Near-inclusions `obstruction.tex` works with operator-norm clock/shift obstructions and a common-corner conclusion when the requisite commuting algebras are already available. It neither rounds a Kraus span into an algebra nor removes the norm mismatch.
* Tracial-projection methods `10_unital_averaging.tex` uses supplied projections, nuclear/order-zero homomorphism replacement, fourth-moment control, and clipping. Its lower proof operations are stronger than a bare theorem slogan, but still presuppose the algebra/projection data which the AR route has yet to construct.

Additional pinned companion files are retained for comparison/provenance, not represented as all read line by line in this iteration. The finite corpus discovery searches replay as **line multisets** on the fixed 9,340-file domain. Their 138 algebra, 569 channel, and 9 stability matches are bounded discovery evidence, not a completeness or priority theorem.

### 2.3 Current primary literature, including the family antecedent

Fresh HTTP response bodies/headers, versions, extraction stderr, and UTC retrieval times are in `primary/manifest.json`: 20 successful responses (nine arXiv abstract/PDF pairs and two author/publisher PDFs), no failed HTTP retrieval in that batch. The server's UTC date was October 10, 2026, corresponding to the session's October 9 Pacific date. Current versions refer to what these responses served; the verifier does not make a live version claim. One PDF extraction font warning is retained. Two early discovery search displays were not separately archived; no theorem depends on them. Three subsequent discovery response records and all primary bytes used below are frozen.

* [Fox, *Commutative algebras with nondegenerate invariant trace form and trace-free multiplication endomorphisms*, arXiv:2004.12343v2](https://arxiv.org/abs/2004.12343): Definition 3.4, Corollary 3.7, Example 3.8, Remark 3.12, and Lemma 3.16 explicitly study the simplicial algebra, its associator, positive Killing form, idempotents, and multiplication spectra. Fox attributes the algebra to earlier work of Griess/Harada. Thus the family below is **old**, not a new algebra. Sections 4–5 are direct computations of its relevance to this particular proposed rounding interface. No priority claim is made for those computations either. Fox's exact projective associativity/unitalization results do not already give a quantitative normalized-HS AR theorem. The sectional-nonassociativity v3 and Steiner-algebra v1 companions were retrieved for discovery; their results are not imported.
* [Bansil–Kachkovskiy, arXiv:2608.31000v1](https://arxiv.org/abs/2608.31000): Theorem 1.1 has the pair (1/3) norm exponent, Theorem 1.3 has matrix-count loss, and Corollary 1.4's iteration exponent deteriorates with the number of matrices. The actual partition operation in Lemma 2.1 replaces one matrix by blockwise spectral averages and the others by block compressions; the subsequent gap deletion/induction controls those operations. Applying it separately to (m) slices does not preserve cubic symmetry or provide a uniform-in-(m) family bound. Matrix-size independence alone is insufficient.
* [Kitaev, arXiv:2405.02434v2](https://arxiv.org/abs/2405.02434): the channel-to-algebra entrance is small cb idempotence error; the approximate (C^*\)-algebra axioms include norm and unit conditions. Its spectral projection can lose complete positivity. No cb entrance is deduced here from (2.1).
* [Coecke–Pavlovic–Vicary, arXiv:0810.0812v1](https://arxiv.org/abs/0810.0812), and [Boralevi–Draisma–Horobeț–Robeva, arXiv:1512.08031v1](https://arxiv.org/abs/1512.08031): exact special commutative dagger-Frobenius structures/exact positive associative multiplication yield orthogonal bases/decompositions. The actual simple-ideal splitting proof assumes exact associativity. No quantitative approximate classification is invoked.
* [Biaggi–Draisma–Seynnaeve, published Proposition 4.1](https://rendiconti.dmi.units.it/volumi/54/017.pdf): the tangent calculation at the coordinate cubic is already explicit. It underlies the I56 technical assessment. It gives no growing-dimension normalized entrance; its complex indefinite examples are not real Euclidean AR examples.
* [Auddy–Yuan, arXiv:2007.09024v2](https://arxiv.org/abs/2007.09024): Theorem 3.1 and its polar-factor proof start with a supplied factor decomposition and singular-value control. Section 6 below is another elementary polar-factor construction with supplied coordinate dilation; the hard factor-existence problem is not solved by it.
* [Poinsot, author version, §3.4](https://lipn.fr/~poinsot/Articles/Hilbertian_Frobenius_algebras_rev.pdf): “approximate units” approximate the identity inside an **exact** Hilbertian Frobenius algebra. They are not a theorem on approximately associative multiplications. Section 4 gives a linked obstruction to the direct unit-recovery substitute.
* [Horodecki–Lewenstein–Vidal–Cirac, arXiv:quant-ph/0002089v1](https://arxiv.org/abs/quant-ph/0002089): the rank-(N) PPT separability theorem requires exact PPT. Its canonical-form/filtering and rank-reduction proof does not control a dimension-uniform repair from the norm in (2.1). Section 4 computes the failed trace-negativity entrance explicitly.

These are applicability comparisons, not audits of external proofs. No external theorem is needed for the elementary partial results below. No MathDB score or unobserved priority/significance claim is supplied.

## 3. Technical partial: dephasing rounding without exact normalization

**Proposition 3.1.** For every real fully symmetric cubic (T), every orthonormal basis (U\), and its dephasing (D_U(X)=\sum_i\langle u_i,Xu_i\rangle u_iu_i^T\), there are signs \(\sigma_i\in\{-1,1\}\) such that
\[
 \left\|T-\sum_i\sigma_i u_i^{\otimes3}\right\|_F^2
 \le\frac94\|P_T-D_U\|_{\rm HS}^2.                    \tag{3.1}
\]
No cap, invertibility, or exact (B=I\) assumption is needed.

**Proof.** Work in basis (U\). Write (a=\sum_{i\ne j,r}T_{ijr}^2\) for off-diagonal slice mass and (M=\sum_{(i,j,r)\ne(i,i,i)}T_{ijr}^2\) for all non-pure-diagonal tensor mass. Full symmetry gives (M\le3a/2\): a repeated-index triple contributes three copies to (M\), two to (a\); a distinct-index triple contributes equally. Since \(\langle P_T,D_U\rangle=\sum_{i,r}T_{iir}^2=\operatorname{tr}B-a\),
\[
 b:=\|P_T-D_U\|_{\rm HS}^2=\beta+2a.                  \tag{3.2}
\]
For each (i\), put (z_i=|T_{iii}|\) and (h_i=B_{ii}-z_i^2\ge0\). Their sum is (M\). The scalar inequality
\[
 (z-1)^2\le(z^2+h-1)^2+2h\qquad(z,h\ge0)             \tag{3.3}
\]
follows because at (h=0\) the right side minus the left side is (z(z+2)(z-1)^2\), and its derivative in (h\) is (2(z^2+h)\ge0\). Choose \(\sigma_i\) with the sign of (T_{iii}\), arbitrarily if zero. The squared tensor error is at most
\[
 M+\sum_i(z_i-1)^2\le\beta+3M\le\beta+\tfrac92a
 =\tfrac94b-\tfrac54\beta\le\tfrac94b.
\]
This proves the claim, including zero diagonal entries and singular (B\). ∎

At (B=I\), (z_i\le1\) and \((1-z_i)^2\le1-z_i^2=h_i\), giving the inherited sharper (3b/2\). Conversely, under (B\le KI\), any odeco tensor (D\) satisfies
\[
 \|P_T-P_D\|_{\rm HS}\le(\sqrt K+1)\|T-D\|_F,         \tag{3.4}
\]
by (AA^*-CC^*=(A-C)A^*+C(A-C)^*\), \(A=\Delta_T\), \(C=\Delta_D\), with operator norms \(\sqrt K\) and 1. Thus finding a dephasing for the **original** (P_T\) would avoid symmetry-destroying normalization. Equations (3.1)/(3.4) are a technical equivalence/extension, not an independent proof of the missing dephasing step. Normalizing one tensor slot by (B^{-1/2}\) is still not licensed.

## 4. Construction A: an actual linked family and channel/positive-algebra tests

### 4.1 Normalized simplicial multiplication

For each (m\ge2\), put (n=m+1\), (V=\mathbf1^\perp\subset\mathbb R^n\), (Q=I-\mathbf1\mathbf1^T/n\), and (s=\sqrt{n/(n-2)}\). Define
\[
 T_m(x,y,z)=s\sum_{a=1}^n x_ay_az_a\quad(x,y,z\in V),
 \qquad x*y=sQ(x\circ y).                             \tag{4.1}
\]
This is the classical simplicial algebra, in the normalization relevant here. It is manifestly fully symmetric and real.

For completeness, its ambient compressed components, divided by (s\), are
\[
 \tau_{ijk}=\delta_{ij}\delta_{ik}
 -\frac{\delta_{ij}+\delta_{ik}+\delta_{jk}}n+\frac2{n^2}.
                                                               \tag{4.2}
\]
The slices on (V\) are (T_x=sQ\operatorname{diag}(x)Q|_V\). Direct contraction, using \(\sum x_a=0\), gives
\[
 \operatorname{tr}_V(T_xT_y)
 =s^2(1-2/n)\langle x,y\rangle=\langle x,y\rangle,
 \qquad\operatorname{tr}_V T_x=s(1-1/n)\sum_a x_a=0.
\]
Hence (B_{T_m}=I_V\), \(\|T_m\|_F^2=m\), and the slice span is trace-free. Expanding the two products (Q\operatorname{diag}(x)Q\operatorname{diag}(y)Q\) in opposite orders gives
\[
 [T_x,T_y]=-\frac{xy^T-yx^T}{m-1}\quad\hbox{on }V.
                                                               \tag{4.3}
\]
For an orthonormal basis, each ordered unequal pair has squared commutator norm (2/(m-1)^2\). Consequently
\[
 E(T_m)=\frac{2m}{m-1},\qquad\varepsilon(T_m)=\frac2{m-1}\longrightarrow0.
                                                               \tag{4.4}
\]
This meets the exact linked full-symmetry, cap (K=1\), and normalized-deficit hypotheses. It is stronger as a method test than an arbitrary matrix channel example.

### 4.2 Exact unit recovery fails

For every (v\in V\), trace-freeness and slice isometry imply
\[
 \|T_v-I\|_F^2=m+\|v\|^2,
 \qquad\inf_v\|T_v-I\|_F^2/m=1.                       \tag{4.5}
\]
Also \(\|T_v-I\|_{\rm op}\ge1\), by its trace. Thus normalized associator error tending to zero does **not** recover an approximate unit inside the original multiplication. It does not even ensure that the scalar identity direction is nearly in its slice span: (P_T(I)=0\), whereas \(\Phi_T(I)=I\).

There is no conflict with a nearby odeco tensor. The contraction sending a cubic to its trace vector, or testing multiplication at an odeco unit of length \(\sqrt m\), is not uniformly controlled by normalized cubic error in the needed way. Replacing the multiplication before seeking its unit remains possible. Poinsot's exact-algebra theorem does not repair (4.5).

### 4.3 Channel spectrum and the correct partial transpose

A contraction of (4.2), restricted to matrices on (V\), yields
\[
 \Phi_T(X)-P_T(X)=\frac{\operatorname{tr}(X)I-X}{m-1}.   \tag{4.6}
\]
One can verify the contraction without choosing a basis of (V\): its ambient four-index right side is
\((Q_{ij}Q_{kl}-Q_{ik}Q_{jl})/(m-1)\), on compressed matrix units. This also independently verifies the operator formula. Since (P_T\) is the projection onto an (m\)-dimensional trace-free symmetric space \(\mathcal V\), the eigenvalues of \(\Phi_T\) are

| Subspace | Dimension | Eigenvalue |
|---|---:|---:|
| scalar identity | 1 | 1 |
| \(\mathcal V\) | (m\) | \((m-2)/(m-1)\) |
| remaining matrices | (m^2-m-1\) | \(-1/(m-1)\) |

In particular \(\|\Phi_T-P_T\|_{2\to2}\ge1\) for every (m\), even though its normalized HS square tends to zero. The spectral rounding cannot justify replacing normalized HS control by operator/cb control on this linked example.

For the proposed positive-state route, regard (P_T\) instead as a bipartite operator with entries (P_{ij,kl}=\sum_r T_{ijr}T_{klr}\). Its partial transpose satisfies
\[
 (P_T^\Gamma)_{ij,kl}=P_{il,kj},\qquad
 P_T^\Gamma=\Phi_T\circ\mathsf{transpose}.             \tag{4.7}
\]
It is **not** \(\Phi_T\) on the whole matrix space. As (P_T\) kills skew matrices, the HS permutation still gives \(\|P_T^\Gamma-P_T\|_{\rm HS}^2=E(T)\). But its spectrum is

| Subspace | Dimension | Eigenvalue of \(P_T^\Gamma\) |
|---|---:|---:|
| scalars | 1 | 1 |
| \(\mathcal V\) | (m\) | \((m-2)/(m-1)\) |
| symmetric trace-free complement | \((m-2)(m+1)/2\) | \(-1/(m-1)\) |
| skew matrices | \(m(m-1)/2\) | \(1/(m-1)\) |

Therefore
\[
 \frac{\operatorname{tr}(P_T^\Gamma)_-}{m}
 =\frac{(m-2)(m+1)}{2m(m-1)}\longrightarrow\frac12.    \tag{4.8}
\]
The normalized HS deficit does not give a vanishing normalized **negative-part trace after partial transpose**, even with exact linkage. So the exact low-rank PPT theorem has no entrance from that proposed trace-negativity estimate. This is not a lower bound on distance to PPT states before partial transpose: partial transpose does not preserve trace norm. It does not rule out an HS repair or AR. At (m=2\) the negative sector has dimension zero, consistent with the formulas.

### 4.4 All-orientation distance and an explicit good orientation

The global positive cubic maximum on the unit sphere of (V\) is
\[
 c_m=\sqrt{(m-1)/m}.                                  \tag{4.9}
\]
To prove this, apply Lagrange multipliers to \(\sum x_a^3\) with \(\sum x_a=0\), \(\sum x_a^2=1\). The constraint gradients are independent, and every coordinate satisfies one quadratic, hence has one of two values. If (k\) coordinates have the positive value, the objective is
\((n-2k)/\sqrt{nk(n-k)}\). Its squared magnitude is (n/[k(n-k)]-4/n\), maximized at (k=1\) or (n-1\). Choose the positive sign and multiply by (s\). This proves (4.9), including (m=2\).

For **every** orthonormal basis,
\[
 \left\|T_m-\sum_i u_i^{\otimes3}\right\|_F^2
 =2m-2\sum_iT_m(u_i,u_i,u_i)
 \ge2m(1-c_m)=\frac2{1+\sqrt{1-1/m}}\longrightarrow1. \tag{4.10}
\]
This is a positive **total** lower bound against all orientations; divided by (m\), it tends to zero. It is not the lower bound required to refute AR.

There is also a uniform total upper bound. Set
\[
 a=(1/\sqrt{m+1}-1)/m,\quad b=-1/\sqrt{m+1},\quad
 u_i=e_i+a\sum_{j=1}^m e_j+b e_{m+1}\quad(1\le i\le m).
\]
Their coordinate sums vanish, and (\langle u_i,u_j\rangle=\delta_{ij}+2a+ma^2+b^2=\delta_{ij}\). For all (i\),
\[
 T_m(u_i,u_i,u_i)=d_m
 =s(1+3a+3a^2+ma^3+b^3).
\]
Thus
\[
 d(T_m)^2\le2m(1-d_m)=4+O(m^{-1/2}).                 \tag{4.11}
\]
The limit follows from (a=-m^{-1}+O(m^{-3/2})\), (b^3=O(m^{-3/2})\), (s=1+m^{-1}+O(m^{-2})\); these are expansions of the displayed elementary formulas. Section 6 gives an independent bounded-total-error proof without asymptotics. Consequently the actual family satisfies (d(T_m)^2/m\to0\). All its obstructions above concern proposed methods.

## 5. Construction B: full greedy deflation and a false charge inequality

Run the I61 global-maximizer deflation on (T_m\), retaining the restricted tensor after each removal and **never renormalizing it**. Every global positive maximizer is a simplex-vertex direction, by the equality cases in the proof of (4.9); choices are equivalent by coordinate permutations. The recursion below therefore covers every choice of positive global maximizer.

At current dimension (d\ge2\), the restricted tensor is (t_dT_d\), where
\[
 r=\frac{m+1}{m-1},\qquad t_d^2=r\frac{d-1}{d+1}.     \tag{5.1}
\]
It starts with (t_m=1\). To see the restriction directly, choose the positive vertex with last coordinate \(\sqrt{d/(d+1)}\) and all other coordinates \(-1/\sqrt{d(d+1)}\). Its orthogonal complement inside \(\mathbf1^\perp\) consists precisely of vectors whose last coordinate is zero and whose other coordinates sum to zero. Restricting (4.1) leaves the same coordinatewise cubic coefficient. Comparison of (s_d^2=(d+1)/(d-1)\) and (s_{d-1}^2=d/(d-2)\) gives
\[
 t_{d-1}^2=t_d^2\frac{(d-2)(d+1)}{d(d-1)}.
\]
This telescopes to (5.1); at (d=2\) the one-dimensional remainder is zero. We do not define (T_1\) by a singular normalization.

In the split (\mathbb Rv\oplus v^\perp\), the maximizing slice is \(\operatorname{diag}(c_d,H_d)\), with
\[
 c_d=t_d\sqrt{(d-1)/d},\qquad
 H_d=-\frac{t_d}{\sqrt{d(d-1)}}I_{d-1}.
\]
The cap and small-(c\) interfaces are explicit:
\[
 B_{\rm current}=t_d^2I,\quad\frac13\le t_d^2\le1,
 \quad c_d^2\ge\frac16\quad(d\ge2).
\]
After deletion,
\[
 B_{\rm remainder}=t_d^2I-2H_d^2=t_{d-1}^2I.         \tag{5.2}
\]
Thus exact normalization is lost exactly as warned in I61, even while a uniform cap persists. The final zero direction is paid below.

The mixed tensor mass removed at this step is
\[
 3\|H_d\|_F^2=\frac{3t_d^2}{d},
\]
because there are three locations of the distinguished index, and (T(v,v,w)=0\). The contracted associator used by the proposed deflation charge is
\[
 a_d=\|H_d^2-c_dH_d\|_F^2
 =\frac{t_d^4}{d-1}=r^2\frac{d-1}{(d+1)^2}.          \tag{5.3}
\]
Here each eigenvalue of (H_d^2-c_dH_d\) is (t_d^2/(d-1)\), so no unrecorded remainder is present.

**Proposition 5.1 (method obstruction).** There is no numerical (C\) such that this greedy recursion always satisfies
\(\sum_d a_d\le CE(T_{\rm initial})\), even if the initial tensor has (B=I\), all current tensors have cap 1, and all selected maxima until the final zero direction obey (c\ge1/\sqrt6\).

**Proof.** On this family,
\[
 \sum_{d=2}^m a_d=r^2\sum_{j=3}^{m+1}\left(\frac1j-\frac2{j^2}\right)
 =\log m+O(1),
 \qquad E(T_m)=2m/(m-1)\le4.
\]
The hypotheses were verified above. ∎

This specifically rules out the naive constant adaptive-charge estimate left unpaid in I61; it does not rule out a different, weaker normalized accounting. Moreover, its greedy **output error** really grows logarithmically. Orthogonality of the separated tensor components gives the exact error of the resulting signed coordinate cubic:
\[
 \operatorname{cost}_{\rm greedy}
 =3r\sum_{d=2}^m\frac{d-1}{d(d+1)}
 +1+\sum_{d=2}^m\left(1-\sqrt r\frac{d-1}{\sqrt{d(d+1)}}\right)^2.
                                                               \tag{5.4}
\]
The term 1 pays the final zero direction. The mixed sum equals
\(3r(H_m-2+2/(m+1))\). The remaining sum is uniformly bounded: (0\le1-c_d\le1-(d-1)/\sqrt{d(d+1)}\le2/d\), so it is at most (1+4\sum_{d=2}^\infty d^{-2}\). Thus
\[
 \operatorname{cost}_{\rm greedy}=3\log m+O(1),
 \quad\hbox{whereas the explicit global basis in §4 costs }4+o(1).
\]
There is no universal linear-in-original-residual guarantee for this greedy algorithm. The normalized greedy error nevertheless tends to zero. In particular, this calculation does not exclude a modulus of order \(\varepsilon\log(1/\varepsilon)\), a weaker power, a blockwise algorithm, or AR itself.

For a general tensor, proving only a one-step mixed-loss inequality is consequently insufficient. A future deflation proof must charge current associators and normalization loss together, with a budget allowing this logarithmic chain, and must handle the small-(c\) branch absent from this example. A conceivable entrance is an entropy-weighted bound on total mixed loss, for example (C_K E\log(e+m/E)\) in an exactly normalized capped input, plus a paid normalization/terminal-diagonal budget. Such an estimate is **not proved here**; its logarithm would be compatible with this family. It is more specific than asserting AR as a lemma, but is still a missing global inequality.

## 6. A complete restricted global construction from a supplied dilation

**Proposition 6.1.** Let (H\subset\mathbb R^N\) have dimension (m\ge1\) and codimension (k=N-m\). Let (Q_H\) be its orthogonal projection and
\(S=Q_H^{\otimes3}\sum_{j=1}^N e_j^{\otimes3}\), viewed as a tensor on (H\). Then there is an orthonormal basis (U\) of (H\) with
\[
 \|S-D_U\|_F^2\le16k.                                \tag{6.1}
\]
For any real (s\), the same basis gives
\[
 \|sS-D_U\|_F^2\le32s^2k+2m(s-1)^2.                 \tag{6.2}
\]

**Proof.** Select any (m\) of the coordinate indices. Put (a_i=Q_He_i\) for these indices, and regard (A=(a_i)\) as a square map from \(\mathbb R^m\) to (H\). Its singular values satisfy (0\le s_i\le1\). Moreover,
\[
 m-\|A\|_F^2=\sum_{\text{discarded }j}\|Q_He_j\|^2\le k.
\]
Take a full SVD and an orthogonal polar completion (U\); a kernel causes no problem because domain and codomain have the same dimension. Then
\[
 \|A-U\|_F^2=\sum_i(1-s_i)^2\le\sum_i(1-s_i^2)\le k.
\]
The (k\) discarded pure coordinate tensors are orthonormal before projection, so their projected sum has norm at most \(\sqrt k\). For the selected tensors, telescope each (a_i^{\otimes3}-u_i^{\otimes3}\) in the three slots. Each sum in the telescope has norm at most \(\|A-U\|_F\). Indeed, the matrix of pairwise tensor factors is one of \((A\otimes A)J\), \((U\otimes A)J\), \((U\otimes U)J\), where (Je_i=e_i\otimes e_i\) is an isometry. Each has operator norm at most 1, and flattening the remaining factor bounds the Frobenius product norm. Therefore \(\|S-D_U\|_F\le\sqrt k+3\sqrt k\). This proves (6.1). Finally (sS-D_U=s(S-D_U)+(s-1)D_U\), with \(\|D_U\|_F^2=m\), proves (6.2). ∎

This includes the simplicial family with (N=m+1\), (k=1\), and (s=\sqrt{(m+1)/(m-1)}\), independently proving bounded total error. It also handles arbitrary supplied subspaces, rank-deficient selected frames, and zero codimension. It is a preassigned-factor/dilation result with an elementary polar proof, not the missing AR mechanism. Neither (2.1) nor the reviewed source operations have furnished such a near-square dilation for arbitrary (T\). No conclusion is drawn for unknown factors, arbitrary block size, or many-matrix simultaneous diagonalization.

## 7. Entropy consequences and preserved obstructions

No new capped entropy stability law is claimed: the AR hypothesis needed to finish it is still unpaid. To fix the intended conditional scope, write (u=\delta/m\) for an actual smooth source-class input with original coefficient cap (K\). R014 supplies
\[
 \eta\le\chi_K(A_Ku),\quad \beta_{\rm coeff}\le2000u/c_K,
\]
and a fully symmetric repaired tensor (Z\) with cap (4K\), normalized repair distance at most (26\eta\), and normalized algebra residual at most
\[
 e_Z=4000u/c_K+(2+2340K)\eta.
\]
If AR\(_{4K}\) were proved, the triangle-square inequality gives coefficient-to-odeco cost at most
\[
 52\eta+2\rho_{4K}(e_Z).
\]
The already accepted I61 §8 covariance/Jacobian/transport reduction would then give, in its actual smooth source class,
\[
 \frac{d_m(f)^2}{m}\le\frac4{q(0)^2}
 \left[2000u+104\eta+4\rho_{4K}(e_Z)\right].            \tag{7.1}
\]
This is a conditional substitution, not a separate result, a square-root rate, or an unrestricted-U theorem. Proposition 3.1 pays one possible approximate-normalization interface, but supplies no \(\rho\) to insert into (7.1).

The following prior objections remain intact, with their full original versions in the frozen brief/reports:

* The heavy star is uncapped; its cross-slot mass survives deleting the bad output direction, and all-slot deletion is expensive. It is not a realized log-concave density counterexample. The simplicial family here has cap 1 and serves a different purpose.
* A rank bound alone does not compress all input slots or preserve Jacobian compatibility. The regularized (Q\) is not (q(S^{1/2}L)\).
* Generic partial-trace channels need not have a linked symmetric cubic realization. The harmonic two-block cb obstruction has bounded defective mass and does not refute AR. Section 4 uses linkage but still does not refute AR.
* Arbitrary flag conditional deficits can be canceled by negative log scales; they are not a positive summable budget. Missing dimensions can be coupled only with the already paid (2k\) cost after a good marginal estimate and one global orientation.
* Density approximation does not establish coefficient convergence or an inherited cap. There is no approximation extension of (7.1) claimed here.
* The radial theorem, ordinary products, fixed-(m\) compactness, and I56's total-error local tube do not give a new uniform normalized stability theorem. Earlier quadrature nonconvergence and floating-versus-certified distinctions are retained.

## 8. Evidence, reproducibility, and final research status

Run from the project root:

```bash
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i65_linked_symmetric_algebra_rounding/verify.py
```

The verifier is read-only and offline. It checks the I65 seal, frozen brief equality, input hashes (allowing only the four named live-ledger drifts), 691 hash-referenced prior artifacts, the complete-tree/corpus correspondence, 26 pinned Git blobs, fixed-domain search line **multisets**, primary response/PDF extraction bytes, archived passage ranges, and an independent diagnostic replay. It does not rewrite old seals, fetch live pages, or run a hidden author proof oracle. `fetch_primary.py` is a separate one-shot acquisition script and is not called by the verifier. The first verification attempt incorrectly equated the 9,340-file corpus with all 10,373 tree blobs and failed. Its initial seal and failure record are preserved in `attempts/`; the corrected check verifies the exact corpus domain plus its inclusion in the complete tree and freezes the 1,033 additional tree entries. No search domain or prior evidence was silently changed.

`diagnostics.py` uses only the standard library, no earlier author diagnostic imports, exact rational arithmetic for its algebraic assertions, and a separate explicitly labeled floating table. Its 29,112 exact assertions cover 35 symmetric rational cubic cases in dimensions 1–5, five exact simplicial cases in dimensions 2–6, ten exact greedy recurrences through dimension 512, and three exact global-orientation checks in dimensions 3, 8, and 15. It checks the channel contraction, correct partial transpose, general-normalization rounding inequalities, exact normalization/commutators/spectra, caps and normalization loss throughout restriction, total-energy telescoping, and the explicit Householder/compression construction. The nine floating records through dimension 4096 only evaluate already displayed analytic formulas; they are not interval-certified values, numerical optimization of the orbit, or universal proofs. Finite diagnostics support implementation/indexing checks, while the quantified arguments are in §§3–6.

The current strongest actual positive partial is the arbitrary-normalization dephasing implication (3.1), together with the supplied-dilation rounding bound (6.1). The sharper negative progress is the exact linked counterexample to unit recovery, trace-negativity upgrading, and constant adaptive associator charge. These are method obstructions on a known algebra, not a substantial newly upstream-enabled rounding theorem. AR, its exact-(B\) version, and unrestricted U remain open in this work. Parent review/count/commit/publication authority is unchanged.
