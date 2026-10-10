# I162 — Focused independent ORIGINAL S155 correctness gate

## Verdict

**FAIL for the unchanged-original proof package in S155 §§3.1–3.7.** There is a factor-four error in its asserted **exact fermionic multiplication operator**. This is not merely a choice of wall convention or an expansion of omitted details. I158's blanket narrower “PASS without substantive repairs” is not sustained.

**This is not a counterexample to the leading Weyl-law statement.** With the explicitly separated correction below, the same leading law on the **original** closed physical supercharge form is established. Its exponent, constant, multiplicities, explicit allowed representation, and physical domain do not change. I do **not** relabel this corrected deduction “original proof PASS without repairs.”

| Scope of unchanged S155 | Verdict |
|---|---|
| §3.1 representation, admissible fixed type, nonzero multiplicity and conservative constants | PASS without substantive repairs |
| §3.2 orbit, stabilizer, Hom convention, multiplicities, measure and angular kinetic expression | PASS without substantive repairs |
| §3.2 asserted exact $B(D_s)$, line 141, and consequently the exact form when that displayed matrix is substituted | **FAIL** |
| §3.3 inherited core, slice matching, central lifts and qualified parity statements | PASS without substantive repairs |
| §§3.4–3.6 estimates interpreted with the source's actual $B$ | Valid deductions; the explicit coefficient correction is required to make the entire claimed exact-operator chain correct |
| §3.7 phase integral, convergence and coefficient | PASS without substantive repairs |
| Unchanged leading-law statement considered apart from the false exact-operator assertion | Proved below with the correction openly separated; no original-proof-without-repairs PASS |
| I158's broader historical assignment | **INCOMPLETE / UNRESOLVED**, unchanged |
| Contribution, substantiality, acceptance | Not decided; a separate gate remains |

All pinned OpenAI theorems **and lower operations** remain stipulated. No upstream truth audit, contradiction inference or ex-falso argument is used. External FNT is ordinary evidence. Eight accepted findings remain eight; two remain. No shared edits, children, staging, commits or publication occurred. This review owns only its report and its two I162 directories.

## 1. Exact originals, sources and focused scope

The unchanged originals checked are:

* `frontier/iterations/i155-fixed-sector-bfss-counting.md`, SHA-256 `c6e05a0853e3232f86c8a8049cb9ecb373c9358ca58bfc1cb42c6e81d4b15f44`.
* `frontier/iterations/iteration155-fixed-sector-bfss-counting-task.json`, SHA-256 `e32170f6d05bfcfea861e801830655650dfe8fb3813b893243bf3428dda775e1`.
* `frontier/iterations/iteration158-fixed-sector-bfss-counting-r2-task.json`, SHA-256 `b61c7515916ff6301f44a945bae99b595fc5c1bc6f7dad2df9170e3f699e76eb`.

The complete 84,894-character I158 brief and 101,952-character I155 brief were decoded losslessly and freshly read in bounded ranges, including their full embedded reports, finalized parent responses, repeated evidence fields and all other top-level fields. The original S155 and incomplete I158 report were freshly read in full. Historical launch fields saying `running` are launch snapshots, not current status: the parent reports I158 failed at the provider usage limit with no pending run. I did not query, resume or interfere with another task.

The actual dependency graph of the leading-law proof is small:

1. **P:** pinned *Positive eigenvalues of the relative SU(2) BFSS Hamiltonian*, October 5, 2026. Complete original TeX, PDF text and PDF-reader presentation were read through their endings. The TeX is at  
   `frontier/sources/i14_spectral_width_novelty_r3/corpus/preprints/Positive-eigenvalues-of-the-relative-SU-2-BFSS-Hamiltonian-October-5-2026/build/positive-eigenvalues-relative-su2-bfss.tex`.
   Its SHA-256 is `c6d02247561556ab27c8015579045a8a71f20214261a14c810175979970621ce`; Git blob `12c5fffb5f90b48856f60fb0e93c18e2490c5f1b` matches the complete pinned preprint tree. Below, **P:T** means its LF-numbered TeX lines; **P:X** means the existing PDF text.
2. **FNT:** Ferone–Nitsch–Trombetti, *A remark on optimal weighted Poincaré inequalities for convex domains*, **1207.0680v2**, November 6, 2012. Existing `frontier/sources/i155_fixed_sector_bfss_counting/external/fnt.txt`, all LF lines 1–529, and the ten-page PDF were freshly read. The theorem and the complete proof through its ending, not just the abstract, are covered.
3. Finite-dimensional compact-group reduction, the local slice construction, Lipschitz multiplication, min–max, and the elementary local cube Weyl argument are reconstructed below. No noncompact equivariant Weyl theorem is assumed.

P's needed dependencies are internal: `lem:form`, `lem:rotations`, `lem:branching`, `lem:slice`, `lem:oscillator`, `prop:confinement`, and `lem:large-sectors`. All were read with their full proofs, including P's concluding theorem proof and bibliography. Its branching argument is supplied internally, rather than outsourced to the cited comparison paper. **No operation from the threshold-state companion is needed**: neither uniqueness of a zero mode, maximal-domain identification, nor its partition-channel machinery enters this proof. I checked that companion's inherited byte binding, but do not claim a fresh semantic reading of that manuscript. This is a dependency exclusion, not a literature/contribution verdict.

The parent expressly narrowed I162. The unrelated recursive triangular Ising, Bose and adiabatic audits have not been completed here. The external-provenance FAIL and missing exact triangular critical-stability premise remain untouched. The historical I153 Bose screen stays incomplete; I155's claimed later comparison closure is historical new work, not retroactive completion and not a new B153 theorem. No new Bose conclusion is drawn.

## 2. Decisive objection: $i/2$ is not $2i$

P:T 236–256, label `eq:potential`, states literally:

```tex
B(x)=\tfrac i2 f_{abc}x_i^a\gamma^i_{\beta\delta}
                   \theta_\beta^b\theta_\delta^c.
```

Its proof repeats the same coefficient at P:T 310–318. The other conventions are unchanged: $f_{abc}=\sqrt2\,\varepsilon_{abc}$, $\{\theta_\alpha^a,\theta_\beta^b\}=\delta_{\alpha\beta}\delta_{ab}$, and kinetic coefficient $1/2$.

S155 line 141 instead writes

$$
B_{\rm S155}(D_s)=2i\sum f_{abc}s_a\gamma^a_{\alpha\beta}
                  \theta_\alpha^b\theta_\beta^c.
$$

It therefore gives **four times** the source matrix. This is not a different summation convention: both expressions sum both nonzero color orders and the same spinor indices. S155 lines 83 and 141 explicitly use the larger coefficient, and I158 lines 61–65 and 103 repeat it. The retained PDF text linearizes fractions awkwardly, including `21` for $1/2$ and `2i` at this term. Such text order is not a mathematical license to replace the unambiguous, hash-matched `\tfrac i2` by `2i`. No conflict between stipulated source results is inferred.

The error is not vacuous after the physical projection. Here is an actual-sector check, independent of finite diagnostics. Let $v$ be the unique maximal-first-weight fermionic vector constructed in §3 below. The first spatial rotation defines the orthogonal complex structure $J_{\rm sp}=\gamma^1\gamma^2$ on each real spinor copy. The top state is the vacuum for one of its two complex isotropic subspaces. Since $\gamma^1$ anticommutes with $J_{\rm sp}$, its bilinear pairing restricted to the opposite isotropic subspace is nondegenerate. Thus
$\sum_{\alpha,\beta}\gamma^1_{\alpha\beta}\theta_\alpha^2\theta_\beta^3v$
has a nonzero two-creation component. The color-2 and color-3 creation modes are distinct, so symmetric spinor coefficients do not make it vanish. In contrast, $\gamma^3,\gamma^5$ commute with $J_{\rm sp}$; their different-color bilinears have only number-preserving terms and annihilate this vacuum.

Consequently $B(X)v\ne0$ at $X=(s_1e_1,s_2e_3,s_3e_5)$, $s_1>s_2>s_3>0$. The source polynomial has value $(s_1s_2)^{2k}$ there. With a suitable radial smooth cutoff, the actual physical vector $\psi=\chi(|X|)P^kv$ in the specified sector has $B\psi\ne0$. Both $B\psi$ and $\psi+tB\psi$, for real $t$, stay in the same projected compact core, because $B$ is smooth and symmetry equivariant. The coefficient of $t$ in
$\langle\psi+tB\psi,B(\psi+tB\psi)\rangle$
is $2\|B\psi\|^2>0$. For some $t$ the expectation is nonzero. Substituting $4B$ in the exact form then changes its value. Thus the false exact-form claim really concerns this physical sector, not only an inaccessible ambient matrix entry.

### Separate correction, not an edit to S155

Use

$$
B_{\rm src}(D_s)=\frac i2\sum f_{abc}s_a\gamma^a_{\alpha\beta}
                   \theta_\alpha^b\theta_\beta^c
$$

in the exact form and radial operator. The source's own symbol $B$ below always means this matrix. Nothing in the remaining counting proof needs its erroneous fourfold value.

The original $C=1024$ is still a valid **upper bound**, not an equality. With the actual coefficient the same estimate even gives
$\|B(X)\|\le32\sqrt2\sum_{i,a}|x_i^a|\le96\sqrt6|X|<1024|X|$.
Hence $m=3072$, $c_m=3$, and the chosen $\lambda$ remain valid. The semiclassical $B$-term is still $O(h)$. This explains why the leading law survives, but does not turn an erroneous exact operator into a harmless clarification. I158's assessment missed a genuine correction.

## 3. Representation and principal fiber

The real Clifford label space is $W=\mathbb R^{16}\otimes\mathbb R^3$. The complex irreducible Clifford module has dimension $2^{24}$. P's spin and gauge actions lift to $\mathrm{Spin}(48)$. Their commutator is scalar on the irreducible Clifford module; its dependence on a factor is a continuous character of a connected semisimple group and is trivial. Thus the actions commute.

A generator of $\pi_1(\mathrm{SO}(3))$ rotates sixteen real planes once in $W$. Its spin lift ends at $(-1)^{16}=1$. The gauge action really descends to $\mathrm{SO}(3)$; no projective residual gauge action is being omitted.

The eight positive-first-coordinate weights of the real Spin(9) spinor are
$(1/2,\epsilon_2/2,\epsilon_3/2,\epsilon_4/2)$. Three color copies give 24 real planes of first speed $1/2$. In the Clifford spin module the unique all-positive choice has first weight $24/4=6$. Its other coordinates vanish by sign balance. Roots increasing the first coordinate kill it; the zero-first-coordinate roots form the semisimple Spin(7) centralizer and act trivially on the unique line. Hence it is a highest vector of weight $(6,0,0,0)$. The commuting gauge group preserves the line and has no nontrivial character, so it is gauge invariant. All first weights are at most six, including for the source's transported Spin(8) stabilizers. Thus $M=6$.

For reference the full spin character can be specified without evaluating a huge representation:

$$
\chi_F(\theta,\phi)=
\prod_{\substack{w=(1,\epsilon_2,\epsilon_3,\epsilon_4)/2\\ c=-1,0,1}}
\left(e^{i(w\cdot\theta+c\phi)/2}+e^{-i(w\cdot\theta+c\phi)/2}\right),
$$

with continuous spin lifts. It is periodic under the gauge $2\pi$ loop. A spatial central $2\pi$ rotation acts by occupation parity relative to the top state, not identically on all of $F$.

Set $G=\mathrm{Spin}(9)\times\mathrm{SO}(3)$, acting by $X\mapsto AXR^t$.
Special-orthogonal SVD supplies every regular orbit with a unique ordered positive singular-value representative. Any unwanted orientation in the left frame can be corrected in its six-dimensional perpendicular space; there is no second orientation copy of the chamber.

At $D_s$, preservation of $D_s^tD_s$ forces
$R=D=\operatorname{diag}(\epsilon_1,\epsilon_2,\epsilon_3)$, $\prod\epsilon_i=1$.
Then $A=\operatorname{diag}(D,Q)$, $Q\in\mathrm{SO}(6)$. Taking the full spin preimage gives exactly S155's $K$.
Its identity component is Spin(6), and its component quotient is the Klein four group. In particular the order-four Spin(6) center, whose square is the global order-two spin center, is included.

Evaluation of a physical intertwiner $V_\lambda\to\mathcal H$ transforms as

$$
\rho(a,R)T=R_F(a,R)T\pi_\lambda(a)^{-1}.
$$

It gives $E_\lambda=(V_\lambda^*\otimes F)^K$, not an arbitrarily chosen dual convention. On $E_0=\operatorname{Hom}_{\mathrm{Spin}(6)}(V_\lambda,F)$, squares and commutators of representatives of the four sign components lie in Spin(6). Therefore their induced actions are commuting involutions and their average is an orthogonal projector. Both original formulas follow:

$$
m_\lambda=\frac14\sum_D\operatorname{Tr}(A_D|E_0)
=\int_K\overline{\chi_\lambda(a)}\chi_F(a,R)\,dk.
$$

This imposes the entire center, not just a parity surrogate.

P's polynomial times the top fermionic vector, with $k=1540$, has
$\lambda=(3086,3080,0,0)$. The bound $3080>3072+6$ is strict.
At columns $s_1e_1,s_2e_3,s_3e_5$, its value is
$(s_1^2s_2^2)^kv\ne0$.
The finite irreducible module generated by this highest vector has nonzero stabilizer-equivariant evaluation. Transport to $D_s$ yields $E_\lambda\ne0$. The same reasoning shows that every nonzero source-constructed type in the theorem has positive principal multiplicity: its nonzero smooth polynomial cannot vanish on the dense regular set.

Every compact smooth $E_\lambda$-valued section $T(s)$ lifts by

$$
I_T(w)(gD_s)=R_F(g)T(s)\pi_\lambda(g_{\rm left})^{-1}w.
$$

The $K$-condition makes the formula well defined. Smooth local singular frames give smoothness on the regular set, and compact support separated from the singular set permits smooth zero extension. This works for **every** fiber section and every $w$, not merely for the source polynomial.

Schur averaging gives orbit norm
$\operatorname{Tr}(T^*T)\|w\|^2/d_\lambda$, for probability Haar measure.
If geometric disintegration has constant $c$, multiplying the lifting map by
$\sqrt{d_\lambda/c}$ makes the identification

$$
\mathcal H_\lambda\simeq V_\lambda\otimes
L^2(\mathcal C,J(s)\,ds;E_\lambda)
$$

unitary. Thus full counting multiplies the reduced count by $d_\lambda$; no extra group-volume factor survives.

## 4. Metric, signs and all physical walls

Each of the eighteen image/perpendicular rotation directions has length $s_i$. For an image pair the two left/right directions have Gram matrix

$$
\begin{pmatrix}s_i^2+s_j^2&-2s_is_j\\-2s_is_j&s_i^2+s_j^2\end{pmatrix}.
$$

The eigenvectors $(1,\pm1)/\sqrt2$ have eigenvalues $(s_i\mp s_j)^2$. Radial directions are orthonormal and orthogonal to all orbit directions. Hence

$$
J=(s_1s_2s_3)^6\prod_{i<j}(s_i^2-s_j^2),
\qquad \deg J=24.
$$

Differentiating the lift yields
$L_{ij}T=dR_F(e_{ij})T-Td\pi_\lambda(e_{ij})$ and
$R_{ij}T=dR_F(e_{ij}^{\rm right})T$.
The transpose in $AXR^t$ is already accounted for in the tangent $AD-DB$;
inserting another sign in the right derivative would be wrong.
The inverse metric gives precisely S155's nonnegative $A_s$, with the
$L+R$ numerator over $(s_i-s_j)^2$. Individual derivatives take values in the larger Hom space. The invariant sum, not each derivative separately, defines the compressed Hermitian form on $E_\lambda$.
Since $B$ is equivariant and $K$ fixes $D_s$, $B(D_s)$ commutes with $R_F(K)$; postcomposition therefore preserves the entire $E_\lambda$. This statement does not discard the fermion matrix or assume cancellation of its eigenvalues.

**With the correction in §2**, the exact compact-regular form is

$$
\int_{\mathcal C}J\left\{
\tfrac12|\partial T|^2+\tfrac12 A_s[T]+V|T|^2+
\langle T,B_{\rm src}(D_s)T\rangle\right\}ds,\qquad
V=\sum_{i<j}s_i^2s_j^2.
$$

The radial expression is $-\frac1{2J}\sum_i\partial_i(J\partial_i)$.
On a regular domain multiplication by $J^{1/2}$ changes this into

$$
-\tfrac12\Delta+\tfrac14\Delta\log J+\tfrac18|\nabla\log J|^2.
$$

The last potential is bounded on each fixed compact regular set; it has no asserted global positive sign.

### Singular slice and matching audit

For rank $r$ with equal-positive blocks of sizes $k_j$, the full vector-image stabilizer consists of

$$
(\operatorname{diag}(O_1,\ldots,O_\ell,Q),
 \operatorname{diag}(O_1,\ldots,O_\ell,P)),
$$

where $O_j\in O(k_j)$, $Q\in O(9-r)$, $P\in O(3-r)$, and both total determinants are one. Use its entire Spin(9) preimage. This specifies finite components and intersections simultaneously.

Orthogonality to $AD-DB$ is equivalent to symmetry of $YD^t$ and $D^tY$.
It gives the normal representation

$$
N_D=\bigoplus_j\operatorname{Sym}(k_j,\mathbb R)
       \ \oplus\ \operatorname{Mat}_{9-r,\,3-r}(\mathbb R).
$$

Thus:

* A simple positive collision has its traceless symmetric two-plane and invariant radial directions. The connected group has simultaneous SO(2) vector image; its actual lift is the central product of Spin(2) and Spin(6), paired with the right rotation.
* Rank two with distinct positive values has $\mathbb R^2\oplus\mathbb R^7$ and connected Spin(7).
* Rank one has $\mathbb R\oplus\operatorname{Mat}_{8,2}$ and connected Spin(8) times the independent right SO(2).
* A positive triple collision has $\operatorname{Sym}(3)$, with the simultaneous Spin(3)/SO(3) lift and Spin(6).
* The origin has all of $G$ and all of $\operatorname{Mat}_{9,3}$.

These formulas also cover a positive collision at rank loss and all intersections.
The compact orbit has an equivariant tubular neighborhood $G\times_H N_D$ locally: the normal-bundle map to $g(D+Y)$ has invertible derivative at the zero section, and compactness permits a uniform small tube. An $H$-equivariant smooth Hom-valued slice map extends by this formula and conversely restricts from an ambient map. Invariant local partitions of unity join compatible pieces. Taylor coefficients lie in
$\operatorname{Hom}_H(\operatorname{Sym}^jN_D,\operatorname{Hom}(V_\lambda,F))$.
Closure is taken in the original projected form norm, not in a freely chosen wall norm.

At a pair collision the simultaneous quarter-turn reverses the signed splitting coordinate. Its square lies in $K$, so its fiber action $W$ is an involution. Therefore
$T(-u)=WT(u)$ gives $WT^{(j)}(0)=(-1)^jT^{(j)}(0)$.
At rank loss the left $\pi$-rotation reversing the missing image axis and one perpendicular axis does the same. Its spin square is $-1\in\mathrm{Spin}(6)$, already trivial on the Hom invariants, so $W_0^2=1$.

I specifically challenged whether S155 substitutes these parity conditions for full slice smoothness. It does **not**: line 155 says they are *part* of the full condition, and lines 149–153 prescribe the whole equivariant slice. Nor does it give pointwise jets to all form vectors. I find no separate false wall claim on that reading. The language about simultaneous orthogonal groups denotes the vector images within an explicitly lifted stabilizer, not an unsupported direct-product claim.

## 5. Original form closure, positive control and IMS

P:T 338–411 supplies the projected compact core and reduction of the associated operator. P:T 615–686 supplies, on that closed sector,

$$
q\ge\tfrac14G+cR_1,\qquad c=c_m>0,
$$

where $G=\|\nabla\psi\|^2$, $R_1=\int |X||\psi|^2$.
The source's exact form gives $q\ge G/2+V_1-CR_1$.
For $\epsilon=c/[2(c+C)]$ their convex combination yields

$$
q\ge aG+\epsilon V_1+bR_1,\qquad
a=(1+\epsilon)/4,\quad b=c/2>0.
$$

Applying this to core differences proves that gradients, $\sqrt V$-multiples and $\sqrt{|X|}$-multiples converge in $L^2$ along any form-Cauchy core sequence. Closedness of differentiation and multiplication identifies the limits. The $B$-form is continuous under the radius norm bound. Thus the exact **source** expression and the inequality pass to the closure. Quartic integrability is proved, not presumed.

For bounded invariant Lipschitz $\chi$ with bounded weak gradient,
$Q_\alpha(\chi\psi)=\chi Q_\alpha\psi+[Q_\alpha,\chi]\psi$;
the commutator is bounded Clifford multiplication. To establish membership in the *minimal* form closure, first mollify $\chi$ with a radial ambient mollifier. It preserves both invariances and the uniform Lipschitz bound. Products with a fixed compact core vector converge in the gradient and weighted norms; then a diagonal core approximation treats a general form vector. This is not an appeal only to a maximal distributional domain.

Ordered singular values are globally Lipschitz, by their min–max characterization and the bound
$|s_i(X)-s_i(Y)|\le\|X-Y\|_{\rm op}\le\|X-Y\|_{\rm F}$.
Crossings cause no surface term in this first-order form argument. Choose the two cutoffs as sine and cosine of one bounded Lipschitz angle; this avoids a square-root cutoff derivative singularity. Expanding gradients gives

$$
\sum_j q[\chi_j\psi]
=q[\psi]+\tfrac12\int\sum_j|\nabla\chi_j|^2|\psi|^2.
$$

Profiles in $E^{-1/4}s$ give error $O_{R,\delta}(E^{-1/2})$.
After reduction and dropping angular energy the scalar comparison is

$$
q[T]\ge\int J\{a|\partial T|^2+W(s)|T|^2\}\,ds,\qquad
W=\epsilon V+b|s|.
$$

This is applied to actual localized physical vectors before any comparison-space enlargement. It is not a pointwise confinement assertion about $V+B$.

## 6. FNT, vanishing weight, complex means and every endpoint

FNT Theorem 1.1 is at text lines 94–104; its one-dimensional Proposition 1.1 and Lemmas 2.1–2.2 are at 137–322; the convex slicing lemma and theorem proof finish at 329–444. References finish at 529. For $p=2$, its conclusion is exactly

$$
\int_Q J|u-u_Q|^2\le\frac{\operatorname{diam}(Q)^2}{\pi^2}
\int_QJ|\nabla u|^2.
$$

The paper reduces a smooth positive log-concave one-dimensional weight to an exponential weight using the slope at the first eigenfunction's zero. Its autonomous $u/u'$ equation pairs positive and negative arguments to obtain the sharp interval bound. The general weight follows by approximation. Convex bisection preserves the weighted mean and makes all but one directions thin; log concavity of cross-sectional volume and the one-dimensional estimate complete the proof.

For additional independent checking of the precise $p=2$ input, if $f=e^h>0$ is smooth and log concave, a nonconstant weighted Neumann eigenfunction satisfies
$-u''-h'u'=\lambda u$.
Set $v=u'$, $z=\sqrt f\,v$, so $z$ has zero endpoint values. Differentiation and integration by parts give

$$
\lambda\int|z|^2=
\int\left(|z'|^2+\left(\tfrac14(h')^2-\tfrac12h''\right)|z|^2\right)
\ge \frac{\pi^2}{L^2}\int|z|^2.
$$

This independently checks the needed one-dimensional direction and constant without importing the article's statements for other $p$.

Here $J$ is a product of positive affine factors to positive powers in the chamber. Hence $\log J$ is concave. On a cube/chamber intersection $Q$ it is bounded, continuous up to the faces, positive in the interior, and may vanish on the boundary. One explicit positive smooth approximation on a neighborhood of its closure is obtained by replacing every affine factor $l$ by $l+\eta$. The resulting weights are log concave, converge uniformly on each bounded cell, and have a positive lower bound for fixed $\eta>0$.

This also makes the usual thin-slice proof precise at zero weights: fix $\eta$ first. Weighted means on each thin piece are recentered exactly. If the mean-integral error is at most $\omega(\tau)|Q_i|$, the loss from recentering is at most
$\omega(\tau)^2|Q_i|/c_\eta$, since the approximate one-dimensional mass is at least $c_\eta|Q_i|$. Sum the errors, let slice thickness $\tau\to0$, then let $\eta\to0$. Smooth test functions extend to the small neighborhood needed in slicing. No uniform positive lower bound for the limiting $J$ is required. This is an explicit realization of FNT's approximation at the needed weight, not an assertion of arbitrary weighted-Sobolev density.

Physical smooth core intertwiners evaluated at the linear diagonal map $s\mapsto D_s$ are smooth through the coordinate walls. FNT therefore applies to their restrictions. The core-difference estimate in §5 gives convergence of their weighted radial derivatives. Weighted means are continuous in $L^2(Q,J)$, since $0<\int_QJ<\infty$, so the inequality passes to the actual restricted form closure. Apply it to real and imaginary parts: each fiber coordinate gives **one complex** mean constraint, not two complex constraints.

For a cube of side $\ell$, $\operatorname{diam}(Q)\le\sqrt3\ell$. Let
$\ell=\kappa E^{-1/2}$, with $a\pi^2/(3\kappa^2)>3$.
Call a cell eligible if $\inf_QW\le2E$.
Zero means on eligible cells cost more than $3E$ there; ineligible cells cost at least $2E$ by their potential. Hence a subspace with every Rayleigh quotient at most $3E/2$ injects into the eligible complex means and has dimension at most $m_\lambda$ times the number of eligible cells. Restoring the representation factor multiplies by $d_\lambda$.

This proves the min–max direction without assuming a degenerate Neumann operator has compact resolvent. If desired, replacing a bounded-cell function by its means on finer convex cells gives finite-rank approximation error at most $\sqrt3\ell/\pi$ times its weighted derivative norm. Compact embedding follows on this particular completion. Arbitrary maximal weighted boundary spaces are not needed.

For supported vectors retain whole cells meeting the support, and take the potential infimum over each **whole** cell. A witness for eligibility and a support point differ by at most $\sqrt3\ell$. Eligibility implies
$|s|\le2E/b+O(\ell)$.
Over a first-coordinate interval starting at $u>0$, the quartic term gives
$s_2,s_3\le\sqrt{2E/\epsilon}/u+O(\ell)$. The transverse cell count is therefore bounded by
$C_\lambda(1+E/u)^2$.
The additive one retains widths smaller than $\ell$ and all transverse endpoint cells.

For horn support $s_1>A=RE^{1/4}$, the first retained interval starts no earlier than $A-\ell\ge A/2$ for sufficiently large $E$ at fixed $R\ge1$. The last interval ends by $C_\lambda E+O(\ell)$. Integral comparison plus the first summand gives

$$
\#\text{cells}\le C_\lambda\left[
\ell^{-1}\int_{A/2}^{C_\lambda E+O(\ell)}(1+E/u)^2du
+(1+2E/A)^2\right].
$$

The integral contributes respectively $O(E^{3/2})$,
$O(E^{3/2}\log(2+E))$, and $O(E^{9/4}/R)$.
The endpoint term is $O(1+E^{3/2}/R^2)$. If the horn starts beyond the eligible region the count is zero apart from the same endpoint allowance. Constants are independent of $R\ge1$; the large-$E$ threshold may depend on the fixed $R$.

In the box $s_1\le RE^{1/4}$, the three wall equations are
$s_3=0$, $s_1-s_2=0$, and $s_2-s_3=0$.
Enlarging a scaled $\delta$-slab by one cell yields at most
$C_R(\delta E^{9/4}+E^{3/2}+1)$ cells. Union over the three slabs includes rank loss, pair/triple collisions, all intersections and the origin. There is no separate uncharged thin channel or corner term.

## 7. Local Weyl law and the physical liminf/limsup

Under $s=E^{1/4}t$, weighted measure becomes $E^{27/4}J(t)\,dt$;
the flat unitary includes $E^{27/8}J(t)^{1/2}$.
Let $h=E^{-3/4}$. On any fixed bounded regular polyhedral domain, the **correct source operator**, divided by $E$, is

$$
P_h=-\tfrac{h^2}{2}\Delta+V(t)I+hB_{\rm src}(D_t)+h^2C_\lambda(t).
$$

All indicated matrix coefficients are smooth and bounded there. The statement is neither uniform near a wall nor uniform in $\lambda$.

For a Dirichlet realization, scalar potentials $V\pm C(h+h^2)$, repeated $m_\lambda$ times, bracket the matrix form. Subdivide into fixed small cubes and bound $V$ by its extrema. On a side-$L$ cube, the Dirichlet/Neumann integer lattice count has limit

$$
h^3N(1)\longrightarrow L^3(2\pi)^{-3}\frac{4\pi}{3}
[2(1-v)_+]^{3/2}.
$$

Coordinate-plane frequencies contribute only $O(h^{-2})$ for fixed $L$.
First let $h\to0$, then cube size tend to zero. For Dirichlet polyhedra, interior and exterior cube unions bracket the domain by inclusion, and exterior cube unions can be split with Neumann forms. Boundary-layer volume tends to zero. This avoids an unsupported Neumann domain-monotonicity argument. Continuity of $(1-V)_+^{3/2}$ also pays thresholds $1+o(1)$.

**Boundary-condition challenge:** natural weighted Neumann conditions do not become flat Neumann conditions under the $J^{1/2}$ unitary. They become
$\partial_nu-\frac12(\partial_n\log J)u=0$, with form boundary term
$-\frac{h^2}{4}\int_{\partial\Omega}\partial_n\log J\,|u|^2$.
On a fixed regular Lipschitz polyhedron this is bounded by
$\eta h^2\|\nabla u\|^2+C_\eta h^2\|u\|^2$, by the trace inequality.
Here the needed trace estimate follows by integrating $|u|^2$ along inward transversal segments in finitely many boundary charts, followed by Cauchy–Schwarz and Young's inequality; density extends it from smooth functions to $H^1$. No global singular-boundary trace theorem is assumed.
Squeezing and then letting $\eta\downarrow0$ gives the same leading law. More importantly, the global proof can use only the slightly larger **Dirichlet** domain explicitly permitted in S155 line 213. No physical wall is replaced by either auxiliary boundary condition. I do not find a second required substantive repair on this point.

The local coefficient is therefore

$$
d_\lambda m_\lambda(2\pi)^{-3}\frac{4\pi}{3}2^{3/2}
\int_\Omega(1-V)_+^{3/2}\,dt.
$$

For the lower bound, all $H_0^1$ vectors on interior regular domains are form limits of the compact regular lifts in §3, in every fiber direction and every representation direction. Extend by zero. The physical count dominates their Dirichlet counts. Exhaust the chamber and use monotone convergence.

For the upper bound, fix $R,\delta$ and choose the invariant sine/cosine partition of §5. Define good and bad spaces as the closed subspaces of the original form domain with essential support in the respective closed support regions, and use their $L^2$ closures as Hilbert spaces. They inherit compact form embedding from P. The map
$\psi\mapsto(\chi_{\rm good}\psi,\chi_{\rm bad}\psi)$
is an isometry, and for the **entire** spectral subspace below $E$, IMS bounds its direct-sum Rayleigh quotient by
$E+C_{R,\delta}E^{-1/2}$. Min–max gives the sum of the two supported counts at this threshold.

The good support is separated from the boundary of a slightly larger regular Dirichlet domain. Its form embeds into that Dirichlet form, in the upper-count direction. The bad support is contained in enlarged wall collars and a horn; §6 bounds it after physical localization. Cells meeting both regions may be overcounted. The shift is $o(E)$ and eventually below the $3E/2$ margin.

Thus

$$
\limsup_{E\to\infty}E^{-9/4}N_\lambda(E)
\le C_{\rm phase}+C_\lambda/R+C_{\lambda,R}\delta.
$$

The order is **$E\to\infty$, then $\delta\downarrow0$ at fixed $R$, then $R\to\infty$**. No uniform control of $C_{\lambda,R}$ in $R$ is assumed. The opposite liminf comes from interior exhaustion. Singular strata have ambient measure zero and no separate $L^2$ summand; their neighborhoods have been estimated, not discarded.

## 8. Phase integral and exact constant

Let $I=\int_{\mathcal C}(1-V)_+^{3/2}\,ds$.
For $s_1=u\ge1$, $V\le1$ implies $s_2^2+s_3^2\le u^{-2}$, so the cross-sectional area is at most $\pi/(4u^2)$. This proves convergence and an $O(R^{-1})$ tail. Positivity follows from any small regular open region with $V<1$.

Tonelli, first integrating $s_3$, gives on the positive octant

$$
Z_{\rm oct}=\frac{\sqrt\pi}{2}
\int_{x,y>0}\frac{e^{-x^2y^2}}{\sqrt{x^2+y^2}}\,dx\,dy.
$$

Put $x=r\cos\theta,y=r\sin\theta$. The radial integral is
$\Gamma(1/4)/(4\sqrt{\sin\theta\cos\theta})$;
the angular integral is
$\frac12 B(1/4,1/4)=\Gamma(1/4)^2/(2\sqrt\pi)$.
Hence $Z_{\rm oct}=\Gamma(1/4)^3/16$ and
$Z_{\mathcal C}=\Gamma(1/4)^3/96$, dividing by the six permutation chambers once.

Quartic homogeneity gives $\operatorname{vol}\{V\le v\}=A v^{3/4}$.
Its Laplace and beta integrals imply

$$
I=Z_{\mathcal C}\frac{\Gamma(5/2)}{\Gamma(13/4)}
=\frac{\Gamma(1/4)^3\Gamma(5/2)}{96\Gamma(13/4)}.
$$

Using $\Gamma(5/2)=3\sqrt\pi/4$ and
$\Gamma(13/4)=45\Gamma(1/4)/64$, multiplication by the momentum factor yields

$$
N_\lambda(E)\sim
d_\lambda m_\lambda
\frac{\sqrt2\,\Gamma(1/4)^2}{270\pi^{3/2}}E^{9/4}.
$$

The $2^{3/2}$ comes from the kinetic coefficient $1/2$.
Neither $J$, a second chamber factor, nor the order-four component group is inserted again. This is the unchanged leading-law statement, proved for the **source operator**, with the correction explicitly made in §2. No full-Hamiltonian law, uniform representation estimate, sector mixing, massless gap or selected physical wall realization follows.

## 9. Contribution boundary and historical evidence

One concrete overlap was freshly checked: Halpern–Schwartz, **hep-th/9712133v1**, retained text lines 126–185, equations (2.4)–(2.6), already has the three singular values, the scalar radial divergence form, and the measure
$(\lambda_1\lambda_2\lambda_3)^{d-3}\prod(\lambda_j^2-\lambda_i^2)$.
At $d=9$ this is precisely the degree-24 Jacobian, in the opposite ordering convention. Its full later proof was **not** reread here; no absence-of-overlap conclusion is drawn from this selected passage.

The original reports' further comparisons with Halpern–Schwartz connections, Lüscher/Simon scalar confinement and nonclassical counts, smaller-model approximate channels and compact equivariant Weyl laws remain inherited comparisons, not fresh I162 full-paper reviews. FNT itself supplies a standard weighted diameter estimate. The complete application may be technical. None of these observations decides the separate contribution gate.

I158 has **no seal**. Its prevalidation lists its read manifest as 8,756 bytes with hash `cb83866deff5ebcbe53855d8d1ff6f216295917c28db9736c3d3cf84a8d13bb5`; the present file is 37,110 bytes with hash `0457af6683f25a048c0a10af30bbac77089bae7b1657c28c9bc4587c114c69f3`. Supplemental files were also added after that inventory. Its old `PASS` is a stale prevalidation result, not a sealed replay PASS. All those bytes were baselined and preserved, including untracked preparation. The present evidence cannot retroactively seal I158 or complete its historical assignment.

## 10. I162 evidence and validation

Owned evidence is under:

* `frontier/sources/i162_fixed_sector_bfss_focused_astra/`
* `frontier/experiments/i162_fixed_sector_bfss_focused_astra/`

The package records exact LF and character reading ranges, passage hashes/endings, lossless original task views, source/text bindings, source-version identifiers, scoped exclusions, failed/truncated displays and the distinction between fresh semantic reading and inherited hashes. The pinned P TeX, PDF and README are checked against `sources/preprints-tree.json`; no truncated root-tree cache is used. No corpus is copied, no ancestor program executes, and no original PDF extraction is rerun. Native PDF-reader presentations were additional reads, not executions of ancestor converters.

The inventory is deliberately **proportionate to this focused gate**, rather than recursively duplicating or revalidating unrelated corpus packages. Four live ledgers may drift; their initial snapshots remain immutable. Reading them does not bind parallel work. The final seal contains the one canonical exact owned-file inventory. Read-only prevalidation precedes its single exclusive creation. The verifier checks immutable owned and referenced bytes, source blob identities and reading-view reconstruction **before** new finite diagnostics, and installs an audit guard denying writes, network, processes and bytecode files.

Prevalidation completed successfully with 51 immutable references, 35 preserved ancestor files, 41 bounded reading receipts and three pinned original blobs. Python syntax parsing and JSON parsing passed. Only the two permitted continuation/count ledgers drifted at that check. New finite mathematical diagnostics were deliberately deferred to the sealed replay. The final replay result is reported in the handoff, not added afterward to the sealed report.

Run, from any directory:

```sh
python3 -I -B /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/experiments/i162_fixed_sector_bfss_focused_astra/verify.py
```

Its PASS concerns evidence and the stated exact finite checks only. It cannot override the **FAIL** at the original exact-reduction scope, prove universal mathematics, certify substantiality or add a finding.

**Unpaid prerequisite for an original-proof PASS:** the parent must explicitly handle the erroneous exact $B$-formula as a correction, not silently accept I158's unchanged-original PASS. The corrected core deduction above has no further identified analytic prerequisite. Separate contribution review and any broader historical completion remain unpaid and outside this gate.
