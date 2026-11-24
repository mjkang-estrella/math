# The type-D contingency metamatrix of rank 27 is not totally positive

MathDB 367377. **Refuted.** The refutation is machine-checked in Lean 4 (Mathlib), for the concrete
group of even signed permutations of 27 coordinates with its 27 standard reflections. The only step
not formalized is the textbook fact that this concrete pair is a Coxeter system of type D₂₇ (stated
below as the cited bridge). The Lean endpoint depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## 1. The conjecture (verbatim)

From the MathDB record (Wang–Xie–Zhang, *On the Total Positivity of Contingency Metamatrices*,
arXiv:2503.02213, Conjecture 1.0.1):

> Let $(W,S)$ be a finite Coxeter group of rank $|S|=n$. For subsets $I,J\subset S$, let $W_I$ and
> $W_J$ be the parabolic subgroups of $W$ of types $I$ and $J$, respectively. Define the metamatrix
> $M(W)=(M_{pq})_{0\leq p,q\leq n}$ by
> $$M_{pq}=\sum_{I,J\subset S,|I|=p,|J|=q}|W_I\backslash W/W_J|.$$
> **Kapranov–Schechtman's conjecture.** The metamatrix $M(W)$ is totally positive.

The source does not define "totally positive"; it cites Kapranov–Schechtman (SIGMA 16 (2020) 062), whose
appendix by Etingof uses the strict sense: every minor, of every size, is positive. The Lean endpoint
uses this strict sense. The negative minor below refutes the conjecture under the weaker reading
(total nonnegativity) as well.

## 2. Result

**Theorem.** Let $W=D_{27}$ be the group of even signed permutations of $\{0,\dots,26\}$ and $S$ its
standard generators: the 26 adjacent transpositions $s_i=(i\;i{+}1)$ for $0\le i\le 25$ and the signed
transposition $s_{26}$ that exchanges coordinates 25 and 26 and changes both of their signs. (In the
Dynkin diagram, $s_0-s_1-\dots-s_{24}-s_{25}$ is a path and $s_{26}$ is joined to $s_{24}$ only; $s_{25}$ and
$s_{26}$ commute. This is the standard labelling of Björner–Brenti §8.2, with indices shifted to start at 0.) Then the
$16\times16$ submatrix of $M(W)$ with rows $p=0,\dots,15$ and columns $q=12,\dots,27$ has negative
determinant. Hence $M(D_{27})$ is not totally positive (not even totally nonnegative).

The determinant is the 372-digit negative integer

-177306466711536626771337515497899683697197566512061335823881798079333592028056388767849808239592722365511612322844098597976463240291494668097579527774028502061044909834310155002750088744092611510476498063180345190523145017454822632655423237779006021692581095282549120854992010128764401037629714483428419312403562825650992501934374943585770331471615745981924998962662604800

(it equals $\prod_i V_{ii}/\prod_i E_{ii}$ for the certificate of §9 and agrees with the inherited LU
certificate).

**Cited bridge (not formalized).** $(D_{27},S)$ is a Coxeter system of type $D_{27}$: Bourbaki, *Lie
Groups and Lie Algebras*, Ch. VI §4.8; Björner–Brenti, *Combinatorics of Coxeter Groups*, §8.2. The
Lean statement is about the concrete pair; this bridge is what makes it a statement about "the finite
Coxeter group of type D₂₇" in the conjecture. Lean proves that the 27 generators are distinct involutions
that generate the group. It does not prove the Coxeter relations or that they present the group; both are
part of the cited bridge. As a sanity check (not a proof for rank 27), the final review verified the
analogous pairs for $n=2,\dots,5$ by computer: the braid relations of type $D_n$ hold, the concrete group has
the order of the abstract Coxeter group computed in its Tits representation (so the two are isomorphic),
and the concrete double-coset metamatrix equals the one given by the source's descent method (Cor. 3.1.2),
computed in the abstract group. For $n=2$ it equals the source's printed table for $I_2(2)$, and for $n=3$ it
equals the metamatrix of $A_3$. Everything else below is proved in Lean.

## 3. Source definitions and their Lean transcriptions

| Source | Lean (module) |
|---|---|
| $W$, the even signed permutations | `EvenSignedPerm 27`, the kernel of the product of coordinate signs on the semidirect product `(Fin 27 → ℤ/2) ⋊ Perm (Fin 27)` (SignedPerm) |
| $S$ | `simpleD27 : Fin 27 → D27`, 26 adjacent swaps then the signed swap of coordinates 25, 26; proved injective, involutive and generating (Generation, ReflectionChecks) |
| $W_I$, parabolic subgroup of type $I$ | `parabolic s I := Subgroup.closure (s '' I)` (Metamatrix) |
| $\lvert W_I\backslash W/W_J\rvert$ | `doubleCount H K := Nat.card (DoubleCoset.Quotient H K)` (Mathlib's double cosets) |
| $M_{pq}$ | `metamatrix s p q := Σ_{I, \|I\|=p} Σ_{J, \|J\|=q} doubleCount (parabolic s I) (parabolic s J)`, in ℚ |
| totally positive | `TotallyPositive A := ∀ k (r c : Fin k ↪o Fin n), 0 < det (A.submatrix r c)` (strict, all sizes, all increasing row/column choices) |

Non-vacuity checks proved in Lean: `M27 0 0 = |D27| > 0` and `M27 27 27 = 1`.

## 4. Proof: from double cosets to fixed points

Write $G=D_{27}$, $n=27$. Double cosets $H\backslash G/K$ are in bijection with diagonal $G$-orbits on
$G/H\times G/K$ ($HgK\mapsto$ orbit of $(H,gK)$). Burnside's lemma (Mathlib) then gives
$$|G|\cdot M_{pq}=\sum_{g\in G}\chi_p(g)\,\chi_q(g),\qquad \chi_p(g)=\sum_{|I|=p}\#\mathrm{Fix}_{G/W_I}(g).\tag{4.1}$$
(Lean: `M27_gram`, inherited from stage 1.)

G acts on integer vectors $y:\{0..26\}\to\mathbb Z$ by $((t,\pi)\cdot y)_i=t_i\,y_{\pi^{-1}(i)}$.

## 5. Chamber vectors and stabilizers

For $I\subseteq S$ define the chamber vector $x_I$: put $x_{25}=0$ if $s_{25},s_{26}\in I$ and $x_{25}=1$
otherwise; for $j\le24$, $x_j=x_{j+1}+[s_j\notin I]$; and $x_{26}=0,1,-1,0$ according as both, only $s_{25}$,
only $s_{26}$, or neither of $s_{25},s_{26}$ lies in $I$. Then $x_0\ge\dots\ge x_{25}\ge|x_{26}|$.

**Lemma 5.1.** $\mathrm{Stab}_G(x_I)=W_I$ for every $I$. (Lean: `stabilizer_eq_PI`.)

*Proof.* Each $s_i$, $i\in I$, fixes $x_I$ by inspection. Conversely let $g=(t,\pi)$ fix $x_I$. Put
$\Phi(\pi)=\sum_j j\,\pi(j)$. If $\pi\ne1$, $\pi$ has an adjacent descent $\pi(j)>\pi(j+1)$ (a strictly
increasing self-map of a finite chain is the identity). Since $|x|$ is antitone and $g$ preserves $|x|$,
$|x_j|=|x_{\pi(j)}|\le|x_{\pi(j+1)}|=|x_{j+1}|\le|x_j|$, so $j,j+1$ lie in one level of $|x|$; by the
construction the corresponding generator ($s_j$, or for $j=25$ one of $s_{25},s_{26}$) lies in $I$, fixes
$x_I$, and has permutation part $(j\;j{+}1)$. Right multiplication by it raises $\Phi$ by
$\pi(j)-\pi(j+1)>0$; $\Phi\le 27\cdot26^2$, so induction applies. If $\pi=1$, $g$ changes signs only on
zero coordinates of $x_I$; these form a terminal block $\{a,\dots,26\}$ with $s_a,\dots,s_{26}\in I$, and
an even sign change supported there is a product of flips of pairs $\{k,26\}$, each a conjugate of
$s_{26}s_{25}$ by adjacent swaps inside the block. ∎

## 6. Face sets

For $y\in\mathbb Z^{27}$ let $L(y)$ be the set of nonzero values of $|y_i|$, $z(y)$ the number of zero
coordinates and $o(y)$ the number of coordinates with $|y_i|=1$. Define
$$\mathcal F_d=\{y:\ L(y)=\{1..d\},\ (z\ge2 \text{ or } (z=0,\ o\ge2))\}\ \cup\ \{y:\ d\ge1,\ L(y)=\{1..d-1\},\ z=1\}.$$
(Lean: `DFace d`.) This is the set of type-D faces of dimension $d$ (the second part are the "glued" faces).

**Lemma 6.1.** For $|I|=p$ the orbits $G x_I$ are pairwise disjoint and their union is $\mathcal F_{27-p}$.
(Lean: `xI_DFace`, `xI_inj`, `DFace_cover`.)

*Proof.* $x_I\in\mathcal F_{27-|I|}$ by a count of the levels of $x_I$ (they are consecutive) and of its
zeros; $\mathcal F_d$ is $G$-stable because it depends only on the multiset of $|y_i|$. If
$g x_I=x_J$ then $|x_J|=|x_I|\circ\pi^{-1}$ and both are antitone, so $|x_I|=|x_J|$; this determines
$I\cap\{0..24\}$ and the pattern at $\{25,26\}$ up to the case "exactly one of $s_{25},s_{26}$", where $x$ has
no zero and the product of the signs of the coordinates is a $G$-invariant that separates the two.
Conversely, for $y\in\mathcal F_d$ sort $|y|$ decreasingly to $s$; the face conditions force consecutive
levels, $(s_{25},s_{26})\in\{(0,0),(1,1),(1,0)\}$, and these data together with the sign product of $y$ define
a type $I$ with $|x_I|=s$. Two vectors with the same multiset of $\pm$-classes are in one signed-permutation
orbit (fibre-wise bijection), and an odd element can be corrected by a flip at a zero coordinate, or is
excluded by the sign product when there is no zero. The dimension count gives $|I|=27-d$. ∎

With $G/W_I\cong Gx_I$ (Lemma 5.1) this gives (Lean: `parabolicCharacter_eq`)
$$\chi_p(g)=\#\{y\in\mathcal F_{27-p}: gy=y\}.\tag{6.1}$$

## 7. Gluing and relabeling

Let $B_k=\{y: L(y)=\{1..k\}\}$, $Z_k=B_k\cap\{z=1\}$, and write $\chi_X(g)$ for the number of $g$-fixed
points of $X$.

**Lemma 7.1 (gluing).** For $g\in G$: $\chi_{\mathcal F_d}+\chi_{Z_d}+\chi_{Z_{d-1}}=\chi_{B_d}$. (Lean: `gluing`.)

*Proof.* $B_d$ splits by $z$ and $o$; the only part not visibly in $\mathcal F_d\cup Z_d$ is
$C_d=\{L=\{1..d\},z=0,o=1\}$. Split $C_d$ by the sign $u=\pm1$ of its unique entry of absolute value 1. The
map $y\mapsto y-\operatorname{sign}(y)$, applied coordinatewise, is a bijection from $C_d^{u}$ onto $Z_{d-1}$
and commutes with every signed permutation. Its inverse puts $u$ at the zero coordinate and adds the sign
to every other coordinate. Let $g=(t,\pi)\in G$ fix $y'\in Z_{d-1}$. Then $\pi$ fixes the unique zero coordinate
$k$. On each cycle of $\pi$ among the nonzero coordinates, going once around the cycle shows that the product
of the $t_i$ is $+1$. Evenness then forces $t_k=+1$ (stage-1 `singleton_sign_positive`). So both lifts are fixed
and $\chi_{C_d}=2\chi_{Z_{d-1}}$. ∎

Let $W_m=\{y:|y_i|\le m\}$ and $ZW_m=W_m\cap\{z=1\}$. (Notation: in §§7–9, $W_m$ and $ZW_m$ are sets of integer
vectors, not parabolic subgroups, and $G_{WW},G_{ZW},G_{ZZ}$ are orbit counts. The names follow the Lean
identifiers.)

**Lemma 7.2.** $\chi_{W_m}=\sum_k\binom mk\chi_{B_k}$ and $\chi_{ZW_m}=\sum_k\binom mk\chi_{Z_k}$, hence by binomial
inversion $\chi_{B_k}=\sum_i(-1)^{k-i}\binom ki\chi_{W_i}$ and the same for $Z$. (Lean: `chiB_inv`, `chiZ_inv`.)

*Proof.* Partition $W_m$ by $U=L(y)\subseteq\{1..m\}$. An odd relabeling $v\mapsto\operatorname{sign}(v)\,\varphi(|v|)$,
with $\varphi:U\to\{1..|U|\}$ a bijection, commutes with the action, preserves zero coordinates and maps
$\{L=U\}$ bijectively onto $B_{|U|}$. ∎

## 8. Orbits of pairs

By Burnside again, $\sum_g\chi_P(g)\chi_Q(g)=|G|\cdot\#(G\text{-orbits on }P\times Q)$. For $(y,w)$ let
$\mu(y,w)$ be the multiset of the canonical representatives of $\pm(y_i,w_i)$, and $\varepsilon(y,w)$ the
product of the signs of the pairs $(y_i,w_i)$ relative to their representatives if no $(y_i,w_i)=(0,0)$, and
$+1$ otherwise. $(\mu,\varepsilon)$ is a complete invariant for $G$-orbits: equal $\mu$ gives a signed permutation
carrying one pair to the other; if it is odd it can be corrected by a flip at a $(0,0)$ coordinate, and
otherwise $\varepsilon$ changes sign under it. Every multiset arises, and when $(0,0)\notin \mu$ both values
of $\varepsilon$ arise. So the number of orbits is $\#\{\mu\}+\#\{\mu: (0,0)\notin \mu\}$. With the class set
$\mathrm{Cls}(i,j)$ of size $K=2ij+i+j+1$ and stars and bars ($\mathrm{mc}(K,r)=\binom{K+r-1}{r}$):
$$\begin{aligned}
G_{WW}(i,j)&=\mathrm{mc}(K,27)+\mathrm{mc}(K-1,27),\\
G_{ZW}(i,j)&=(j+1)\,\mathrm{mc}(i(2j+1),26)+j\,\mathrm{mc}(i(2j+1),26),\\
G_{ZZ}(i,j)&=\mathrm{mc}(2ij,26)+2\,ij\,\mathrm{mc}(2ij,25),
\end{aligned}$$
for the orbit counts on $W_i\times W_j$, $ZW_i\times W_j$, $ZW_i\times ZW_j$ (splitting off the unique
entry with a zero first coordinate, and then the unique entry with a zero second coordinate).
(Lean: `gram_WW`, `gram_ZW`, `gram_ZZ`.)

## 9. The explicit entries and the negative minor

Combining (4.1), (6.1) and Lemmas 7.1–7.2, with $\alpha_{d,i}=(-1)^{d-i}\binom di$ and
$\beta_{d,i}=-(\alpha_{d,i}+\alpha_{d-1,i})$,
$$M_{pq}=F(27-p,27-q),\quad F(d,e)=\sum_{i\le d}\sum_{j\le e}\big[\alpha_{d,i}\alpha_{e,j}G_{WW}(i,j)+\alpha_{d,i}\beta_{e,j}G_{ZW}(j,i)+\beta_{d,i}\alpha_{e,j}G_{ZW}(i,j)+\beta_{d,i}\beta_{e,j}G_{ZZ}(i,j)\big].$$
(Lean: `M27_eq_Fc`.) The Lean kernel evaluates $F$ for the 256 entries (rows 0–15, columns 12–27) and
finds exactly the integer matrix $A$ of `type-d-minor.csv` (`entries_row_0` … `entries_row_15`,
`decide +kernel`; no `native_decide`). An integer elimination certificate $EA=V$ with $E$ lower triangular
with positive diagonal and $V$ upper triangular with diagonal signs $(+^{15},-)$ is checked the same way, so
$\det E>0$, $\det V<0$ and $\det A<0$ (`det_Aint_neg`, `negativeMinor27`). Since the minor is selected by
the increasing embeddings $i\mapsto i$ and $j\mapsto 12+j$, strict total positivity fails
(`not_totallyPositive_M27`).

Independent check (not part of the proof): the formula of §9 reproduces the brute-force double-coset
metamatrices of $D_4$ and $D_5$ entry for entry (`scripts/verify_orbit_formula.py`).

## 10. Significance

The conjecture is known in type A (Etingof). The source proves it for type B, checks the exceptional types
by computer, and reports Ukraintsev's proof for rank at most 3. The source computes nothing in type D. Its
Remark 2.3.5 leaves open whether its method extends to other types. The present counterexample shows that the
conjecture fails in type D, an irreducible finite real reflection group, so it cannot hold for all finite
Coxeter groups. The independent review found every rank from 2 to 26 strictly totally positive and rank 27
the first failure. The final review reproduced this with the same closed formula (27 replaced by $n$),
validated there against brute-force double cosets for $n\le5$ and the source's descent method for $n=6,7$.
Both used the Gasca–Peña initial-minor test. Ranks 28–30 also fail. None of this rank scan is formalized,
and no claim of minimality is made in Lean. Its relevance is only that no small-rank check, and nothing
within reach of the source's element-by-element method, would have found the failure. The method is standard (orbit counting by Burnside,
type-D gluing, binomial inversion, stars and bars, an exact determinant). The fixed-face content of the
gluing is already in Stembridge's work. The contribution is the explicit high-rank obstruction and its full
machine check from the literal double-coset definition. A specialist may judge the derivation routine (the
review's not-routine estimate is 0.55). The result is not a small-group search: the group has
$2^{26}\cdot27!\approx7.3\cdot10^{35}$ elements.

## 11. Prior art (from the adversarial review, 2026-11-20)

arXiv:2503.02213 has only v1 and no journal version was found; its §§1–3 were read. The source proves type
B (Etingof's Gauss-decomposition method) and checks the exceptional types by computer; it computed nothing in
type D. Kapranov–Schechtman (SIGMA 16 (2020) 062) state the extension to reflection groups as "seems likely".
Omega issue/PR searches for "2503.02213", "contingency metamatrix" and "Kapranov Schechtman" returned nothing,
web search found nothing on type D, and the source has zero recorded citations. The fixed-subcomplex
h-polynomials of the type-D Coxeter complex are Stembridge's (FPSAC 1992 Props. 1 and 3; 1994 Lemma 9.1, as
reported by Yang–Zhang §5); this paper claims no originality for them. A refresh on 2026-11-21 found nothing
new. The arXiv abstract page still shows only v1, with no journal reference. OpenAlex lists no citing work.
Kapranov–Schechtman's later paper *Parabolic induction and perverse sheaves on W\h* (Adv. Math. 2022,
arXiv:2006.04285v2) treats the two-sided Coxeter complex for general W but does not discuss total positivity
of the metamatrix. The other works citing Kapranov–Schechtman 2020 (PROBs I–II, Lorentzian lower bounds for
contingency tables) are about other questions. There were no further papers by the three authors on the
topic. The omega issue tracker, GitHub code search, the Principia, mio-qwq and openai/math archives, and the
ReuF2F benchmark (cmu-l3/reuF2F) have no entry for this conjecture. These checks are bounded and do not
establish exhaustive priority.

## 12. Formal statement

```lean
theorem TypeD.not_totallyPositive_M27 : ¬ TypeD.TotallyPositive TypeD.M27
theorem TypeD.negativeMinor27 :
  (TypeD.M27.submatrix ⇑TypeD.minorRows ⇑TypeD.minorCols).det < 0
-- 'TypeD.not_totallyPositive_M27' depends on axioms: [propext, Classical.choice, Quot.sound]
```
All 39 modules and their statements are listed in LEAN-SOURCE-APPENDIX.md; REPORT.md has the receipts.
