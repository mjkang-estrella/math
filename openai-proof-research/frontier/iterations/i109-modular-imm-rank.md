# I109 — modular IMM rank: original audit and two paid mechanisms

**Disposition: no substantial finding nominated. Eight accepted findings remain eight.** The original new I106 claims A106, A1 (both bounds), B106, B1, B2 and C106 receive **ORIGINAL PASS WITHOUT REPAIRS**, separately and within their stated scopes. The original scoped obstructions also pass. This is an independent agent audit under the accepted premises, not human review or formal certification.

The all-prime balanced IMM gate lower bound remains **unproved and unrefuted**. This iteration develops two further mechanisms in the actual coefficient-one contraction map. P109 constructs one compatible periodic-occupation identity minor, rather than adding overlapping minors. Its exact size improves the old certificate but remains exponentially small uniformly over the corridor width and period. E109 gives an exact rank-generating decomposition of an independent-excursion degeneration. N109 then proves that **even the entire rank of this degeneration**, not merely a chosen Boolean minor, is at most

`D exp(−(log(4/3)/2)n + O(√n+log n))`

in characteristic two. Both mechanisms have complete circuit comparisons and paid losses. Neither attains the necessary scale. The balanced modular-rank branch is **parked pending a mechanism retaining interaction between excursions or a genuinely adequate aggregate modular-rank estimate**. The original target itself is not parked as false.

## 1. Contract, frozen originals and source boundary

Accept all theorems and lower proof operations in `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. No upstream truth audit or contradiction synthesis is used. AGENTS.md and the **complete additional_instructions field** of `iteration109-modular-imm-rank-task.json` were read before mathematical work. The four ledgers were consulted at their current-status and relevant branch passages, then frozen. I107/I108 working outputs are not dependencies. No children, shared edits, staging, commits or publication occurred.

The frozen I106 report has SHA-256 `8e217586e78abc4e70db3a2e37ae3c03eb2715c9c30c567ea8d4a8733f6fcda0`; its seal has SHA-256 `07ef9184bb8484e4e90677f4bd8781f574c52f538542ee095d8a0dae91129e43`. The complete I109 task, launch brief, additional directions, original I106 brief (including the inherited I103 originals), report and finalized parent response are preserved. Separator whitespace is preserved in the extracted verbatim sections; report equality is checked after stripping separator whitespace, and the separately frozen report preserves its actual original bytes. The I106 and I103 seals and their complete inventories are replayed in place, including the inherited originals, without another corpus copy. Their evidence PASS records are not mathematical-proof verdicts.

The complete mapping is reused: 13,223 tree entries, 749 manuscripts, 10,373 original positions (9,340 I14 originals and 1,033 augmented positions, including the inherited PDF extracts). The inherited full I106 occurrence multisets and its 83-record refined screen are replayed. A new exact expression for IMM, contraction, divided-power, Smith and inclusion-matrix mechanisms retains 132 occurrences. Most Smith/divided-power hits concern unrelated subjects. The IMM/depth-five clause selects H below. This is **lexical coverage, not a semantic reading of all 749 manuscripts**. The complete tree/title and documented relevant-companion screen did not reveal a stronger pinned all-prime balanced-IMM theorem.

New reading records use UTF-8 `split('\n')`, one-based inclusive LF ranges, with one appended LF for passage hashing. Form feeds stay inside LF lines. Inherited lexical searches use `str.splitlines()` and retain exact match offsets and multiplicities; these conventions are not interchanged. All six substantive H sections were read through their endings. The original I106 mathematics in the verbatim task/report is the proof being audited; its closed I103 audit is retained rather than reopened.

Primary literature was checked on 2026-10-10. The actual comparison passages, rather than search snippets, were read:

* **H**, [Homogeneous depth-five lower bounds for iterated matrix multiplication](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Homogeneous-depth-five-lower-bounds-for-iterated-matrix-multiplication-September-25-2026), §§1–6: unrestricted-bottom, shared-gate, balanced characteristic-zero result; every-field circuit upper estimate. Its full complex lower proof uses positive trace moments. It is not a modular rank theorem.
* Limaye–Srinivasan–Tavenas, [ECCC TR21-081 revision 1](https://eccc.weizmann.ac.il/report/2021/081/revision/1/download/), actual Corollary 3: all fields but degree `d≤log(w)/100`. The retained revision is the comparison contract.
* Amireddy–Garg–Kayal–Saha–Thankey, [arXiv:2211.07691v1](https://arxiv.org/abs/2211.07691v1), Theorem 4.10 and its complete proof: `2^(−O(d))w^(Ω(√d))` for homogeneous product-depth-two formulas with `w=ω(d)`. Current arXiv metadata still lists only v1. Formula unfolding cannot remove the degree loss or the width condition.
* Forbes, [CCC 2024](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2024.31), Lemma 5 and Theorem 10 through its proof ending: low-degree all-field bounds and transfer of **vanishing** rank minors. A large unit minor on the hard polynomial is a separate input. These operations do not transfer H's nonvanishing rational minors.
* Bera–Chakrabarti, [CCC 2015](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CCC.2015.183), Theorems 1.1/4.2, completion and support-barrier discussion: width `d^q` and bounded bottom support. Armand–Behera–Tavenas, [ECCC TR26-104](https://eccc.weizmann.ac.il/report/2026/104/), Theorem 1.1, Corollary 1.3 and completion: NW-family bounds over each fixed finite field, with field-dependent exponential rate. Neither supplies this target.
* Ghorbani–Khosrovshahi–Maysoori–Mohammad-Noori, [Inclusion Matrices and Chains, arXiv:0709.3144v1](https://arxiv.org/abs/0709.3144v1), complete paper, especially Theorem 1, equation (8) and Corollary 3 through their proof endings: integral basis changes give Wilson's diagonal entries `binom(k−i,t−i)`, with multiplicity `binom(v,i)−binom(v,i−1)`. It pays the Boolean inclusion-block calculation, not a decomposition of the full IMM map. The new local Boolean formulas below are also proved directly. Only this PDF was newly downloaded/extracted; the other full-text passages reuse sealed extracts.

Source URLs, versions, byte hashes and read ranges are in the adjacent manifests. PDF-byte binding does not certify extraction accuracy. No pinned PDF was re-extracted. The named significance context remains Valiant's IMM problem; the broader conjecture is not solved here. No worldwide-priority or numerical importance claim is made.

## 2. Exact model and notation

Use H's parameters and schedule without changing width, degree, ambient variables or size:

```
s = largest integer ≤ √n with s ≡ n (mod 2)
k=(n−s)/2, m=(n+s)/2, v=kn², u=mn², ρ=k/m, λ=k/n
h(r,A)=binom(r+A−1,A)
a=ceil(v/(√n−1)), α=a/(a+v)
b=ceil(u α^ρ/(1−α^ρ)), β=b/(b+u)
D=h(v,a)h(u,b), q=α^((1+ρ)/2)
schedule = VU^(ℓ₁) … VU^(ℓ_k)
ℓ_i=1+floor(is/k)−floor((i−1)s/k) ∈ {1,2}.
```

For all sufficiently large n, `a,b=Θ(n^(5/2))`, `α=n^(−1/2)exp(O(1/a))`, `α≤β≤2/√n`, `k/n∈[.49,.5]`, and `s≤√n`. All thresholds and implicit constants below are absolute unless explicitly stated otherwise.

On the divided-power-indexed vector space with basis `e_ν`, `|ν|=A`, define **coefficient-one contraction** `c_i e_ν=e_(ν−e_i)` if `ν_i>0`, and zero otherwise. These commute. Ordinary multiplication acts on a separate U polynomial ring. The finite map is

`F^c_f=f_[k,m](c_V,U): Γ_V(a)⊗F[U]_b → Γ_V(a−k)⊗F[U]_(b+m)`.

This is an algebra representation on the full graded module, followed by a finite bidegree choice; it is not naive substitution of Hasse derivatives. In particular `(c_x+c_y)^p=c_x^p+c_y^p`, while `c_x^p` can be nonzero.

The circuit has five computational layers `ΣΠΣΠΣ`, arbitrary field constants on sum inputs, arbitrary bottom linear support/fan-in, arbitrary sharing and finite fan-out. Positive-degree product inputs count with multiplicity. Size S counts vertices, including leaves; the argument also works with computational gates alone. It concerns formal polynomials, not functions on a finite field.

The audited circuit estimate is

`rank_F F^c_f ≤ 2S² D exp(C√n) n^(−√n/100).`                    (CU)

Thus a lower rank `D exp(−L(n,p))` would give

`S ≥ 2^(−1/2) exp(−(L(n,p)+C√n)/2) n^(√n/200).`              (COMP)

For a uniform positive gate exponent, it is sufficient that `L(n,p)≤(1/100−ε)√n log n` for one absolute `ε>0`. The stronger `L=O(√n)` target remains sufficient, not necessary. A loss of order n is too large.

## 3. Separate audit of ORIGINAL I106 proofs

The following verdicts apply to the original proofs before the constructions in §§5–7. No new argument below is inserted into I106 to earn a pass. There are **no repairs required**. The elaborations here check the steps that the original already states.

### A106 — ORIGINAL PASS WITHOUT REPAIRS

For corridor width `1≤t≤n`, the active variable counts are exactly

`v_c=t+(k−1)t²`, `u_c=t+(m−1)t²`.

The first V layer has fixed incoming endpoint; the last U layer has fixed outgoing endpoint. There are `t^(2k−1)` independent V-edge choices. Every choice has an active completion, using vertex 1 in a two-U gap. A chosen U completion determines all the V edges because there are no adjacent V layers, including the first fixed endpoint. This proves injectivity of the completion selector.

The selected columns have active V degree k and active U degree zero; the selected rows have active V degree zero and active U degree m. A nonzero selected entry must therefore differentiate all k active V variables and multiply all m active U variables. It cannot touch ballast in either group. The U completion then forces the V choice, and equality of the remaining monomials forces equality of the ballast labels. Consequently the selected submatrix is exactly the identity over Z, of order

`J_t=t^(2k−1)h(v−v_c,a−k)h(u−u_c,b)`.

Every active differentiated exponent is one, so this holds for the ordinary and contraction maps. Inactive endpoint variables belong to the ballast, not the active count. For sufficiently large n, complementary variable counts are positive even at t=n. No prime, factorial, or coefficient-field condition is missing.

### A1 lower budget — ORIGINAL PASS WITHOUT REPAIRS

For `t=floor(n^(1/4))`, the original exact ratios give

`J_t/D ≥ t^(2k−1)α^k exp(−2k²/a−2a v_c/v−2b u_c/u)`.

Here `(a−k+1)/(a+v)≥α exp(−2k/a)` eventually; `v_c/v,u_c/u=O(n^(−3/2))`; and `a,b=Θ(n^(5/2))`. Also `t≥n^(1/4)/2`, `α≥n^(−1/2)`, so the prefactor is at least `2^(−2k+1)n^(−1/4)`. Each remaining logarithmic cost is O(n) or smaller. The conclusion `rank≥D exp(−C_A n)` has one field-independent constant and threshold. It is a genuine all-field partial, with the loss explicitly too large for COMP.

### A1 uniform upper bound on the certificate — ORIGINAL PASS WITHOUT REPAIRS

The original upper binomial ratios imply

`J_t/D ≤ t^(2k−1)(a/(a+v−1))^k exp(−(a−k)v_c/(v+a−k)−b u_c/(u+b))`.

Write `x=t²/√n`. Since `v_c≥(k−1)t²` and `u_c≥(m−1)t²`, the penalty is at least `.8nx`, uniformly over `1≤t≤n` for sufficiently large n. The logarithm of the prefactor is `k log x−log t+o(1)`; the o(1) comes from `k/a` and `k/(a+v)`, independent of t. With `κ=k/n∈[.49,.5]`,

`max_(x>0) [κ log x−.8x]=κ(log(κ/.8)−1)<−.73`.

Thus the original weaker `exp(−.7n+o(1))` upper bound holds with slack. It bounds **J_t**, not the actual rank. There is no rank upper bound inferred from one small minor.

### B106 — ORIGINAL PASS WITHOUT REPAIRS

On the full contraction/U module, polynomial substitution respects products, including repeated factors and small-characteristic identities. The homogeneous dimensions are the same h(v,A), h(u,B) used by H. For each bidegree assignment of factors Q_j, put `δ_j=i_j−λe_j` and apply positive discrepancies first. The intermediate space has degrees `(a−I,b+J)`, with `I≤k`, `J≤m`; its dimension ratio is at most

`2α^(I−ρJ)=2∏q^|δ_j|`.

Subadditivity over assignments and dropping the sum constraint give `2D∏H_(e_j)`. No Leibniz or characteristic-zero step is needed. I read H's entire rank and circuit sections to check the interface rather than only its final inequality.

For all-small factors, the source's integer-distance estimates give `2D exp(C√n)n^(−√n/20)`. For one large factor occurrence, expanding that occurrence costs at most S and exposes its linear factors, giving `2SD exp(C√n)n^(−3√n/160)`. Other occurrences of the same shared gate remain unexpanded. There are at most S distinct predecessors of the output sum. Combining parallel sum wires, absorbing degree-zero factors and discarding zero contributions gives CU. Bottom linear support never enters. Sum coefficients are free; product multiplicities remain in the degree sum. Thus the original S² charge is for the stated gate convention, not wires or an unfolded formula.

### B1 — ORIGINAL PASS WITHOUT REPAIRS

Over Q, `e_ν↦V^ν/ν!` is an invertible degreewise change of basis intertwining contractions and derivatives. Over characteristic p the same comparison works if `p>a`; it compares the two maps in that field and does **not** compare their rank to rational rank.

For the every-characteristic dominance assertion, replacing the lowering coefficient at positive occupation j by `j+z` gives a polynomial matrix specializing to the derivative map at z=0. On the generic fiber, the basis scaling by `∏_(i)∏_(j=1)^(ν_i)(j+z)^(-1)` intertwines it with coefficient-one contractions. Each factor is a nonzero polynomial even if some j vanishes in the field. Specialization cannot increase rank. This proves ordinary rank ≤ contraction rank with arbitrary polynomial coefficients and the fixed finite spaces. No missing factorial invertibility was used.

### B2 Boolean and balanced torsion claims — ORIGINAL PASS WITHOUT REPAIRS

For `Σv_i u_i`, each combined occupation `ν_i+η_i` is preserved. On the all-one sector, the map from V degree p to p−1, for `r=2p−1`, is the stated adjacent-subset inclusion matrix. Each row contains p ones, yielding a nonzero all-ones kernel vector modulo p. On real Boolean spaces, `DU−UD=(r−2j)I`, with `U=D*`. At j=p, a vector killed by D would have `||Ux||²=−||x||²`, forcing it to be zero. Equality of middle-level dimensions proves rational nonsingularity. This uses positivity only to establish the rational comparison of this explicit block, not a modular rank lower bound.

The balanced three-by-three minor also works as written. The first VU pair can traverse three intermediate vertices and return to 1. All later edges are fixed, including an extra U edge when the first gap is two. Selected exponent shifts force those exact paths. Inactive endpoint variables supply the remaining degrees once `a≥k+1,b≥1`, which holds at the stated sufficiently-large-n scope. Both operators have the same off-diagonal-one matrix, determinant 2. Therefore total unimodularity is false. It does not exclude a different large unit minor.

### B2 edge-scaling and naive Hasse obstructions — ORIGINAL PASS WITHOUT REPAIRS

A variable scaling multiplies each path coefficient by its edge monomial. For fixed rows and columns of any minor, the total signed exponent shift is fixed, so all determinant terms acquire the same monomial factor. Equivalently the matrix is multiplied by invertible diagonal row and column matrices over the parameter field. A fixed bad minor cannot be cured by edge weights. Degenerating some weights to zero can only **lower** rank; §6 uses that distinct operation honestly.

The identity `D^[1]D^[1]=2D^[2]` falsifies the naive Hasse substitution as a polynomial-algebra homomorphism, already in characteristic two. It does not refute B106's different module or every possible divided-power measure.

### C106 inequality and gate corollary — ORIGINAL PASS WITHOUT REPAIRS

The contraction matrix has entries 0/1: a row-column shift determines every edge in a path. A column has at most `L_n=n^(n−1)` nonzero entries. A nonzero rational-rank-size integer minor B therefore has `|det B|≤L_n^(r_n/2)` by its column norms. If the whole matrix has mod-p rank s<r_n, unit elimination over `Z_(p)` leaves an `(r_n−s)`-square block divisible entrywise by p. Hence `p^(r_n−s)|det B`. This gives precisely

`rank_F F^c_IMM ≥ max(0,r_n(1−log L_n/(2 log p)))`.

Extension from the prime field preserves this integer matrix's rank. B1 and the accepted H lower rank give `r_n≥D exp(−C_H√n)`. At `p≥L_n` the retained fraction is at least 1/2. CU and square roots yield the original `S≥n^(√n/400)` eventually, with absolute constants. For every fixed p the hypothesis fails eventually. The original report correctly avoids claiming a fixed-field asymptotic theorem.

## 4. Full-scope contribution comparison of I106

I agree with the technical disposition, for concrete reductions. A106 is an explicit support restriction and coefficient-one pivot extraction from H's path expansion; the exact counts are products of freely chosen internal vertices and symmetric-power ballast dimensions. Its asymptotic estimates use H's already-paid parameter bounds and elementary binomial ratios. B106 replaces the module but preserves precisely the polynomial-algebra, graded-dimension and bidegree-factorization interface of H's complete shared-circuit proof; no new circuit-decomposition theorem remains. B1 is an explicit diagonal conjugation followed by specialization. B2 is a concrete inclusion block and a frozen-path embedding, with the edge-scaling diagonal equivalence. C106 combines the accepted rational rank with these paid interfaces and Hadamard/p-divisibility for one integer minor.

This reduction covers all fields, arbitrary circuit constants, unrestricted bottom forms, sharing, repeated wires, actual rank dimensions and the quantitative prime threshold. It is not an argument from the mere availability of classical tools or absence of duplicate titles. None of the original partials establishes the new uniform modular-rank bridge. The fresh constructions below are likewise retained as technical partials and scoped method obstructions, not nominations.

## 5. Route I: compatible periodic occupation pivots

The first attempt is to combine many copies of A106 without overlaps. Keeping active ballast zero is unnecessarily restrictive; letting it vary arbitrarily destroys the old diagonal argument. A residue lattice gives an intermediate construction whose compatibility can be proved.

For integers `r≥c≥0`, `A≥0`, `L≥2`, define

`H_L(r,c;A)=[z^A](1−z)^(−(r−c))(1−z^L)^(−c)`.

This counts degree-A monomials whose exponents on c designated variables are multiples of L, without restriction on the other variables. Use the corridor and one completion u(q) for each V monomial q exactly as in A106.

**P109 (author proof).** The contraction matrix contains an identity submatrix of order

`P_(t,L)=t^(2k−1) H_L(v,v_c;a−k) H_L(u,u_c;b)`                (P)

for every `1≤t≤n`, `L≥2`. It works over every field with the same rows and columns. For the ordinary derivative matrix, the same submatrix is diagonal with entries congruent to 1 modulo any prime dividing L. In particular L=p gives a prime-dependent unit minor of the same order.

**Proof.** Let r,z range over the two counted baseline monomials; their active exponents are multiples of L. Select column `(qr,z)` and row `(r,u(q)z)`. A column's active V residues are 1 on q and zero elsewhere; an output row's active V residues are all zero. Since a path lowers exactly one variable in each V layer, it must lower exactly q. It cannot lower an active variable absent from q (that would leave residue L−1) or a ballast variable (a residue 1 would remain). The analogous U residues force the path to multiply exactly the active completion in its selected output row. That completion uniquely determines q. Equality after these shifts then forces equality of both full baseline exponent vectors. This also proves that the selected columns and rows are separately distinct; baseline changes by multiples of L cannot hide a changed 0/1 path residue.

All surviving contraction coefficients are one, so all baselines and path choices together form **one identity submatrix**. For ordinary derivatives the diagonal is the product, over its k V edges, of numbers `Lγ_e+1`; modulo a prime dividing L each factor is one. This is not an addition of ranks of overlapping minors. ∎

The coefficient formula is explicit:

`H_L(r,c;A)=Σ_(j=0)^floor(A/L) h(c,j)h(r−c,A−Lj)`

with `h(0,0)=1` and `h(0,j)=0` for j>0. Consequently `P_(t,L)≥J_t`. Taking `t=floor(n^(1/4))` retains the field-uniform lower estimate `D exp(−O(n))`, now allowing nonzero active ballast. Even choosing the period depending on p is allowed.

Here is the **paid obstruction to this larger family**, uniformly over both free parameters. We first record a coefficient estimate used again in Route II.

**Coefficient normalization.** Put `M_n=(8a+4)(8b+4)=O(n^5)`. For any power series G with nonnegative coefficients convergent at (α,β),

`[x^a y^b]G / D ≤ M_n G(α,β)(1−α)^v(1−β)^u`.              (SAD)

To prove it, the distribution `Pr(N=j)=h(r,j)(1−z)^r z^j` has mean A when `z=A/(A+r)`. At the source parameters `0<A<r`, its unique mode is A−1, and `Pr(N=A)/Pr(N=A−1)=1−1/(A+r)≥1/2`. Markov's inequality gives mass at least 1/2 in `0,…,2A`; hence its maximal atom is at least `1/(4A+2)` and its atom at A at least `1/(8A+4)`. Apply this separately to (v,a) and (u,b). A nonnegative coefficient is at most the evaluated series divided by its monomial weight, proving SAD. No asymptotic saddle-point theorem is assumed.

Apply SAD to `t^(2k−1)x^k` times the two generating functions in P. Since L≥2,

```
P_(t,L)/D
 ≤ M_n t^(2k−1)α^k
   ((1−α)/(1−α^L))^v_c ((1−β)/(1−β^L))^u_c
 ≤ M_n t^(2k−1)α^k (1+α)^(-v_c)(1+β)^(-u_c).
```

With `x=t²/√n`, the logarithm of the power prefactor is `k log x−log t+o(1)`. Since β≥α,

`v_c log(1+α)+u_c log(1+β) ≥ .8nx`

uniformly for large n: use `v_c+u_c≥(n−2)t²` and `log(1+α)≥n^(−1/2)−O(n^(−1))`. The same one-variable maximization as in the original A1 audit gives

`P_(t,L)/D ≤ exp(−.7n+O(log n))`                             (P-loss)

for every t,L, with absolute constants. The period may grow with n or p without affecting this bound. Thus compatible active-ballast sectors improve exact counts but cannot close COMP. Their failure is now proved for the larger compatible family rather than inferred from the old minor.

## 6. Route II: independent excursions and an exact modular rank series

This route attempts to pay much more local rank than the corridor by retaining complete occupation sectors, including collisions and torsion. It first isolates a structured degeneration of the **actual** map, then analyzes its entire rank.

For each VU chunk i retain V edges `1→j` and the first U edges `j→1`, `j∈[t]`. In a two-U gap retain also its last U edge `1→1`. Set all other path variables to zero in the polynomial. With distinct variables renamed, the resulting polynomial is

`g_t = z · ∏_(i=1)^k (Σ_(j=1)^t v_(i,j)u_(i,j))`,           (EX)

where z is the product of the s extra-U connector variables. The original ambient V,U sets remain of sizes v,u. No width-degree replacement is made.

**E109 (author proof).** For every field,

`rank F^c_IMM ≥ rank F^c_(g_t)`.

For characteristic p define the nonnegative formal series

`R_(p,t)(x,y)=Σ_(d,e≥0) r_(p,t)(d,e)x^d y^e`,

where `r_(p,t)(d,e)` is the rank of `L_t=Σ c_(v_j)u_j` from V degree d and U degree e to degrees d−1,e+1 (zero if d=0). Then the exact rank of EX is

`rank F^c_(g_t)=[x^a y^b](1−x)^(-(v−kt))(1−y)^(-(u−kt)) R_(p,t)(x,y)^k`.    (ER)

Its coefficient depends only on the prime, not the extension coefficient field.

**Proof of degeneration and exact decomposition.** Scale each forbidden edge variable by a parameter τ and each retained variable by 1. For τ≠0, the mixed contraction matrix is diagonally equivalent to the original matrix over F(τ). Indeed, give exponent vector `(ν,η)` signed weight `−Σ_V w_eν_e+Σ_U w_eη_e`; its output minus input weight is the edge weight of the contributing path. At τ=0 the entries specialize to EX. Nonzero minors cannot be created by specialization, yielding the stated direction of the rank inequality. This uses edge scaling to produce a lower-rank comparison, not to repair torsion in a fixed minor.

For one pair group, every combined occupation `h_j=ν_j+η_j` is invariant. Fixing h identifies its space with

`A_h=F[z_1,…,z_t]/(z_1^(h_1+1),…,z_t^(h_t+1))`,

via `e_ν U^η ↔ z^η`; the operator is multiplication by `z_1+…+z_t`. It is coefficient-one, including at the boundary η_j=h_j. Its degree-e map is exactly the local contraction map. This gives a direct sum over h, not a matching argument without cancellation control.

Different groups in EX use disjoint variables. Fix their local d_i,e_i and each ballast exponent vector. The whole map is a tensor product of the k local maps; multiplication by z injects the ballast monomial space into itself with a fixed shift. Different data go to different direct-sum target sectors, since local degrees shift by exactly (−1,+1) and ballast shifts are fixed. Thus ranks multiply within sectors and add across sectors. Counting the ballast bases gives ER, including all active occupations, all repeated powers and connector variables. ∎

Since `r_(p,t)(1,0)=t` (an identity matrix), ER immediately yields the all-field lower bound

`rank F^c_IMM ≥ t^k h(v−kt,a−k)h(u−kt,b)`.                    (EX-low)

Taking `t=floor(√n/2)` gives `D exp(−O(n))`. Explicitly the same binomial ratios as A1 bound its ratio below by

`t^k α^k exp(−2k²/a−2a kt/v−2b kt/u)`.

Here tα is bounded below by an absolute positive constant, and the last two costs are O(n). This lower estimate is weaker than the desired scale but is unconditional and has no characteristic dependence.

There is also an exact and useful Boolean-sector computation. For a local h with r entries one and the rest zero, the degree map is the r-element adjacent-subset inclusion map. Select columns containing a fixed distinguished element and rows not containing it; the diagonal blocks give an identity minor of size `binom(r−1,d−1)` for V degree d. In characteristic two this is the exact rank: in the squarefree algebra, multiplication by the sum has square zero and contraction at the distinguished variable gives `Lh+hL=I`. Equivalently the tensor complex is acyclic, and induction from its lowest degree gives ranks `binom(r−1,d−1)`. Summing over r and d gives the local rank series

`B_t(x,y)=x((1+x+y)^t−1)/(x+y)`.

It is a polynomial despite the displayed quotient. For every prime it is coefficientwise a lower bound on R_(p,t); in characteristic two it is the exact contribution of these Boolean sectors. This computation agrees with the classical inclusion-matrix diagonal form. ER is not restricted to this Boolean part: the next section controls all remaining occupations as well.

## 7. Full-excursion filtration: an exponential characteristic-two obstruction

It is tempting to hope that adding the non-Boolean sectors restores nearly all the local rank and makes ER adequate. The following bound rules that out for this entire degeneration at H's actual occupancy scale.

**N109 (author proof).** Uniformly for `1≤t≤n`, all sufficiently large n, and every field of characteristic two,

`rank F^c_(g_t)/D ≤ M_n (3/4+80/n)^k`

and hence

`rank F^c_(g_t) ≤ D exp(−(log(4/3)/2)n+O(√n+log n))`.         (N)

This is an upper bound on g_t's **full** contraction rank. It is not an upper bound on the full IMM rank.

**Proof.** In the invariant sector A_h of §6, if every `h_j≤3`, characteristic two gives

`L_t^4=(z_1+…+z_t)^4=Σz_j^4=0`.

We need a weighted rank bound, not just an ungraded Jordan count. A nilpotent operator raising degree by one admits a basis of homogeneous Jordan chains. One direct proof chooses a homogeneous vector v of maximal chain length ℓ. Choose a homogeneous linear functional λ on the final degree with `λ(N^(ℓ−1)v)=1`. Since N^ℓ=0, the map

`π(w)=Σ_(j=0)^(ℓ−1) λ(N^(ℓ−1−j)w) N^jv`

is a graded N-equivariant projection onto this chain: degrees force its value on N^iv to be N^iv, and the commutation identity follows by shifting the sum. Its graded invariant kernel permits induction. This proves the required homogeneous chain decomposition without assuming semisimplicity or characteristic zero.

Evaluate source-degree weights at x=α,y=β. In a chain of length ℓ the consecutive weights have ratio β/α≥1, because total combined degree H is fixed while U degree rises and V degree falls. The rank in each source degree counts exactly nonterminal chain vectors. The terminal vector has at least the average chain weight. If ℓ≤4, the weighted sum of ranks is therefore at most 3/4 of the weighted dimension of that chain, and hence of the entire good sector.

The full local source-dimension series is

`G_t(x,y)=((1−x)(1−y))^(−t)`.

After normalization at (α,β), the ν_j and η_j are independent geometric variables with respective ratios α and β. Since α≤β≤1/2,

```
Pr(ν_j+η_j≥4)
 ≤ Σ_(r≥4)(r+1)β^r
 = β^4(5−4β)/(1−β)^2
 ≤20β^4.
```

The union bound and `β≤2/√n` show that sectors with some h_j≥4 have at most `320t/n²≤320/n` of the weighted dimension. On these bad sectors use rank ≤ source dimension, paying them in full. Thus

`R_(2,t)(α,β)/G_t(α,β) ≤ 3/4+(1/4)(320/n)=3/4+80/n`.

This accounts for every sector, not just typical sectors informally. Multiplying the k factors in ER and evaluating the two ballast series leaves exactly `(1−α)^(-v)(1−β)^(-u)` times the k-th power of this ratio. SAD gives the first assertion of N. Finally `log M_n=O(log n)`, `k=(n−s)/2` and `s=O(√n)` give the displayed exponent with its absolute error term. ∎

The cutoff 4 is necessary for this argument. On the one-variable sector h=(2), multiplication by z has rank 2 on dimension 3, so the nilpotence-two/rank-one-half assertion is false. Occupations two and three are included in the proved good sectors; large occupations are paid through the explicit tail estimate. This prevents a silent squarefree approximation.

The proof extends as a local observation: if all h_j<q with q a p-power, then L^q=0, and the same chain argument gives weighted rank fraction at most `1−1/q` whenever β≥α. A tail budget must be paid before multiplying many factors. N uses q=4,p=2 and pays it uniformly; no all-prime extrapolation is needed to disqualify this degeneration for an all-prime target.

## 8. Circuit comparison, classification and exact unpaid bridge

Both routes operate on the same F^c with exactly H's a,b,k,m,D. Thus CU, whose entire circuit interface was independently audited, applies with no new support bound, formula unfolding, field-presentation assumption, or gate/wire conversion. For P109 insert `P_(t,L)/D` into COMP. For E109 insert the exact ER ratio, or the unconditional EX-low bound. The results have loss O(n), which overwhelms `√n log n/100`. More decisively, P-loss and N show that optimizing t, choosing p-dependent periods, or computing every local Smith factor of the independent-excursion model cannot make these particular constructions pay the target.

The two new reductions are concrete. P109 uses residue-separated baseline coordinates and the old completion selector, with an explicit generating function and coefficient normalization; its unit minor is one actual compatible object. E109 uses an actual zero-weight degeneration and conserved pair occupations, with exact tensor/direct-sum rank accounting. N109 adds a weighted homogeneous-Jordan filtration and an explicit geometric tail bound. The Boolean component is already covered by the primary inclusion-matrix operations. The rest consists of the displayed elementary representation and counting steps. These are useful technical estimates and method obstructions, not a substantive all-prime lower bound or a ninth finding.

Neither route can be promoted by summing independently chosen minors from different corridors. Nor does diagonal rescaling add independent coefficients to a bad determinant. The positive trace proof remains a rational-rank input only. The new degeneration is highly structured and much simpler than IMM; its small characteristic-two rank does not imply a small circuit for IMM.

The unpaid sufficient inequality remains

`rank_(F_p) F^c_IMM ≥ D exp(−C₀√n)`

for one absolute C₀ and every prime, or the explicitly weaker loss threshold in COMP. A valid continuation would have to retain enough interaction across the reset vertices removed in EX, or establish independence of a much larger family of occupation sectors. Joining excursions into blocks might reduce the number of local losses, but no near-full modular rank bound for such a block is established here. Applying the current corridor estimate inside every block still sums an O(n) loss; it does not resolve the missing estimate. There is presently no viable paid continuation of these two mechanisms. **Park this rank-construction branch; retain the exact target as open under the accepted premises.**

## 9. Evidence, diagnostics and final read-only validation

Only `frontier/iterations/i109-modular-imm-rank.md`, `frontier/sources/i109_modular_imm_rank/` and `frontier/experiments/i109_modular_imm_rank/` were written. The final verifier is run from the repository root with

`python -B frontier/experiments/i109_modular_imm_rank/verify.py`.

It is offline and read-only, including an audit hook rejecting file writes, process launches and sockets. It verifies the exact owned inventory and hashes, original report/brief/parent equality, I106/I103 seals and full inherited original mapping and lexical records, the new exact occurrence multiset, LF reading hashes, external byte bindings, and reproducible finite diagnostics. Only the live `README.md`, `frontier/README.md`, `frontier/TEN-FINDINGS.md` and `frontier/iterations/README.md` may drift; their frozen snapshots cannot. No download, bytecode, PDF re-extraction, repair or reseal is performed by the verifier. Preparation/validation occurs before one final seal.

The new pure diagnostics construct actual periodic minors in VU, VUU and VUVU maps, test Boolean ranks through r=9, check 84 weighted nilpotent occupation sectors, and compare the complete excursion rank formula with explicitly generated matrices in nine cases over F₂,F₃,F₅. Ordinary diagonal residues are checked separately from contraction coefficients. These are finite diagnostics, not universal proof or acceptance certification.

Retained preparation events include truncated broad file/ledger searches (not counted as complete reading), a nonexistent guessed `05-path-sum.tex` filename (correctly resolved to `05-paths.tex`), and the initial `rg --files` omission of ignored source paths (resolved using `--no-ignore`). The supplied launch-tool size rejection remains in the frozen parent task. Preseal validation and any failures are recorded before the seal. Evidence identity, mathematical audit and substantiality remain separate claims.
