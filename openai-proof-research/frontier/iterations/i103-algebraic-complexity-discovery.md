# I103 — algebraic complexity and exact constructions

**Disposition: no substantial finding nominated.** This fresh scout develops an author-level, all-positive-characteristic rational hitting-list construction (G103), including simultaneous expression-domain conditions and prime-field output, and an author-level every-field transfer of the 9/4 matrix-multiplication exponent (T103). Both are classified here as **technical under the accepted lower-operation standard**. G103 is a complete construction, not a conditional missing-lemma proposal; its reduction to the two pinned hitting constructions, folded-Wronskian flags, and finite algebra descent is explicit below. T103 needs only a harmless change of Fourier length and fixed-extension simulation. Neither is independently audited in this iteration. No ninth finding, worldwide-priority claim, human-review claim, or formal certification is made.

The most useful retained bridge is the arbitrary-characteristic **Newton-flag reversal estimate** in §4, together with the **all-conjugates descent budget** in §6. The independent local-series route in §3 pays an exact coefficient cutoff but cannot choose the required noncommuting domain point. The balanced positive-characteristic depth-five lower-bound target remains unproved and unrefuted here; it needs a new rank argument, not just reduction of an unspecified nonzero integer minor.

## 1. Scope, source contract, and evidence boundary

Work accepts every theorem and lower construction in `openai/math` at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. It does not test their truth or manufacture contradictions between them. AGENTS.md and the four current status ledgers were consulted and frozen at the start. Their current-status and relevant historical entries identify eight accepted findings (R006, R008–R014), no accepted algebraic-complexity finding, and I28's different commutative-algebra/structure investigation. No accepted result is split here. The task's I100 disposition is retained; I101/I102 working artifacts are not dependencies. Later changes in the four permitted ledgers are reported as drift, not rebound into this argument.

The complete tree has 13,223 entries, 749 manuscript directories and 10,373 original blob positions. The search uses all 9,340 I14 originals and the I79/I88 augmented mapping for the other 1,033 positions, including 776 inherited PDF text extractions. All original SHA-256 and Git-blob hashes were replayed. No corpus directory was copied or downloaded again. `queries.json` records the exact five regular expressions; `lexical-hits.jsonl` retains **every match**, its source, full line and offsets (including repeated occurrences). This is a **full-domain lexical search, not full semantic reading**. Its respective match totals are rational 500, expansion 70, fields 25, tensor 765, models 41. The selected eleven source families have 181 original positions. Exact selected paths, hashes and originals are in `selected-inventory.json`; actual passage reads are separately recorded in `read-manifest.jsonl`.

Text passage numbers use UTF-8 decoding followed by Python `str.splitlines()`, one-based inclusive, unless explicitly labelled LF. In particular a PDF form feed is a splitlines boundary, so inherited PDF splitlines numbers must not be substituted for `sed`/LF numbers. New external PDF extracts use `pdftotext -layout` once each; no pinned PDF was re-extracted. Raw external response bytes and extraction hashes are preserved. Read ranges from these extracts are indexed separately by LF convention. Search-result snippets were only leads. The mathematical contracts below use actual TeX or full primary-paper passages through the relevant proof endings.

The relevant pinned contracts are:

* **Q**, *Polynomial Hitting Lists for Noncommutative Rational Formulas*, 24 September: `thm:main`, `prop:formula-certificates`, `lem:small-expansion`, `prop:rectangular`, `lem:division-lift`, `prop:pencil-deformation`, `prop:generator-hitting`, `cor:pencil-hitting`, `cor:rank-detecting-list`. Its theorem is over rational coefficients. Its proof already supplies simultaneous feasible-pencil hitting, tree-domain preservation, division-algebra deformation, all-root regular representation, and nonadaptive noncommutative rank. These are not new contributions of I103. The encoding, expansion, division, generator and rank sections were read completely.
* **P**, *Uniform Matrix Hitting Points in Every Positive Characteristic*, 4 October: `thm:main`, `thm:words`, `thm:order`, `lem:coefficient-descent`, `cor:path-programs`. One prime-field tuple has dimension O(n³s⁶), polynomial generation in n+s+log p, and works over every coefficient field of characteristic p. It is division-free, with acyclic path programs also covered. All five substantive sections were read completely. Its infinite-order shift, disjoint pole orbits and Casoratian Vandermonde are accepted lower operations.
* **Z**, *One Rational Matrix Hitting Point for Noncommutative Formulas*, 24 September: `thm:main` has dimension at most 2ns² over every characteristic-zero field, polynomial bit generation; `prop:path-programs` gives dimension (n−1) binom(m,2)+m for m-state acyclic representations. Shared paths are already covered; arbitrary shared arithmetic circuits are not. The actual coefficient and matrix constructions were inspected.
* **N**, *Matrix Multiplication Nine Fourths*, 2 October: `thm:main` is ω_C≤9/4. The complete proof, including the detecting-character appendix through its ending, is used in T103. It selects a finite exact rank scheme for each accuracy; it does not specify a useful finite crossover.
* **M**, *Complex Matrix Multiplication Below 2.258 and Rectangular Bounds*, 24 September: the strongest field-transfer section supplies ω_F<2.258 and w_F(.709)<2.092 outside one finite set of characteristics, plus α_F>.465 in characteristic zero. The complete finite-exception and accuracy-dependent transfer proofs were inspected. A varying exceptional set cannot be silently replaced by one common set when taking an exponent infimum.
* **S**, *Staggered extraction for exact matrix multiplication over every field*, 24 September: `thm:main` is ω_F<2.371054886006746 for every fixed field. Its foundations use exact coefficient extraction and a fixed-scheme arithmetic recursion. Its sharper field coverage does not make its numerical exponent stronger than N.
* **H**, *Homogeneous depth-five lower bounds for iterated matrix multiplication*, 25 September: the main lower bound is n^(sqrt(n)/400) for syntactically homogeneous five-layer circuits over every characteristic-zero field. Gates may be shared and bottom linear forms unrestricted. Its complex trace-moment proof and path-sum ending, and the complete field-transfer/completion proof, were inspected. The corresponding upper construction is n^(sqrt(n)+4) over every field.
* **F**, *Finite tensor savings and exact Fourier circuits*, 25 September: only a nonuniform subsequence conclusion in its stated theorem. Its explicitly referenced stronger companion **E**, *An explicit power saving for the exact discrete Fourier transform*, already supplies an all-length deterministic exact algorithm in its specified-root/arithmetic/address model. E's `thm:main` gives O(n(log n)^θ(log log n)^(4−θ)), θ<1, with preparation and indexing charged, and a supplied root of order <1024n³. Its full all-length/chirp/convolution ending was read. The integer-multiplication companion is present in the version screen; its bit model is not conflated with E's field model.

The permanent source was also checked at its actual statement: its Ω(m³) bound already concerns **border** determinantal complexity and fixed-budget border branching programs. An exact/ABP restatement is therefore not a target. Its smooth-form product bound and coefficient-selector construction are lower source operations, not a license for a general-circuit lower bound.

Current primary comparison: Arvind–Chatterjee–Mukhopadhyay, arXiv:2309.15647v4 (11 July 2025), remains the latest arXiv version in the observed submission history; the SIAM article was published online 1 June 2026. Its actual Theorem 2 and Corollary 3 are quasipolynomial rational-matrix constructions over Q. Its conclusion names polynomial matrix dimension and black-box NSingular as questions. This gives genuine named-problem relevance for G103, but the accepted Q manuscript already answers its rational-coefficient polynomial question. Guruswami–Kopparty's *Explicit Subspace Designs*, actual Lemma 12, §4.2 and Appendix A, already provide folded-Wronskian independence and multiplicity counting. Hrubeš–Wigderson (2015), Theorem 2.1 and its preceding model definitions, supplies the operational/free-skew-field equivalence used below. These are classical dependencies, not discoveries here.

The bounded MathDB search did not locate a directly matching rational-hitting/NSingular page. It did return the matrix-multiplication tag and [Valiant's IMM page](https://mathdb.com/p/375152/valiant-s-conjecture-for-iterated-matrix-multiplication), plus [strong USP capacity](https://mathdb.com/p/379385/strong-usp-capacity-conjecture). Those broader problems are **not solved here**. The observed strong-USP page labels importance “Research corpus”; no numerical ranking or featured status is inferred. Primary authors' explicit open-problem discussion supplies the relevant significance evidence for the selected rational target.

## 2. Four exact screens and selection

**A — universal rational lists in every positive characteristic (selected).** Given a prime p in binary and n,s in unary, construct in deterministic polynomial bit time a polynomial-output list of prime-field matrix tuples. For every extension coefficient field F of characteristic p and every size≤s rational **formula tree** over F with a defined nonzero matrix evaluation over an extension, some listed tuple must define the original tree and give invertible output. Size includes all leaves and inverse gates; there is no inverse-depth, constant-height or coefficient-encoding bound. Q supplies the characteristic-zero architecture; P supplies only division-free positive-characteristic hits. The remaining apparent obstacle is a uniform, full-rank domain construction in small characteristic. Sections 3–7 develop two routes and completely pay that construction. Its eventual contribution classification is technical, for the explicit reasons in §9.

**B — ω_F≤9/4 for every fixed field F.** Quantifiers: for every F and every ε>0, there exists an exact arithmetic algorithm and constant C_(F,ε) such that all n×n products cost at most C_(F,ε)n^(9/4+ε). No uniform bit algorithm for presenting arbitrary F or generating finite schemes is requested. N is later and numerically stronger than M/S; M's finite-extension simulation is already a lower operation. The only characteristic-sensitive step of N is a Fourier order and interpolation. Section 8 pays the whole transfer. This is technical, despite improving the numerical bound in the all-field statement relative to S's headline.

**C — balanced IMM depth-five lower bounds over all positive-characteristic fields.** Ask for absolute c>0,n0 such that every field F, every n≥n0 and every syntactically homogeneous ΣΠΣΠΣ circuit over F computing IMM_(n,n) has at least n^(c sqrt n) gates, unrestricted bottom support and sharing. H covers characteristic zero; its cited all-field low-degree results do not cover balanced width=degree=n with this rate. H's integral rank matrix does not supply one large minor remaining nonzero modulo each p. In particular its positivity/trace-rank step is over C, not a finite-field rank inequality. Taking p larger than polynomial degree alone does not prevent a nonzero integer minor from becoming zero. This target survives the screen but was not selected: it needs a characteristic-independent large minor or an alternative rank measure; no such estimate is proved here. No counterexample to the target is claimed.

**D — all-length exact Fourier power saving with preparation charged.** Ask for a single algorithm at every n with o(n log n) cost in E's root-supplied complex field/address model. E already states the stronger quantified bound above; its working length 2n≤L<4n, prime axes, CRT indexing, scalar preparation and chirp convolution pay the conversion. Rejected as an exact stronger-companion duplication. Removing supplied roots, proving stable floating-point bounds, or changing to arbitrary finite fields would be different contracts; none follows automatically.

A had the clearest plausible construction gap after the initial statement screen. Its completed proof and the full-operation comparison, rather than the absence of a matching title, determine the final technical disposition.

## 3. Route I: linear realization and local series — paid cutoff, circular domain choice

Here is the exact finite-dimensional lemma behind the first route.

**L103 (author proof; technical).** Let K be any field, m≥1, A_1,…,A_r∈Mat_m(K), u a constant row and v a constant column. The noncommutative formal series

    R(y) = u(I − Σ A_i y_i)^−1 v = Σ_w (u A_w v)y_w

is zero if and only if every coefficient with |w|≤m−1 is zero.

**Proof.** If u=0 there is nothing to prove. Otherwise let V_j be the span of uA_w for |w|≤j. V_0 has dimension one, V_j⊆V_(j+1), and V_(j+1)=V_j+Σ_i V_j A_i. If equality occurs, V_j is invariant under all A_i and the chain remains constant. If it never occurs through j=m−2, V_(m−1) has dimension m and is again invariant. Thus every row uA_w belongs to V_(m−1). If all its spanning rows annihilate v, every coefficient is zero. The converse is immediate. This argument is valid in every characteristic and uses no numerical rank surrogate. ∎

The source's formula realization has order |Φ|+1≤s+1. At a **supplied** defined d×d matrix point A, L_Φ(A) is invertible. Write a general amplified substitution as

    X_i = A_i⊗I + Σ_(a,b=1)^d E_ab⊗y_(i,a,b).

Factoring L_Φ(A) on the left makes every scalar entry of the represented value a series of the form in L103, with state dimension m≤(s+1)d and r=nd² letters. Thus a nonzero such series has a word witness of length at most (s+1)d−1. Its homogeneous component can be computed by a layered path program with at most (m+1)² vertices: copy the m states at every length from 0 to m−1, and add source/sink scalar edges. P therefore supplies a prime-field matrix hit for this nonzero component with dimension polynomial in n,s,d. This assertion is about the component and a supplied A, not a universal rational hit.

For completeness, the needed nonzero local series exists when Φ is operationally nonzero and A defines it. If every scalar-entry series vanished, then at every amplification dimension e the ordinary commutative rational matrix entries in the e×e entries of the y's would have zero formal expansions. Their denominators are nonzero at y=0, so their numerator polynomials would be zero. Every de×de tuple is of the displayed block form; therefore Φ would vanish at every defined tuple of those dimensions. Repeating any original nonzero witness d times by direct sum gives a defined nonzero tuple of dimension a multiple of d, a contradiction. A field extension with indeterminates can be used throughout, so this argument does not confuse polynomial identities with scalar functions on a finite field.

One can also pay a finite radial specialization once A and a hit Y are supplied. Suppose the hit dimension is e and k is a degree detected above. Set X_i(t)=A_i⊗I_e+tΣE_ab⊗Y_(i,a,b). Every domain-certificate determinant is a polynomial in t of degree at most (s+2)de, nonzero at t=0. One nonzero output-entry numerator, obtained from the root realization adjugate, has degree at most (s+1)de−1; it is nonzero because its Taylor coefficient of degree k is nonzero. The product of at most s inverse-node determinants, the root-realization determinant, and this numerator has degree at most

    ((s+1)(s+2)+(s+1))de = (s+1)(s+3)de.

(The bound deliberately overcounts.) In any extension with more than this many scalar choices, one choice keeps every original inverse defined and the output nonzero. This is a paid polynomial budget after a domain point has been supplied; it is not a way to find that point.

**Actual obstruction.** P's and Z's nonconstant hitting matrices are simultaneously strictly triangular. Any common scalar shifts a_i I+T_i remain simultaneously triangular. The commutator [a_1 I+T_1,a_2 I+T_2]=[T_1,T_2] is strictly triangular and singular. Thus the fixed-size rational expression

    (x_1 x_2 − x_2 x_1)^−1

is undefined at every such shifted tuple, while E_12,E_21 give commutator diag(1,−1), invertible even in characteristic two. This is a genuine failure of the proposed domain mechanism, not a counterexample to A. A block sum of tuples does not repair it: a rational expression is defined on that block sum exactly when it is defined on **every** block, whereas a division-free hitting-set promise only guarantees one successful block. The local route is therefore circular at the universal-domain step. It is not a general rational or shared-circuit PIT algorithm.

## 4. Route II: Newton flags and a new explicit estimate

All fields in this section are arbitrary. Let F be a field and let q,t be independent indeterminates over F. Put K=F(q), J=K((t)), and O=K[[t]]. For i=0,…,w−1 define

    α_i=(1+q)^i,       ξ_(i,r)=α_i q^r  (r≥0),
    b_(i,a)(z)=∏_(r=0)^(a−1)(z−ξ_(i,r)),       b_(i,0)=1.

All nodes ξ_(i,r) are distinct: equality first forces equality of r by order at q=0, and then equality of i by order at q=−1. These are integer valuations, unaffected by the characteristic. For a nonzero polynomial f∈K[z], its i-flag order is the largest a for which b_(i,a) divides f. Since the b_(i,a) form a monic triangular basis, this is the index of its first nonzero Newton coefficient. A dimension-h subspace V⊂K[z]_(<d) has an echelon basis with distinct orders

    0≤a_(i,1)<…<a_(i,h)<d.

**N103 (author proof; technical folded-flag estimate).** For every such V,

    Σ_(i=0)^(w−1) Σ_(j=1)^h a_(i,j) ≤ h(d−1)+w h(h−1).                 (4.1)

**Proof.** For a basis f_1,…,f_h define C(z)=det(f_j(q^r z))_(0≤r<h,1≤j≤h). Echelonize the basis by ordinary polynomial degree, obtaining distinct degrees e_j and nonzero leading coefficients c_j. The highest-degree coefficient of C is

    (∏c_j) det((q^e_j)^r) = (∏c_j) ∏_(j<k)(q^e_k−q^e_j),

which is nonzero. Thus C≠0 and deg C≤h(d−1). Changing to any other K-basis scales C by a nonzero constant in K. Fix i and use its flag-echelon basis. At z=ξ_(i,r), the entire column belonging to order a_(i,j) vanishes if r+h−1<a_(i,j), since its h arguments are h consecutive roots of that polynomial. Each such column is divisible by z−ξ_(i,r), so

    mult_(ξ_(i,r)) C ≥ #{j:a_(i,j)≥r+h}.

All nodes in all the orbits are distinct. Summing multiplicities gives

    h(d−1) ≥ Σ_(i,j) max(0,a_(i,j)−h+1)
             ≥ Σ_(i,j) a_(i,j)−w h(h−1).

This is (4.1). It holds for arbitrary K-coefficients, including coefficients depending on q; the shift fixes K. ∎

The ordinary Taylor substitute genuinely fails. In F_5[z], V=span(1,z^5), d=6, has vanishing sequence (0,5) at each of 0,1,2,3,4. The source's ordinary-Wronskian right side is h(d−1)+w binom(h,2)=15, whereas the sum is 25. Ordinary differentiation and the first two Hasse rows both annihilate z^5's first derivative. Merely renaming those derivatives does not repair the proof.

The folded determinant itself is classical (Guruswami–Kopparty, Lemma 12 and §4.2) and P already uses its infinite-order Vandermonde form. The prefix-flag multiplicity sum in (4.1) is the explicit interface required to reuse Q's reversal; it is not claimed to be a new worldwide determinant principle.

Now fix n,B≥1, put w=n+1, Δ=4w³B, and choose an integer M>BΔ, with N=M−Δ. For f=Σ_(a=0)^(N−1)c_(i,a)(f)b_(i,a), define

    T_i f = Σ_(a=0)^(N−1) c_(i,a)(f)t^a b_(i,M−1−a),      i=0,…,n.   (4.2)

These are injective maps J[z]_(<N)→J[z]_(<M), computed without scalar specialization.

**R103 (author proof; technical reversal construction).** For every subspace U⊂J[z]_(<N) with 1≤k=dim U≤B,

    dim_J Σ_i T_i U > (w−1)k.                                      (4.3)

**Proof.** Reduction of U∩O^N has dimension k. Here one takes the entire integral lattice, not reductions of an arbitrary basis. To verify this, choose an integral vector with a unit coordinate, eliminate that coordinate from the rest of U, and induct; the resulting k vectors have independent reductions and a unit k×k minor. That minor also shows every integral vector is an O-linear combination of them. The same applies to W=Σ_i T_iU, of dimension ℓ, whose reduction has dimension ℓ.

Let a_(i,j) and b_(i,j) be the flag orders of these reduced spaces. We claim

    b_(i,ℓ−j+1) ≥ M−1−a_(i,j),       1≤j≤k.                       (4.4)

Set A=a_(i,j). Lift j independent reduced vectors whose first A+1 Newton coordinates are independent and let U' be their span. Every integral vector in U' with nonzero reduction has a unit coefficient at some index a≤A. Normalize any nonzero f∈U' to have minimum t-valuation zero. In (4.2) its smallest coefficient valuation is min_a(ν_t(c_(i,a))+a)≤A. No a>A attains this minimum. The leading reduction of T_i f is therefore a combination of b_(i,M−1−a) with a≤A, and is divisible by b_(i,M−1−A). The surviving coefficients cannot all cancel because the Newton basis is linearly independent. Newton/monomial basis changes and their inverses lie in GL(K), so preserve minimum t-valuation.

The entire reduction of T_iU' consequently lies in that high-order flag. It has dimension j by injectivity and the integral-lattice argument. This proves (4.4), including for subspaces with arbitrary Laurent-series coefficients. No specialization of such coefficients is used.

Summing the largest k output orders, and applying (4.1) to both reductions, yields

    ℓ(M−1)+wℓ(ℓ−1)
       ≥ wk(M−1)−Σ_(i,j)a_(i,j)
       ≥ (w−1)k(M−1)+kΔ−wk(k−1).

If ℓ≤(w−1)k, this implies

    kΔ ≤ w[k(k−1)+ℓ(ℓ−1)]
        ≤ w[1+(w−1)²]k² ≤ w³Bk < 4w³Bk = kΔ,

a contradiction. ∎

**Feasible-pencil consequence.** Let A_0,…,A_n∈Mat_a(F), 1≤a≤B, and suppose L=A_0+ΣA_ix_i has an invertible matrix evaluation over some extension of F. Then ΣA_i⊗T_i is injective. Indeed, a nonzero kernel vector with components f_1,…,f_a spans a k-dimensional U, k≤a. Write its components in a basis of U using an a×k full-column-rank matrix P. Each row of [A_0P … A_nP] is a relation among the wk vectors T_i u_j. By (4.3) that relation space has dimension <k. Thus the column space V of P is mapped by every A_i into one common space V_- of dimension <k. Extend scalars to a common field containing J and the witness field (use fresh q,t and Laurent series over that witness field). The witness evaluation would send V⊗E^e into V_-⊗E^e, contradicting invertibility. This is exactly Q's shrunk-space argument, with its rank and common-field budgets preserved.

Append Δ zero columns to T_i to get R_i∈Mat_M(F_p[q,t]) when char F=p. Then

    rank ΣA_i⊗R_i ≥ aN > (a−1)M,                                 (4.5)

because M−aΔ≥M−BΔ>0. Notice that ordinary nonzero polynomial evaluation would not suffice for (4.5); the full rectangular expansion was necessary.

## 5. Division lift, with characteristic and degree budgets

Take ℓ=2 if p≠2 and ℓ=3 if p=2. Let M be the least power of ℓ exceeding BΔ. Then M≤3BΔ and p∤M. Write m=φ(M)≤M and

    Ψ_M(Z)=Z^(M/2)+1                         if ℓ=2,
    Ψ_M(Z)=Z^(2M/3)+Z^(M/3)+1               if ℓ=3.

Over an algebraic closure these polynomials have exactly the primitive M-th roots, all distinct. This follows by factoring (Z^M−1)/(Z^(M/ℓ)−1) and using p∤M. We never request a finite-field primitive-root oracle or factor an arbitrary p−1.

For each primitive root ω, let D e_j=ω^j e_j, S e_j=e_(j+1), indices modulo M, and for fresh commuting parameters a,b set

    R_i^*(q,t,a,b;ω)=Σ_(u,v=0)^(M−1) c_(i,u,v)(q,t) a^u b^v D^u S^v,
    c_(i,u,v)=M^−1 Σ_(j=0)^(M−1) ω^(−uj)(R_i)_(j,j−v).           (5.1)

At a=b=1 this is R_i by finite Fourier inversion. Q's lift proof works verbatim when p∤M: the algebra generated by aD,bS has ordered-monomial basis, multiplication with a nonzero root-of-unity scalar, and no zero divisors by its leading lexicographic term. Localize by the central polynomial ring in a^M,b^M. The resulting algebra has dimension M² over F(q,t,ω)(a^M,b^M), with basis (aD)^u(bS)^v for 0≤u,v<M; independence follows by clearing central denominators and comparing exponent residues. A finite-dimensional domain over a central field is a division algebra, since left and right multiplication by a nonzero element are injective and hence surjective. Block Gaussian elimination inside this algebra makes every ordinary block-matrix rank a multiple of M.

For each feasible L, a nonzero minor witnessing (4.5) remains nonzero after lifting, because it specializes to the original minor at a=b=1. Its rank is >(a_L−1)M and is divisible by M, so Σ A_i⊗R_i^* is invertible. In particular R_0^* is invertible generically, by the constant pencil 1. Normalization is on the **left**:

    (I⊗(R_0^*)^−1)(Σ A_i⊗R_i^*)
        = A_0⊗I + Σ_(i≥1) A_i⊗((R_0^*)^−1R_i^*).               (5.2)

All degrees can be bounded uniformly before seeing any coefficients. Put C=M(n+M). The coefficient matrices of the Newton bases have q-degree≤C and are unit triangular. Their inverses, by the finite geometric series for a strictly triangular matrix, have degree≤(M−1)C. Therefore R_i has q-degree≤MC and t-degree≤M−1. Equation (5.1) adds a,b degrees at most M−1 each. The total degree of a lifted entry is at most

    MC+3M ≤ E := 4M²(n+M).

There are no parameter denominators; 1/M is a nonzero prime-field constant. An order≤B pencil determinant has degree≤BME. This deliberately loose bound is adequate for dense polynomial-time generation.

## 6. A full prime-field list, preserving all conjugates

**G103 (author proof; classified technical here).** Given prime p in binary and positive n,B,h in unary, there is one deterministic Turing machine producing a list H_(p,n,B,h) of n-tuples of matrices over F_p, independent of all coefficient values. Its bit generation time and complete dense binary output length are bounded by a fixed polynomial in n+B+h+log p. For every field F of characteristic p and every family of at most h affine pencils over F, each of order≤B and each admitting an invertible evaluation over an extension of F, one tuple in the list makes **all** pencils invertible over F. The witnesses may initially have different dimensions and live over different extensions. All output tuples have common dimension d=eMφ(M), with the parameters below; in particular d=O((n+1)^6 B^4 log(n+B+h+2)).

Set

    D0=(h+1)BM²E,        H=(D0+2)².

If p>H, set e=1, K=F_p, and use the grid {0,…,D0}^4. If p≤H, choose the least e≥1 with Q=p^e>H, construct K=F_(p^e), and use K^4. We have Q≤pH≤H² and e≤1+log_2 H≤D0+3. Thus Q>H>eD0. These bounds do not include the unknown coefficients.

Compute the symbolic R_i and their lifts with ω replaced by ξ in the finite algebra

    A=K[ξ]/(Ψ_M(ξ)).

At each grid tuple (q0,t0,a0,b0), specialize and replace each A-entry by its multiplication matrix in the explicit F_p-basis (a power basis of K, followed by 1,ξ,…,ξ^(m−1)). This gives Z_0,…,Z_n of dimension d=eMm over F_p. If Z_0 is singular, discard that tuple. Otherwise emit (Z_0^−1Z_1,…,Z_0^−1Z_n).

**Hitting proof.** Fix F and the family, and add the constant pencil 1. Work in an algebraic closure Fbar. For each pencil and each primitive root ω, §5 supplies a nonzero determinant polynomial in q,t,a,b. Their product P is nonzero of total degree≤D0. This is only a proof object; the machine does not compute it.

When p>H, the ordinary grid lemma on D0+1 distinct scalar values gives a point with P≠0. When p≤H, identify K with its unique finite subfield in Fbar. For every j=0,…,e−1, the bad set

    {x∈K^4 : P(x_1^(p^j),…,x_4^(p^j))=0}

has size at most D0 Q³. Indeed the coordinate Frobenius map permutes K^4, and a nonzero polynomial of total degree≤D0 has at most D0 Q³ zeros on this grid, even with coefficients in Fbar. The latter follows by induction in the number of variables, using the usual root bound on each nonzero univariate fiber. A union bound gives at most eD0 Q³<Q⁴ bad tuples. Hence one tuple is good for every j.

After scalar extension to Fbar, the regular representation of A is the direct sum of its e·m embeddings, obtained from the e Frobenius embeddings of K and the m primitive roots. On each summand, every raw pencil matrix is precisely its lifted evaluation at the corresponding conjugate tuple and root. The chosen tuple makes all summands invertible. Thus every ΣA_i⊗Z_i is invertible after extension and hence already over F. The constant-pencil factor ensures Z_0 is invertible, so that tuple is emitted. Equation (5.2) makes every original pencil invertible. This proves the simultaneous guarantee without identifying F with K or requiring F to contain K. ∎

The conjugate budget is essential. In F=F_4 with α²+α+1=0, P(x)=x−α is nonzero at x=α² but zero at its Frobenius conjugate α. Consequently the F_2 multiplication matrix of α², minus αI after scalar extension to F_4, is singular. One good extension-field point does **not** suffice for descent when coefficients are allowed in arbitrary extension fields. Our list pays all e conditions; a product with Frobenius-substituted polynomials needlessly inflates degrees, so the proof counts their bad sets instead.

**Bit construction proof.** All integer parameters and polynomial degrees above are polynomial in n+B+h. For p≤H, brute-force construction of K is still polynomial: enumerate monic degree-e polynomials, at most p^e=Q≤H²; reject reducible ones by testing divisibility by all monic polynomials of degree≤e/2, at most e p^(e/2), also polynomial in H. A degree-e irreducible exists: the roots of X^(p^e)−X in a splitting field form a field of size p^e; the union of its proper subfields has size at most Σ_(r=1)^floor(e/2) p^r<p^e for e≥2 (e=1 is immediate). An element outside that union has minimal degree e. Thus enumeration terminates. No randomized factorization assumption is hidden here. For p>H, no extension is constructed or enumerated.

Newton-basis formation, unit-triangular inversion, the M² Fourier sums in the quotient algebra, and specialization all use polynomial-size dense arrays. The small-p grid has Q⁴≤H⁸ tuples, while the large-p grid has (D0+1)^4 tuples. The finite algebra has dimension em≤eM over F_p. Ordinary residue arithmetic, polynomial long division, and Gaussian elimination cost polynomially many bit operations in array sizes and log p; modular inverses use the Euclidean algorithm. Every entry is emitted as a residue in {0,…,p−1}; d²n entries per tuple and all dimensions/delimiters are charged. A Turing implementation may scan its polynomial storage per access without changing polynomiality. Thus the entire output and generation time have the asserted uniform bound. The exponent of that polynomial is large; no practical-size assertion is intended.

## 7. Rational expression domains and the shared-circuit boundary

For a formula Φ of tree size≤s, use G103 with B=2s+1,h=s+1. Q's affine recursions are valid over every field: a leaf has pencil [[1,−x],[0,1]] with selectors e_1^T,e_2; addition uses block direct sum; multiplication uses the upper-right constant block −v_f u_g; inversion appends [[L_g,v_g],[u_g,0]] with negative last-row selector. Induction gives order |subtree|+1 and value uL^−1v wherever the subtree is defined. Schur factorization at an inverse node is

    [[L,v],[u,0]]
       = [[I,0],[uL^−1,I]] diag(L,−uL^−1v) [[I,L^−1v],[0,I]].

The signs remain valid in characteristic two. Retain the pencil for **every inverse occurrence** and the root augmentation. There are at most s+1 pencils, order≤2s+1. From leaves upward, their simultaneous invertibility implies definedness at every inverse gate; after that induction the root Schur complement implies invertible final value. Conversely, definedness and invertible final value imply every certificate is invertible. This is Q's full domain operation, not a new linearization.

It remains to justify feasibility when the operational nonzero witness is only nonzero, not invertible. Over its witness field E, Hrubeš–Wigderson Theorem 2.1 identifies admissibility with a correct free-skew-field expression and identifies equality with equality on all defined matrix domains. Thus Φ is a nonzero element there; the expression Φ^−1 is correct. Applying part (i) again supplies a defined matrix evaluation of Φ^−1, hence a defined **invertible** evaluation of the original Φ. Therefore every certificate is feasible over an extension of F and G103 applies. This invocation is field-general, and avoids trying to apply Q's characteristic-zero symbol lift to an initial witness size divisible by p. The construction's own block size M is prime to p by design.

We obtain exactly the operational formula conclusion of screen A: the prime-field list works uniformly over all F of characteristic p and all constants and inverse depths. Equivalence in a skew field does not erase the original gate certificates. For instance (x^−1)^−1+1 remains undefined at x=0 even though its simplified rational function is x+1.

This result does **not** give a polynomial list in arbitrary shared-circuit size. The block recursion duplicates child realizations at every use; on a DAG its bound is the unfolded formula size. A concrete obstruction to that recursion is repeated squaring: a chain of O(k) shared multiplications computes x^(2^k), whereas a division-free binary formula for that monomial needs at least 2^k variable leaves by degree. This does not prove a lower bound for every rational realization or refute general circuit PIT; it proves that the offered recursion does not pay the shared-subcomputation step. A general-circuit or polynomial-degree circuit extension remains outside G103.

Nor is noncommutative rank identified with ordinary identity testing: G103 tests invertibility of blow-ups of feasible affine pencils; it does not test the commutative determinant polynomial alone. Q already contains a complete rectangular-rank completion construction over Q. A field-general rank corollary would additionally invoke the exact free-field/blow-up characterization over that field; it is not counted as another construction or asserted here without that extra contract.

## 8. T103: the full every-field 9/4 reduction

**T103 (author proof; technical).** For every fixed field F and every ε>0 there is a constant C_(F,ε) and an exact algorithm using at most C_(F,ε)n^(9/4+ε) scalar additions and multiplications over F for every n×n matrix product.

**Proof under the accepted lower operations.** First work over the algebraic closure K of F, which is infinite in every characteristic. Rebuild N's tensor semiring and detecting-character argument there. Its appendix uses only finite ranks, flattenings, restriction, direct sums/products, real finite-dimensional cone separation, compactness, and the Schauder–Tychonoff argument. No characteristic-zero scalar operation occurs in it. Thus its `lem:existence` applies to the K-rank exponent ν_K with the same proof, including the catalyst reused only once and the order of limits j→∞, δ↓0, n→∞.

For its finite separation operation with M blocks, choose L=5M when char K does not divide 5M, and L=5M+1 otherwise. In all cases 5M≤L≤6M, char K∤L and K has a primitive L-th root ζ. Use exactly N's three Fourier substitutions with 1/L. Their phase sum is the indicator of u−v+2(g−h)=0 mod L. Since its absolute integer size is at most 3(M−1)<L, this is the integer equality, irrespective of the field characteristic. Give variables the same **integer parameter exponents** g²,hu−h²,−hv. The exponent of a surviving term is (g−h)²; this is a nonnegative integer exponent, not a field element that could vanish modulo p. The weight-zero part is exactly the desired full direct sum with B_X(M). Its source cost is at most 6M instead of 5M.

Every fixed degeneration can be interpolated at arbitrarily many distinct nonzero points in K. Its j-th power costs jL_deg+1 exact evaluations, so character monotonicity follows upon taking j-th roots. In the fixed-type-word entropy argument the extra constant 6 disappears after N-th roots just as the source's 5 does. Hence N's shared-leg entropy inequality holds unchanged.

The determinant filtration for polynomial multiplication uses D=uw−vs, diagonal substitution, explicit monomial quotient lifts and the kernel basis D·monomials. Surjectivity and the equality of kernel dimensions prove the exact sequence over **every** field; no division by 2 or Clebsch–Gordan semisimplicity is used. All multiplication slices preserve that filtration. Thus the two diagonal tensor blocks and the entropy-maximized discrete concavity inequality are unchanged. The three-sector degeneration uses interval indexing, weights −1,0,1, translations and a leg permutation, also over any field. It gives the same shifted-tripling inequality. Polynomial multiplication of input lengths a,b has exact rank a+b−1 over K by ordinary interpolation and its flattening. No fixed small field is used for interpolation.

Consequently for every detecting character the same symmetrized positive real profile P obeys P(1,b)=b, symmetry, discrete concavity, shifted tripling, and P(a,b)≤(a+b−1)^(1/t). N's complete real growth lemma gives P(a,a)≥a^(4/3), so t≤3/4. The detecting-character conclusion then yields ν_K≤9/4 exactly as in N, with the character permitted to depend on the testing dimension. These are the source's lower operations, with every changed field input now specified.

Fix ε>0 and δ∈(0,ε). Select one exact finite K-rank scheme for T_u of rank r<u^(9/4+δ). Its finitely many coefficients lie in a finite algebraic extension E/F because K is an algebraic closure; let e=[E:F]. The standard block recursion over E has cost O_(u,r)(n^(log_u r)log(n+1)), allowing the boundary r=u², and padding by the next power of u costs a fixed factor. Choose a fixed F-basis of E containing 1 and simulate **the entire recursive computation** in coordinates. Each E-addition or multiplication takes a constant number (at most O(e³)) of F-operations using its fixed multiplication table. Input coordinates are F-valued, so the final coordinate of 1 is exactly the required F-product and other coordinates are zero. This constant factor is applied to the whole operation count, not multiplied into r at each tensor level. Absorbing the logarithm by the remaining exponent margin proves the claim for all n. ∎

All scheme dimensions, field-extension degrees, structure constants and crossover constants may depend on F and ε. This is an exponent-infimum statement and an existence of exact finite schemes, not an efficiently generated universal finite-size algorithm or a bit bound. It is not obtained by interchanging accuracy with M's finite exceptional set. Instead the full source proof was transferred over K; M's already available finite-extension simulation then finishes. This is why the every-field headline improvement is technical under the task's rule.

## 9. Contribution test and remaining gaps

There is no exact all-characteristic rational-list statement in the selected pinned titles. That absence is not the contribution argument. G103's full scope is paid by a concrete chain:

1. Q's rectangular Taylor reversal and integral-lattice/shrunk-space mechanism;
2. P's independent-orbit choice and infinite-order folded determinant, equivalently the classical Guruswami–Kopparty folded-Wronskian multiplicity method;
3. monic Newton coordinates, whose prefix roots replace Taylor multiplicities, with the explicit loss w h(h−1) and Δ=4w³B;
4. Q's symbol deformation, taking powers of 3 instead of 2 in characteristic two;
5. Q's all-root regular representation, plus enumeration of a polynomial-size finite extension and an elementary union bound over its conjugates;
6. Q's original-tree certificates and classical Amitsur operational equivalence.

Every operation is displayed with its budget and all-field applicability, so there is no unpaid conditional lemma hidden by this classification. The combined construction is useful and was worked out here, but this author does **not** recommend treating this Wronskian-to-folded-flag model transfer as one of the user's two remaining substantial findings. Classical tools alone would not automatically defeat substantiality; it is the complete matching lower-operation reduction, including the only apparent new domain/field obstacles, that does so in this case. Independent proof or contribution reviewers could examine this disposition; none was started because this assignment forbids children.

T103 is an even more direct standard transfer, fully accounted for in §8. The field parameter change is not a new tensor extraction. D is already in E. C survives, but this iteration has no new characteristic-independent large-rank estimate for it. The scalar-shift domain proposal, ordinary/Hasse-first-row flag proposal, and one-embedding descent proposal are explicitly falsified, not merely unproved. G103 and T103 are author proofs, not independent-audit passes. No numerical experiment is used as a proof.

A useful next algebraic-complexity direction would require a genuinely different parameter or model bridge: for C, an explicit large minor surviving each characteristic or a replacement measure with a proved all-field rank lower bound; for circuit PIT, an actual polynomial-budget shared-subcomputation representation. This report proves neither and does not nominate them conditionally. It does not claim that all possible algebraic-complexity targets reduce to the sources.

## 10. Reproduction, failures, and ownership

Only the assigned report, `frontier/sources/i103_algebraic_complexity_discovery/`, and `frontier/experiments/i103_algebraic_complexity_discovery/` were written. No child agent, staging, commit or publication was performed.

`check_math.py` runs pure exact finite diagnostics: 216 folded-flag cases, 240 parameter/conjugate-budget cases, the F_5 ordinary-flag counterexample, the F_4 descent counterexample, and triangular-domain checks, totalling 4,757 counted assertions. These support implementation and obstruction checks only. They do not certify universal algebraic proofs, the applicability of accepted premises, or contribution status.

The final `verify.py` is offline and read-only. Invoke from the repository root with `python -B frontier/experiments/i103_algebraic_complexity_discovery/verify.py`. It verifies the exact owned inventory and hashes, immutable original references and frozen snapshots, every original blob against the complete tree, the exact search-expression/match multiset, read-passage hashes, and the exact diagnostics. The four live ledgers alone may drift; their frozen snapshots remain sealed. It neither downloads nor writes, repairs, re-extracts PDFs, produces bytecode, or reseals. Hash replay is evidence integrity, not universal proof or contribution certification.

Retained preparation failures: the first attempt to read E's introduction used the nonexistent suffix `01-introduction.tex` and failed before any read record was added; the correct `introduction.tex` was then read. A later short family selector matched five introductions and a guessed complex-multiplication filename matched none; both assertions failed before logging a passage, and exact selectors resolved them. An initial post-compaction command ran from the workspace parent and found no owned report; it performed no writes. Several initial combined console reads were truncated, so only later explicit complete ranges are treated as complete proof reads. The Derksen–Makam publisher-hosted PDF request returned HTTP 403; it is not a mathematical dependency and was not silently replaced by an assumed read. Its arXiv metadata was consulted only as metadata. Any preseal validation failure is recorded in `preseal-events.json` before the one final seal. The fresh construction was not edited after that seal.

### Primary references

* Arvind, Chatterjee, Mukhopadhyay: [arXiv:2309.15647v4](https://arxiv.org/abs/2309.15647v4), actual Theorem 2, Corollary 3 and §6; [2026 SIAM publication](https://epubs.siam.org/doi/10.1137/24M1689508). Version and publication-date observations are in the retained web responses. The journal full text was not assumed identical to the preprint; the quantified comparison here is explicitly to v4 and the journal abstract/metadata.
* Guruswami, Kopparty: [author full paper](https://www.math.utoronto.ca/swastik/subspace-designs.pdf), Lemma 12, §4.2 through Theorem 14's proof ending, Appendix A; [ECCC report/version page](https://eccc.weizmann.ac.il/report/2013/060/). Folded independence and multiplicity counting are credited to this work.
* Hrubeš, Wigderson: [published full paper](https://theoryofcomputing.org/articles/v011a014/v011a014.pdf), §2 definitions and Theorem 2.1; Q's complete source encoding was used for the concrete recursion and original-domain proof.
* Pinned source URLs, exact versions, original-byte hashes, labels and inspected line ranges are given in the adjacent `source-contracts.json` and `read-manifest.jsonl`, not inferred from the catalogue summaries.
