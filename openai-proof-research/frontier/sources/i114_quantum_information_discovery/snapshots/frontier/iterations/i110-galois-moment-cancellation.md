# I110 — Original-proof audit and actual Galois moment cancellation

**Disposition: all requested ORIGINAL I108 mathematical claims PASS at their stated scopes, without repairs. Arbitrary admissible moment cancellation, TD, and G104 remain unproved and unrefuted. Park this branch; no substantial finding is nominated. Eight accepted findings remain eight.**

Two mechanisms were pursued beyond the audit. The first constructs integral central residue projectors and recovers **integer fixed ordinary-label counts** from finite-field cocenter ranks. It gives exact moment certificates, rather than long positive-valuation sequences, for six inputs, including all mixed supports for S5 at p=2, a=1. It also yields a proved product transfer and the uniform estimate v₂(N)≥s+3 for A5×A with **every finite abelian odd-order A**, every admissible a, every multiset, and s≥1. The second retains coefficient Galois action in the complete BBY local-point involution, producing an actual equivariant pairing on every nontrivial local-point stratum. Its attempted extension through an auxiliary central p-group, and its attempted minimal-field averaging, leave the trivial-group component unpaid. Neither mechanism proves cancellation for arbitrary groups.

All theorems **and lower proof operations** in openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are accepted premises. There is no upstream truth audit, inconsistency argument, or ex-falso deduction. The original I108 audit of I104 is a frozen prerequisite. No children, shared-index edits, staging, commits, or publication were used. I109 and I107 artifacts are not dependencies. This is agent-level mathematical work and evidence replay, not human review, formal certification, contribution acceptance, or a worldwide-priority claim.

## 1. Frozen originals and reading boundary

The assigned full I110 brief, including the complete original I108 brief/report/finalized parent response, is frozen in `../sources/i110_galois_moment_cancellation/original-i110-brief.txt`. The independent copies of the I108 report and original I108 prompt are also frozen. The I108 report has SHA-256 `756db8cd8b2cf97037bc4e5adf343ac8baeb34a18b758a35f170aef286d7596e`; its original seal has SHA-256 `0081d4ceb8f4c724841036d2a16856d89317846a4761006800f5479e4dbbd625`. The finalized parent response and its underlying replay record are kept distinct. The latter verifies evidence; it did not previously pass I108's new proofs.

Write A for the pinned *The Blockwise Alperin Weight Conjecture*, and ID for *Integral Donovan Finiteness over Witt Vectors*. The source operations used here were read through their relevant proof endings: A's full valued lift/marked-cover/descent section and full specialization section; the full exact inseparable-genus proof and index-base-change proof; the cocenter/subsection operation and detector/final group reduction; the full functorial consequence; ID's full integral comparison and assembly. The frozen I108 audit supplies the already closed I104 results, including the integral permutation-summand lift and universal TD⇒G104. Those proofs are not reopened here.

The complete BBY arXiv v1 and the later **February 11, 2026 author manuscript** were compared through the end of the local-point involution and stable conclusion. The Huang–Yılmaz author manuscript was read through its chain, fixed-projective-functor, minimal-field, and Galois-conjugate-block proofs. FFZ v2's inductive hypotheses and final reduction/construction, and Huang v3's exact central-extension and final compatible-family assembly operations, were inspected through their endings. Imported theorems remain attributed to their authors. This is selective complete-operation reading, not semantic reading of the entire corpus.

`passages.json` records source bytes, one-based **str.splitlines()** ranges, separate LF-split counts, and hashes of the selected lines joined by LF with one final LF. PDF form feeds make the conventions different. `immutable-references.json` binds the inherited sealed evidence and new selected references. Only the four authorized live ledgers may drift; their frozen snapshots are checked instead.

## 2. ORIGINAL I108 verdicts — before the new mechanisms

The following are separate verdicts on the original text, not repaired substitutes.

* **Constrained puncture bijection (10): ORIGINAL PASS.** The generation and simultaneous-conjugation multiplicities are unchanged, and the constraint is part of the assertion.
* **Marking counterexample: ORIGINAL PASS at its stated scope.** It disproves invariance under the exhibited handle marking, not membership of that marking in the auxiliary arithmetic Galois image.
* **Full-residue/index obstruction: ORIGINAL PASS.** It includes inseparable residue degrees and applies to an additional divisor defined over the small extension. It does not forbid a geometric point after paying a large field extension.
* **Conditional Hurwitz loss (11): ORIGINAL PASS.** Its three comparison hypotheses must be retained, including the original-label selected-vanishing comparison and the inseparable-genus threshold. It gives bounded loss, not Euler-characteristic equality.
* **Mixed moment identity (12): ORIGINAL PASS.** The subgroup lattice consists of actual subgroups, the class assignment is ordered, and the orbit divisor is D_J=|J|/|Z(J)|.
* **T108 sufficiency, uniformity, and threshold: ORIGINAL PASS.** The multinomial valuation pays for sparse or p-indivisible supports; the estimate holds in every fixed finite ramification index, including p=2.
* **T108 necessity: ORIGINAL PASS.** Every accessible residue vector has a positive realization, including Q=2, and dilation preserves the multinomial valuation. This proves both directions, not just a sufficient criterion.
* **Cyclotomic norm cutoff: ORIGINAL PASS.** Precision is imposed on A=D_JΘ, not silently on Θ; the strict inequality p^R>B^φ(Q−1) is sufficient.
* **Fixed-label/integral-block-projector obstruction: ORIGINAL PASS at its stated scope.** It excludes an integral central selector of an arbitrary fixed-character subset and extraction from one detector's central powers. It does not exclude a characteristic-zero projector, or use of the separate power operator and its full integral permutation data.

No mathematical repair was required. The improvements below, including fixed-word integrality and use of projectors together with rank profiles, are new technical deductions; they are not retroactive changes to the original verdicts.

### 2.1 Puncture and marking

Use [x,y]=xyx⁻¹y⁻¹. From Uy^t=xyx⁻¹, right multiplication by y⁻¹ gives Uy^(t−1)=[x,y]. Hence with A=y, B=x, v=A^(t−1), one has [A,B]Uv=1, and the converse recovers the original relation. Forgetting v and swapping the handles is the inverse. The u_i, their order and class multiset are unchanged. Since v is a word in A, the generated group and the simultaneous centralizer are unchanged. Thus the orbit size of a generating tuple remains D_J. The Riemann-existence operation applies to this **marked subset** after adding a distinct puncture; it does not provide arithmetic stability of the constraint.

For admissible t, its congruence modulo the p-part of exp(J) kills A_p^(t−1), so v is p-regular. It may be 1. A trivial peripheral monodromy is permitted in the marked-cover classification but does not create a p-singular branch point.

In S3 with p=2,t=5, choose A=(123), B=(12), u₁=u₂=B. Then U=1, v=A⁴=A, [A,B]=A², so the punctured relation holds. The subgroup is S3. The Nielsen substitution A′=AB, B′=B preserves [A,B], but A′ has order two and (A′)⁴=1≠v. This proves exactly the marking dependence claimed in I108. Nothing in this computation identifies the Nielsen element with an arithmetic automorphism over A's field.

### 2.2 Full residue degrees and the conditional loss

Let L/K_s be a finite extension of A's spherical base and F its residue field. For a closed point z of X_L put M=κ(z). Properness extends Spec M→X_L over the valuation ring of M. Its reduction is a point of E_F valued in res(M). The full-residue-degree operation gives

    [res(M):F]=[M:L]=deg_L(z).

If the image closed point of E_F is x, its pushforward zero-cycle is [res(M):κ(x)]·x. Its degree is precisely the displayed number, not merely its separable part. With [F:F₀]_p≤p^h and s≥h, the source index operation makes p^(s−h) divide this number. Summing proves the assertion for every effective divisor. For a point defined after a further extension, the same calculation charges the p-part of that extension. Over K_s an individual point therefore costs p-part at least p^s.

In characteristic zero, an L-defined set of r distinct geometric points has a reduced divisor of degree r, since all finite residue extensions are separable. Thus 0<r<p^(s−h) is impossible. A geometrically specified exceptional point with no L-descent is outside this conclusion. Replacing it by its full orbit changes the number of punctures and the tuple constraint.

For (11), retain m=|J|, the source threshold p^(s−h)>m(h+log_p m), its residue-degree equality, and the selected-vanishing comparison for the original n labels. Let V=Σ_wν(C_w)/m and G=ν(Y)/m. With r extra geometric branch points the generic formula is

    G=Σ_i(1−b_i)+R,       R=Σ_j(1−1/e′_j),       0≤R≤r.

The two retained lower bounds are

    V≥Σ_i(1−q_i+δ_iq_i),
    G≥V+2Σ_i max(q_i−b_i,0).

Subtracting gives Σ_i(|q_i−b_i|+δ_iq_i)≤R. This is (11) with no dropped term or factor two. Generic e_i divides m. The complete reduced-special-fiber identity makes m/(r_i a_i) an integer, retaining full residue degrees, so r_i a_i also divides m. Consequently each nonzero summand is at least 1/m, and at most floor(mR)≤rm labels are bad. A positive right side does not force equality of Euler characteristics. The source construction of its model explicitly needs equality of every sufficiently high section-space dimension. Bounded loss does not supply it. If the exceptional divisor descends with bounded degree, the previous index obstruction already removes it for large s.

### 2.3 Mixed moments and all denominators

For a fixed word of J-class labels with multiplicities m_i, the puncture-product convolution in H is ∏_i W_{H,i}^{m_i}. The central factors commute; thus its count is independent of the order of this word. The frozen twisted trace identity gives |H| times the sum of its eigenvalue products over **γ_t-fixed ordinary χ**. Subgroup Möbius inversion extracts the tuples generating J. A generating tuple's simultaneous stabilizer is Z(J), and dividing by D_J gives the count of its orbits. Finally there are M(m)=n!/∏m_i! distinct label words. This proves original (12) exactly.

In fact F_t(m) itself is a nonnegative integer: it is the number of generating orbits for one fixed label word. I108 used only the weaker integral-numerator bound v_p(F_t(m))≥−v_p(D_J), which is valid and suffices. No division by M(m) in a residue field is justified or needed. Empty intersections give zero eigenvalues; m_i=0 omits a coordinate. If there are no p-singular classes, all positive-length tuple sets are empty.

### 2.4 T108: independent proof audit of both directions

Normalize v_π(π)=1, e=v_π(p), d=v_p(D_J). Every λ is an algebraic integer: multiplication by its integral class sum has a monic integral characteristic polynomial and λ is an eigenvalue. A common finite p-adic splitting extension contains the λ and their Teichmüller representatives. No group-uniform ramification assertion occurs.

For α a unit with Teichmüller representative ω, write α=ω(1+z), v_π(z)≥1. The internal binomial coefficients in the pth power have valuation at least e, so

    v_π((1+z)^p−1)≥min(e+v_π(z), p v_π(z))≥v_π(z)+1.

For p=2 there are no missing internal terms. Induction gives valuation at least k+1 for α^(p^k)−ω^(p^k). For a nonunit, ω=0 and v_π(α^(p^k))≥p^k≥k+1. Factoring A^u−B^u preserves the bound for every positive multiple p^k u. Telescoping products over the active support therefore proves

    v_p(F_t(m)−Θ_t(I,m mod(Q−1)))≥(k+1)/e−d,
    k=min_{i:m_i>0}v_p(m_i).

The coefficient μ(H,J)|H| is integral; summing cannot lower the minimum valuation. Dividing by D_J subtracts exactly d.

For total p^s, the residue vector is accessible. If all accessible moments vanish, put c=v_p(M(m)). The integer identity

    m_i M(m)=p^s (p^s−1)!/((m_i−1)!∏_{j≠i}m_j!)

gives c+v_p(m_i)≥s for **each active i**, so k≥s−c. If c≥h+d, numerator integrality already gives v_p(N)≥h. Otherwise

    v_p(N)≥c+(k+1)/e−d
           ≥(s+1)/e−d+c(1−1/e)≥(s+1)/e−d.

Thus s≥max(0,e(h+d)−1) suffices. The number of multisets, size of the support, and how many multiplicities are divisible by p do not enter the threshold. This proves the original sufficiency at full scope; no assumption k=s or c=0 has slipped in.

Conversely fix an accessible (I,ρ), choose positive representatives in {1,…,Q−1}, and choose b in the given class modulo f so large that p^b dominates their sum. The difference is a nonnegative multiple of Q−1; adding it to one coordinate gives positive m_i with total p^b and residues ρ. When Q=2 the modulus is one, the positive representative is 1, and the same construction works for every nonempty support.

Dilate m to p^k m for k tending to infinity through multiples of f. Base-p digits simply shift under this dilation. Legendre's formula therefore gives v_p(M(p^k m))=v_p(M(m)), with **no assertion that the multinomial numbers themselves are constant**. Teichmüller powers are unchanged along these k; the preceding power bound makes F_t(p^k m) tend to Θ_t(I,ρ). TD for every h makes v_p(N_t(p^k m)) tend to infinity. Subtract the constant multinomial valuation to conclude F_t(p^k m)→0, hence Θ=0. Uniform TD is more than needed on this one sequence, but it supplies the conclusion for every accessible vector. This proves necessity.

For the cutoff set A₀=D_JΘ, M=Q−1 and B=max(1,Σ_H|μ(H,J)||H|k(H)). A₀ is integral in Q(ζ_M); every complex conjugate has absolute value ≤B. Its degree is at most φ(M), with φ(1)=1. If nonzero, its rational norm is a nonzero integer of absolute value ≤B^φ(M). All p-adic conjugates are integral; one having v_p≥R forces the norm's valuation at least R. (Here p∤M, so the cyclotomic local extension is unramified; the weaker inequality also follows from the local norm formula.) If p^R>B^φ(M), this is impossible. To test Θ instead of A₀, one must add d to its measured valuation. Equality at the bound is not asserted to suffice.

### 2.5 Precise projector obstruction

On A4 at p=2, the involution-class eigenvalues 3,3,3,−1 all reduce to 1. For admissible t=5, the two nontrivial linear characters are exchanged; the trivial and degree-three characters are fixed. Thus this detector's central powers have identical Teichmüller coordinates but the fixed-label count is two, not four. A polynomial in these **residual scalar data alone** cannot choose just the two labels.

More concretely, in a characteristic-zero splitting field the central idempotent e₁+e₃ selecting these two labels has identity coefficient (1²+3²)/12=5/6. This is not 2-integral. Hence the unique central characteristic-zero selector does not belong to the integral group algebra. This proves the obstruction without assuming that every characteristic-zero projector must be integral. It does not forbid integral projectors selecting residue fibers (unions of whole blocks), followed by a separate computation of L_t on those fibers. That distinction is used next.

## 3. Mechanism I — residue projectors with the ordinary-label action retained

The attempted universal mechanism was to resolve central residue fibers, retain the full cyclic module on each, and seek subgroup-Möbius cancellation there. It succeeds in constructing the fibers and computing their integer traces. It does **not** prove the cross-subgroup identity. It supplies the following complete technical bridge and a product-family estimate.

### 3.1 Exact residue-fiber construction in characteristic two

**Proposition P110.** Let J be finite, p=2, and let t be admissible for a. Set E=exp(J), E′=E_{2′}, and f=ord_{E′}(2), with f=1 if E′=1. Assume gcd(a,f)=1. For H≤J and each singular J-class C_i, let A_{H,i} be multiplication by W_{H,i} on the **class-representative cocenter basis**, reduced over F₂. Let L_H be the class permutation [y]↦[y^t]. Put q=2^f, l=k(H), choose 2^b≥l, and define

    P_{H,i}=A_{H,i}^{(q−1)2^b},       P_{H,I}=∏_{i∈I}P_{H,i}.

These are commuting idempotents commuting with L_H. On im P_{H,I}, let d_H be the dimension and

    K_H(j)=d_H−rank((L_H^j−1)P_{H,I}),       1≤j≤d_H.

Apply the two integer Möbius inversions of frozen I104 (9) to these K_H(j), obtaining c_{H,1}. Then, for **every** residue vector ρ on the nonempty support I,

    D_J Θ_t(I,ρ)=Σ_{H≤J} μ(H,J)|H| c_{H,1}.                    (18)

In particular the right side is an exact integer and is independent of the positive exponents on this support. Every nonempty support admits an accessible residue vector. Consequently all accessible moment zeros are equivalent, under these hypotheses, to the 2^r−1 integer zero tests (18). No scalar trace in F₂ is substituted for c_{H,1}.

**Proof.** Choose the cyclotomic local field K=Q₂(ζ_E), with the chosen embedding. Its residue field is F_q. Indeed X^{E′}−1 is separable modulo 2 and all its roots lie in F_{2^f}; the primitive roots first occur there. Hensel lifting produces exactly the unramified extension of degree f. For v≥2, the polynomial Φ_{2^v}(1+X)=(1+X)^{2^{v−1}}+1 has constant coefficient 2, leading coefficient 1, and every interior coefficient even. It is Eisenstein, also over that unramified extension, so adjoining ζ_{2^v} is totally ramified. The cases v≤1 add no field. Every integral central scalar lies in its valuation ring. Admissibility makes γ_t an automorphism of this local field, acting on residues by 2^a and fixing the 2-power roots. For a fixed ordinary χ and an integral rational class sum W, γ_t(λ_χ(W))=λ_{χ^{γ_t}}(W)=λ_χ(W). Its residue belongs to the fixed field F_{2^{gcd(a,f)}}=F₂. Thus on fixed χ the Teichmüller value is either 0 or 1.

For any such W, the central elements W^{(q−1)2^k} converge to a central idempotent e_W whose coordinate is 1 exactly at the unit eigenvalues. Indeed this follows coordinatewise in the split semisimple algebra from the p-power estimate, and hence in its finite-dimensional vector-space topology. The approximants are integral, and the integral group algebra is a closed finite free lattice, so e_W is integral. They have Z₂ coefficients, hence so does the limit. In particular its reduction is fixed by coefficient Frobenius. The selected ordinary set is γ_t-stable, because γ_t preserves valuation. Multiplication by e_W commutes with L_t in characteristic zero and integrally.

On the reduced l-dimensional cocenter every eigenvalue of A_W lies in F_q, by reducing its characteristic polynomial, whose characteristic-zero eigenvalues are the λ_χ. Over F_q its Jordan blocks have nilpotent length at most l. Raising to 2^b≥l kills those nilpotent parts. Raising the nonzero eigenvalues to q−1 gives 1 and sends zero eigenvalues to 0. Thus A_W^{(q−1)2^b} is exactly the reduction of multiplication by e_W. This also proves independence of b once 2^b≥l, idempotence and all asserted commutations. Products select the common unit fibers.

For the product idempotent e_I, the frozen I104 subsection/lattice operation applies: its reduction is coefficient-Frobenius stable. The integral cocenter summand is an integral permutation module for L_t, isomorphic to the permutation lattice on subsection simple labels. This assertion includes 2-torsion in the cyclic action and uses no averaging. Its characteristic-zero trace equals the number of γ_t-fixed ordinary labels in its selected coordinates. Reduction, followed by scalar extension to an algebraic closure, gives the same K_H(j). Kernel dimensions count gcd of cycle lengths with j in every characteristic. The frozen two inversions therefore recover the integer number c_{H,1} of fixed labels, even when a cycle length is even. This establishes the required trace without confusing it with its residue.

On a fixed ordinary χ, every active Teichmüller factor equals 1 iff that coordinate is a unit, and otherwise is 0, independently of its positive exponent. Its contribution to (13) is therefore the indicator selected by e_I. Summing proves (18). Finally choose residues on any nonempty support with sum 1 modulo q−1 (set all but one arbitrarily and solve for the remaining one). This is accessible with b=0. The positive-realization argument already audited makes it an actual positive tuple multiplicity sequence. ∎

This is a construction with finite stopping bounds: q and 2^b are explicit; matrices are over F₂; the reconstruction involves at most k(H) kernel dimensions. The Teichmüller arithmetic is exactly 0/1 on the selected fixed ordinary labels, proved by the local Frobenius action. It is not an empirical p-adic convergence test. The hypothesis gcd(a,f)=1 is retained; no extension to all a or other p is claimed for this implementation.

### 3.2 Exact certificates, and what they do not establish

`exact_moments.py` constructs groups from permutation or affine multiplication, enumerates their actual subgroup lattices and Möbius functions, and builds the matrices in P110 directly by

    A_{H,i}[y]=Σ_{u∈H∩C_i}[uy].

It records every subgroup with nonzero Möbius coefficient, every H-class, every matrix and projector, and every rank profile for every nonempty support. It checks the trivial 2-core and admissible power, projector identities, commutation, and the reconstructed nonnegative integral cycle counts. `exact-moments.json` contains the full certificates, not just a minimum valuation.

At p=2,a=1 the exact moment numerators are all zero for:

* S3: 6 subgroups, one support, t=5.
* A5: 59 subgroups, one support, t=17.
* D14: 10 subgroups, one support, t=9.
* S3×C3: 14 subgroups, seven supports, t=5.
* S3×C5: 12 subgroups, 31 supports, t=17.
* S5: 156 subgroups, 15 supports, t=17.

There are 56 exact support tests. By P110 they cover all accessible exponents for those fixed inputs, and T108 supplies their corresponding all-length, all-multiset consequence. This inference uses the proved finite reconstruction and T108, not extrapolation from finite tuple lengths. The finite certificates remain computational evidence and do not prove the assertion for arbitrary J. No counterexample to admissible TD or G104 was found.

An independent A4 diagnostic recovers rank profile (3,4,3,4) and fixed-label count 2 on its four-dimensional unit fiber, while all four detector residues are 1. This explicitly exercises the even 2-cycle, where reducing an integer trace loses information. The script also checks exact ramified arithmetic and the positive-residue/dilation step separately.

The hoped-for universal cancellation would require the signed integers on the right side of (18) to vanish for every p-core-free J (already at this restricted p,a). The projectors for H and K≤H are not related by a supplied equivariant bijection of their ordinary-label fibers. Restriction of modules is additive and may decompose; restriction of central coefficients is not a unital algebra map on arbitrary centers. Neither gives the required fiberwise transport. The accepted t=1 moment equations say the corresponding **total ranks** cancel; they do not determine these fixed-label integers. A4 demonstrates the lost data within one term, not noncancellation of the full sum. Thus (18) is a paid exact computation method, not a universal zero proof.

### 3.3 A genuine uniform product transfer

**Proposition U110.** Let K,L be finite groups, p∤|L|, and suppose K and L have no common nontrivial quotient. For any unit t modulo exp(K×L), prescribe multiplicities m_{ij} of all p-singular classes C_i×D_j of K×L. Put m_i=Σ_jm_{ij} and m′_j=Σ_im_{ij}, with positive total n. Let F_{L,t}(m′) be the generating simultaneous-orbit count in L for **one fixed ordered word** of L-class labels with multiplicities m′, using the same relation and unrestricted L punctures. Then

    N_{K×L,t}(m)= [∏_i m_i! / ∏_{ij} m_{ij}!] · N_{K,t}(m_i)
                  · F_{L,t}(m′).                                (19)

All three factors are nonnegative integers. In particular any all-multiset divisibility threshold for K transfers unchanged to K×L. If t is admissible on the product it is admissible on K. For p-core-free K the product is p-core-free. Coprimality of |K| and |L| is sufficient for the quotient hypothesis, but is not necessary.

**Proof.** A subgroup S≤K×L surjecting to both factors gives normal subgroups N_K={x:(x,1)∈S}, N_L={y:(1,y)∈S}. Assigning to x the coset of any y with (x,y)∈S gives a well-defined isomorphism K/N_K≅L/N_L: different choices differ by N_L, and multiplication and the analogous inverse are immediate. The no-common-quotient hypothesis forces these quotients trivial, hence S=K×L. Thus a product tuple generates exactly when its two projections generate.

For a fixed ordered product-class word, its equations, choices and simultaneous inner conjugations split into the two factors. Its generating orbit set is the product of the two fixed-word generating orbit sets. Their cardinalities are F_{K,t}(m_i) and F_{L,t}(m′). The mixed central convolution proof in §2.3 shows each fixed-word count depends only on its multiplicities; this does not require punctures in L to be singular. Summing over the M(m) product-class words gives M(m)F_KF_L. Replace F_K by N_K/M(m_i); the quotient M(m)/M(m_i)=∏_i m_i!/∏_{ij}m_{ij}! is a product of multinomial integers. This proves (19), without dividing a congruence by a possibly nonunit integer.

Since L has no p-singular element, the singular classes of the product are exactly C_i×D_j. The restriction of the exponent congruences for t is immediate. A normal p-subgroup of the product projects to normal p-subgroups of both factors; both are trivial under the stated conditions. Finally any common quotient has order dividing gcd(|K|,|L|), proving the sufficient coprimality condition. ∎

**Corollary.** For every finite abelian group A of odd order, J=A5×A, p=2, every a≥1 and its admissible t, every p-singular J-class multiset of total 2^s, and every s≥1,

    v₂(N^t_{J,s}(M))≥s+3,

with v₂(0)=∞. Hence s₀=max(1,h−3) works uniformly in the multiset **and in A and a**.

Indeed A5 has no nontrivial abelian quotient. One elementary verification of perfectness is that the commutator of (12)(34) and (12)(35) is a 3-cycle; all 3-cycles are A5-conjugate and generate A5, so its commutator subgroup is A5. Apply (19) and the frozen, independently passed I104 all-a estimate v₂(N_A5)≥s+3. Its single singular class makes this literal for all product multisets. This is an actual infinite-family uniform estimate, but its complete proof reduces to the passed A5 calculation, the explicit subdirect-product argument and multinomial integrality. It is technical, not a substantial nomination or a new G104 group-family theorem.

## 4. Mechanism II — equivariant local-point pairing and the residual component

This mechanism uses local points and coefficient-compatible Brauer maps, independently of the central scalar calculation. The attempt was to build an integral equivariant cancellation before taking any trace, then use an auxiliary local p-group to reach the missing trivial stratum.

### 4.1 An actual pairing, including coefficient Galois action

Fix a central idempotent b∈kG and a finite quotient Γ of its coefficient stabilizer through which the finite label sets below factor. Fix a BBY pair (L,u) with L a **nontrivial** p-group. For each strict p-chain C=(1=Q₀<…<Q_r), put H_C=G_C and b_C=Br_{Q_r}(b). Use the exact BBY set of data (C,P_γ,π), where P≤H_C, γ is a local point on (kH_C b_C)^P, π:L→P is an isomorphism, and πuπ⁻¹ is realized by an element normalizing that point. Take G-orbits of the entire data, with parity r. These finite sets carry commuting coefficient Γ and right Aut(L,u) actions as in BBY.

**Proposition C110.** The even and odd data sets just defined are isomorphic as Γ×Aut(L,u)-sets. Their free integral permutation modules consequently admit a split two-term equivariant contraction. This assertion concerns the specified local-point sets; it does not assert a splendid Rickard complex or a simplicial differential on block algebras.

**Proof.** Given the data, choose the largest i with P⊄Q_i, which exists because P≠1. Insert Q_iP immediately after Q_i unless it is already the next term, in which case delete it. P normalizes all Q_i, so Q_iP is a p-group; later Q_j contain both factors. The last term not containing P is unchanged by the operation, so it is a sign-reversing involution, including terminal insertion/deletion.

If C′ is the partner chain, then

    N_{H_C}(P)=N_{H_C′}(P),     C_{H_C}(P)=C_{H_C′}(P),
    Br_P(b_C)=Br_P(b_C′) in their common centralizer algebra.

For the normalizer equality, an element normalizing P and every Q_j also normalizes Q_iP; conversely a deleted term Q_iP is reconstructed from P and Q_i. For the Brauer equality, both restrictions are the coefficient truncation of b to the common centralizer of P and the terminal chain subgroup (with P appended if necessary). This is precisely the complete BBY operation.

The Brauer local-point bijection used there identifies γ and γ′ through their common image point in this identical centralizer algebra. It preserves the realizing normalizer of πuπ⁻¹ and all stabilizers needed for the data. The image is unique, and applying the construction twice recovers γ. Conjugation commutes with this identification. A coefficient automorphism also commutes with coefficient truncation, takes units to units and primitive idempotents to primitive idempotents, and hence commutes with the local-point bijection and its inverse. It leaves all subgroups and π unchanged. Thus the involution commutes with Γ as well as with G. Precomposing π by the BBY right action changes neither P nor the Brauer identification, so the involution commutes with Aut(L,u). It descends to G-orbits and pairs their parities.

Let d send each even basis element to its paired odd element. It is an integral equivariant isomorphism; its inverse h gives dh=1 and hd=1. The two-term complex with this differential is therefore contractible over Z, with no division by |Γ| and no restriction on p-torsion in Γ. ∎

This pays the coefficient-equivariance of the **nontrivial** local-point cancellation. Its full scope is a concrete refinement of the same BBY Brauer-point involution, including the later author version. It is technical. No inference from ordinary character multiplicities to an unspecified equivariant functor category is made: the result is an explicit bijection of the finite data sets just defined.

### 4.2 Attempt to use an auxiliary p-group to remove the residual term

For L=1, P=1 and u=1, the condition P⊄Q_i never holds. The entire pairing construction stops. The local points at P=1 are the primitive-idempotent classes, i.e. the indecomposable projective labels. Their Γ-action corresponds to the simple-module action. These are exactly the fixed labels in Huang–Yılmaz's residual functor, not extra nontrivial local terms that were accidentally omitted.

An attempted repair was to pass to G×C_p and use the nontrivial central P=C_p. This is an actual group, so it avoids treating a power map as an automorphism. It still does not yield the target. For every chain in the product normalized by this P, the above involution inserts/deletes its product with P. In particular chains lying wholly in G×1 pair with chains ending after the central P has been adjoined (or inserted at the first needed position). The Brauer label transport is the identity on the residual G-label information, through the common centralizer algebra. Removing the partner chains to leave the desired G-side breaks the contraction: their boundary contribution is the identical label set with the opposite sign. The ambient zero has the form X−X, not an independently zero X. This explains exactly why nontrivial P in the enlarged group cannot be identified with cancellation at P=1 of the original group. No source operation provides a vanishing of that boundary.

The underlying subgroup toggles were exhaustively checked on S4 as a finite diagnostic. The proof of coefficient-compatible local-point transport is the algebraic argument above; that finite test checks only the subgroup skeleton and is labeled accordingly.

### 4.3 Minimal-field averaging and a quantitative residual estimate

Another attempt starts with the geometric equality given by A and BBY and tries to descend a characteristic-zero isomorphism by averaging. This fails at a concrete linear-algebra step, even when |Γ| is invertible. Let Γ=C₂, X have two fixed labels and Y one two-cycle. Both permutation modules have dimension two. If Γ acts by I on X and the swap S on Y, the average of a linear comparison A is (A+AS)/2=A(I+S)/2, of rank at most one. It cannot be invertible. With p=2, averaging also fails to be integral. This is an obstruction to the proposed **automatic averaging construction**, not a group-block counterexample. The frozen symmetric forms show that arithmetic permutation data can indeed differ in geometrically isomorphic symmetric algebras; no group-block realization is asserted.

For the actual detector, one can at least pay its complete error term. Fix G,p,a and a σ_a-stable idempotent E, the original supported integral lift w, and a finite local coefficient field containing all scalars, with ramification index e. Let Φ_{p^s,t} be the original chain trace sum and let

    δ_{G,E}(a)=Σ_{C/G} (−1)^|C| |S(kH_C E_C)^{σ_a}| − |S_proj(kGE)^{σ_a}|.

Use the full chain idempotents and the frozen nonnormal/subsection toggles. The original detector's 0/1 residues, with the p-power estimate already audited, imply

    v_p(Φ_{p^s,t}−δ_{G,E}(a))≥(s+1)/e.                         (20)

**Proof.** Cancel nonnormal chains first; their scalar operators and L_t agree before and after the toggle. For each remaining chain and fixed ordinary χ the scalar λ has residue 0 or 1. Its p^s power differs from that residue by valuation at least (s+1)/e. A finite signed sum cannot decrease this bound. The limit sum counts the selected fixed ordinary labels with the defect-zero term removed; the frozen equivariant subsection toggle identifies it with the integer δ displayed above, retaining its block assignment. There is no denominator in this eigenvalue trace calculation. If one uses the actual-tuple numerator B_s=|G|Φ instead, (20) becomes v_p(B_s−|G|δ)≥v_p(|G|)+(s+1)/e. ∎

Numerical AWC gives δ(id)=0 for the identity coefficient action; this is not the assertion δ_{G,E}(a=1)=0. It does not give δ(a)=0. If an element σ has prime-power order ℓ^r on all label sets in this expression, elementary orbit decomposition at least gives δ(σ)≡δ(id)=0 mod ℓ. This follows because every nonfixed orbit has cardinality divisible by ℓ, and it holds for signed sums too. It does not imply unbounded ℓ-adic valuation. The abstract defect 2[fixed point]−[two-cycle] already has dimension zero and nonzero trace 2 at the generator. Thus neither (20) nor this congruence supplies the missing zero.

The precise stopping point of this route is the vanishing of the virtual cyclic permutation character δ, on the trivial local-point stratum, for every pair and subquotient required by the frozen inversion. A genuine comparison over the minimal field, with inverse morphisms, would pay it. No such comparison is constructed here.

## 5. Stronger complete operations and technical disposition

Live primary metadata checked on 2026-10-10 still exposes [Huang–Yılmaz v1](https://arxiv.org/abs/2512.07369), [FFZ v2](https://arxiv.org/abs/2512.15243), [Huang category v3](https://arxiv.org/abs/2604.06166), and [BBY arXiv v1](https://arxiv.org/abs/2507.20314). The later [BBY author manuscript](https://yilmazdeniz.bilkent.edu.tr/papers/alperin-functorial.pdf), dated February 11, 2026 in its own bytes, is newly frozen and read through its ending. It is kept distinct from arXiv v1; its residual term is still n_{G,b}[S_{1,1,F}]. The [publisher record](https://link.springer.com/article/10.1007/s00209-026-03999-5) identifies Math. Z. 312, article 112, version of record March 19, 2026, accepted February 11. Its subscription proof was not accessed; the dated author version supplies the full proof used here. The [Huang–Yılmaz published record](https://www.sciencedirect.com/science/article/pii/S0021869326002243) identifies Journal of Algebra 701 (September 2026), 312–327; the proof source used is their separately frozen author manuscript.

The significance reference remains the named blockwise Galois Alperin weight conjecture, Huang–Yılmaz Conjecture 1.2. Their universal chain theorem, FFZ's reduction, and Huang's categorical reformulation are evidence of research interest, not a priority or ranking certificate.

The complete-operation comparisons are concrete:

* A's marked-cover construction fixes all |J|th roots of unity and preserves peripheral classes through tangent characters. Its descent splits a center-valued extension over a Sylow p-subgroup. Neither operation preserves the new handle constraint. The large index already charges any new descended point; the specialization proof requires equality, not the loss bound alone.
* A's functorial consequence explicitly has algebraically closed coefficient fields. BBY's stable quotient removes the functor generated at the trivial group. C110 retains Γ on the nontrivial local-point sets but cannot restore that removed component. This is a complete source-operation reduction of C110's actual scope.
* Huang–Yılmaz §3 uses the span of **fixed PIM labels**, not the invariant subspace of their permutation span (the latter counts orbits). Its minimal-field proof in §4 begins with inverse bimodule-class morphisms over the common field, extends them to a splitting field, and obtains a cyclic permutation-module comparison. Averaging an arbitrary geometric inverse pair does not preserve the inverse identities, as the rank-one example shows. Their Galois-conjugate-block construction in §5 has different endpoints.
* ID constructs σ^m(U)⊗T_λ⊗U^∨ between a block and its Frobenius twist. Its actual inner factors, Teichmüller overlap errors, central-kernel descent and final H²(S,T)=0 for a pure p-subgroup with trivial scalar action were retained. Its assembly produces integral Morita finiteness and extension to a fixed complete DVR. These operations do not connect the block to its weight endpoint or give the needed cyclic descent datum.
* FFZ v2 uses an equivariant H-triple comparison on universal p′-covers at the minimal-normal-subgroup step, then Clifford and DGN transport. Its defining-characteristic result is not an arbitrary-group construction. Huang v3's final assembly requires compatible equivariant bijections on maximal subgroups, while its twisted central-extension operation retains the F_p-valued cocycle condition. Numeric AWC is not any of these inputs.
* P110 is fully reduced to integral central power limits, finite-field Jordan nilpotence, the already passed I104 permutation-summand lift, and two Möbius inversions. It resolves the calculation of the moments at its stated p,a scope, not their universal zero. U110 is fully reduced to subdirect products and the mixed central convolution operation; its A5×A estimate imports the already paid all-a A5 bound. Equation (20) is the source detector estimate with its error retained. These are technical deductions at their complete scopes.

No result is rejected merely because it uses classical tools. The reason for **no nomination** is that the complete paid scopes reduce as above and neither route supplies the arbitrary-group cancellation. The branch should remain parked until a construction preserves and cancels the residual ordinary/simple label action across the required subgroup or weight endpoints. T108 must not be cited as proving its own zero conditions.

## 6. Evidence replay, retained failures, and scope

The complete tree and I88 mapping are reused in place: 13,223 entries, 749 manuscript families, 10,373 original positions (9,340 I14 originals, 257 other byte representations, 776 inherited PDF texts). No recursive corpus copies or whole-corpus downloads were made. The inherited I108 verifier replays its exact 245/353 occurrence multisets and all original-source hashes. The I110 lexical query preserves every occurrence with path, one-based splitline, half-open character span, exact match and full line. Lexical searches are not semantic reading or absence/novelty proofs.

The exact moment calculation is finite and reproducible. Its structural justification is P110, including its local field and integer permutation-lift proof; the saved zeros are not inferred from repeated congruences. The separate checks cover ramified power estimates, all positive accessible-residue vectors in a stated small domain, dilation valuations, A4's even Galois cycle, the product formula by direct tuple enumeration, and the subgroup part of C110. The universal proofs are in the report; no hash is a proof of those arguments.

Retained work limitations/failures: some early combined catalogue/ledger/PDF terminal reads were truncated; relied-on proof ranges were then read in bounded ranges. The initial filename discovery listed some unrelated artifact names but did not read or bind their contents. No GAP or Sage executable was available, so the exact finite calculation uses elementary bit-matrix arithmetic with the inherited group constructors. These are discovery limitations, not failed theorem tests. The original I104/I108 retained failed runs remain sealed dependencies. Any I110 validation failure is retained separately and is not overwritten as a pass.

Replay from the repository root:

```text
python3 -B frontier/experiments/i110_galois_moment_cancellation/verify.py
```

The final verifier is offline and read-only: no network, writes, bytecode, repair, or resealing. It checks its exact owned inventory, frozen originals and immutable references, passage/line conventions, raw primary response hashes, the one new PDF's stdout-only re-extraction, the inherited sealed I108 replay, the exact I110 lexical occurrence multiset, and the new finite certificates. Preparation is a separate script, never imported by the verifier. Validation is performed before the one final seal; final replay writes only to stdout. Its PASS is evidence integrity and finite reproducibility, not certification of universal truth, novelty, or contribution acceptance.
