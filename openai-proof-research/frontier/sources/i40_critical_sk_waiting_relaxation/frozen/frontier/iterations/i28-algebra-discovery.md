# I28 algebra/representation discovery: filtered persistence and three scoped gaps

**Disposition: no substantial finding proposed for acceptance.** This report screens three distinct targets, proves a source-relative filtered-persistence statement in full, develops a second approach and diagnoses its failure, and records explicit obstructions to two other constructions. The persistence statement is useful technical progress, but a genuinely nonconical example satisfying the obstructed numerical geometry has not been constructed. Rees machinery plus the source's already-general divisor lemmas is not, by itself, submitted as a substantial new discovery. No priority claim or finding number is assigned. Count changes belong to the parent.

## 1. Frozen scope, source contracts, and reading

The original task is preserved verbatim in `../sources/i28_algebra_discovery/task-brief.txt`. All OpenAI results below are accepted at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; this work tests new deductions, not upstream truth. No agents, shared-index edits, staging, commits, or pushes were performed. The only task writes are this report and the two assigned I28 directories.

The frozen inputs include AGENTS, TEN-FINDINGS, upstream metadata, CONTENTS, the **complete 749-manuscript** preprint tree, and the manifest of the **9,340-file** read-only text cache. CONTENTS advertises an older manuscript count; the complete tree controls inventory. Only 35 selected source files were copied, with both Git-blob SHA-1 and SHA-256 checked. The full cache was searched in place, not copied. See `pinned-manifest.json`, `inventory-audit.json`, `source-contracts.json`, and `read-passages.json` in the source directory. Exact retained primary-version bytes and retrieval dates are in `literature/*manifest.json`; search results and query records are retained separately. Full proof text of the three selected OpenAI papers and the unitarizability companion was read, including all Kurosh proof sections rather than only its lifting theorem.

Source abbreviations, each a pinned immutable manuscript directory:

- **U:** [Strong Ulam Stability](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Strong-Ulam-Stability-Characterizes-Amenability-October-5-2026), `build/strong-ulam-stability.tex`.
- **C:** [No small Cohen–Macaulay module](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Complete-Local-Domain-Without-a-Small-Cohen-Macaulay-Module-September-23-2026), `build/paper.tex`, `build/surface.tex`.
- **K:** [Kurosh counterexample](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Counterexample-to-Kuroshs-Division-Ring-Problem-September-23-2026), all twelve `build/sections/*.tex` files.
- **D:** [Unitarizability companion](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Unitarizability-Implies-Amenability-for-Countable-Groups-September-23-2026), all five proof sections. Its final C*-extension corollary is not used here, so the additional similarity theorem it cites is not an input to any deduction.

The earlier negative contexts are respected. Nothing here uses a signed Saxl quotient, finite-width coverage, or palindromicity as character positivity. The lesson of I15/I17 is particularly relevant: expanding an operation already available inside a proof can be correct without being substantial. The filtered construction below is labeled accordingly. I25 significance and I27 geometric analysis remain separate tasks.

## 2. Target U: a dimension-uniform finite-window correction theorem

### Exact target and strongest available interfaces

The proposed extension was: for every epsilon > 0, find a finite radius R >= 1 and delta > 0, depending on a fixed finitely generated amenable group and epsilon but **not on matrix size**, such that any normalized unitary map on the word ball of radius 2R with multiplicative defect <= delta for pairs in the radius-R ball is epsilon-close, on the fixed generators, to a representation on the same space. Even for Z² we may use coordinate boxes instead of word balls, at the cost of changing radii. The theorem would turn finite tests into a usable approximation procedure; it is different from global strong Ulam stability.

U, `thm:main`, quantifies over countable discrete groups and **all complex Hilbert spaces**; its defect is the supremum over every pair of group elements in operator norm. For every nonamenable countable group and every positive defect tolerance it constructs a separable witness at distance > 1/10 from all representations. The proof's stronger interfaces are `lem:priority` (Schur-complement metric transfer preserving a specified subspace), `lem:truncate`, `prop:comparison`, and the exact signed-frame witness `lem:witness`. In `eq:defect-bound` the estimate is C h + C N eta + C N h eta, with h = 1/(2 sqrt(L)), N = L+1. Alphabet sizes and the number of group locations do not enter C. The actual Hilbert space has a copy at every group location. Truncating locations is not a finite-dimensional version of the proof: it destroys unitarity of translations and the exact cancellation.

D is already stronger than a qualitative unitarizability headline: it gives nonunitarizable genuine representations with uniform bound 1+epsilon, using a direct sum of bounded cocycles whose implementer norms diverge. Its finite-dimensional **fibres** sit inside l²(G; C^k); those are not finite-dimensional representations when G is infinite. Neither this construction nor changing the Hilbert norm supplies the missing finite-window correction.

The positive amenable input is also not new: Burger–Ozawa–Thom, [arXiv:1010.0565v1](https://arxiv.org/abs/1010.0565v1), Theorem 3.1, records a global bound delta + 120 delta² for delta <= 1/10. Theorem 3.2 already treats an amenable subgroup acting approximately on a bounded map on a larger group. Its invariant-mean iteration uses all group elements. A relative-subgroup version or a fresh presentation of that averaging is therefore not a discovery here.

### Constructed obstruction, with a uniform constant

The proposed finite-window target is **false** in operator norm with dimension-independent constants. This is the classical clock-and-shift obstruction, not a new result. Here are the complete estimates needed for this screen.

Let n >= 8 be even, zeta = exp(2 pi i/n), and on C^n put

    U e_j = zeta^j e_j,       V e_j = e_(j+1 mod n).

Thus UV = zeta VU. Set mu(a,b) = U^a V^b for integers a,b. Direct multiplication gives

    mu(a,b) mu(c,d) = zeta^(-bc) mu(a+c,b+d).

On the box |a|,|b|,|c|,|d| <= R, the defect is at most 2 pi R²/n. Restricting mu to the box of radius 2R therefore gives arbitrarily small local defects as n grows.

Nevertheless there are no commuting unitaries U',V' with both ||U'-U|| < 1/10 and ||V'-V|| < 1/10. Suppose otherwise. Connect U to U' and V to V' by their short unitary logarithmic paths U_t,V_t. Functional calculus on angles in (-pi,pi) gives ||U_t-U|| <= ||U'-U|| and the analogous inequality for V. For C_t = U_t V_t U_t* V_t*, telescoping four unitary factors gives

    ||C_t-C_0|| <= 2 ||U_t-U|| + 2 ||V_t-V|| < 2/5.

Since C_0 = zeta I and ||zeta I-I|| < 1 for n >= 8, every C_t has ||C_t-I|| < 7/5 < 2. Its spectrum avoids -1, so its principal logarithm varies continuously. Also det(C_t)=1. Consequently

    kappa(t) = Tr(log C_t)/(2 pi i)

is a continuous integer-valued function. At t=0 it is 1, since n log(zeta)=2 pi i, while at t=1 it is 0 because U',V' commute. This contradiction proves the uniform separation. Every exact representation of Z² has commuting generator images, so the target fails for epsilon=1/10, regardless of the chosen finite R and positive delta.

There is no conflict with U: the same globally defined mu has defect **exactly 2**, by taking b=n/2 and c=1. The local-to-global step fails before the global theorem can be used. Fixed n, normalized Hilbert–Schmidt metrics, and infinite-dimensional norm limits have different compactness and stability questions; none is identified with this assertion.

The comparison is primary and explicit: Loring's [Quantitative K-theory](https://arxiv.org/abs/1302.0349), Section 2, develops the winding/logarithm index and quantitative separation of almost-commuting pairs. Our conservative 1/10 constant is only a diagnostic, not a claimed improvement. The retained version history identifies v4 as the latest version checked; both inspected v3 bytes and the later v4 bytes are preserved.

A second tempting upgrade, pointwise norm-continuous parameter families, also needs an extra hypothesis. An invariant mean does not preserve that continuity automatically: on Z take f_j(t)=min(1,|j|t), t in [0,1]. Each f_j is continuous; every invariant mean gives mean_j f_j(0)=0 and mean_j f_j(t)=1 for t>0, since the exceptional set is finite. This is an obstruction to the averaging step, not a counterexample to every possible continuous correction. Uniform equicontinuity in j would fix this particular issue, but using it merely recovers a standard uniform-family argument.

Current comparison also rules out presenting dimension enlargement as a new repair. Lubotzky–Salomon, [2607.17578v1](https://arxiv.org/abs/2607.17578v1), Theorem 2.3, treats sequences of matrix pairs with commutator norm tending to zero. Their proof uses |w_n|/d_n -> 0, adds |w_n| clock-and-shift blocks of size m_n -> infinity with |w_n|m_n/d_n -> 0, and then applies the established zero-winding correction theorem. The output has size k_n=d_n+o(d_n), with the original pair approximated by compression through an isometry. This preserves operator norm but changes the dimension contract. Section 2 and the full proof of Theorem 2.3 were inspected; no quantitative rate absent from that theorem is inferred.

**Remaining obligation for a different substantial target:** specify an extra structure or a quantitative algorithm beyond the already-known zero-winding and flexible corrections, and prove its uniform bounds. Merely adding a vanishing winding hypothesis for Z² is already covered by the Gong–Lin/Eilers–Loring–Pedersen theorem recalled in that paper. No new correction algorithm is supplied. The unqualified same-space local target is rejected.

## 3. Target C: persistence in genuinely nonconical filtered deformations

### Exact goal and source/companion comparison

The substantive goal is to construct a complete local complex domain R', not isomorphic to the source's completed cone, with a complete multiplicative filtration whose associated graded ring is the section ring of an obstructed surface, and prove that R' has no nonzero finite MCM module. A formal perturbation of displayed equations is insufficient: preservation of the full initial ideal, normality or the needed regular model, and nontriviality of the deformation must all be proved. An ordinary flat extension or a new polarization of the same cone would not meet this goal.

C proves a more useful interface than its example alone. If X is a smooth integral projective complex surface and H is ample and globally generated, its completed section ring has an MCM module only if

    Delta(X) := K_X² - 2 c_2(X) <= 6 H².                       (C1)

C, `lem:balance`, applies to **any** integral Noetherian scheme with a smooth projective Cartier divisor X of conormal H, and any torsion-free extension with torsion-free restriction. It changes the extension only along X and confines normalized HN slopes to width <=1. C, `lem:lattice`, applies to a torsion-free sheaf on **any** integral Noetherian scheme with a Cartier divisor P² of conormal O(1), provided the sheaf is trivial off that divisor. It gives

    v(F) := 2 ch_2(F)/rank(F) - (c_1(F)/rank(F))² >= 0.       (C2)

The source proves (C2) by finite Cartier-quotient layers and derived restriction; it does not require a splitting into line bundles. C, `lem:factor` and `eq:mixture`, then bound the same expression above by 1/2 - Delta(X)/(12H²). These statements, including their full proofs, are the available machinery. Merely restating them for a supplied finite model would be an automatic extension.

Current primary comparisons materially narrow the possible contribution:

- Anghel, [2609.15589v1](https://arxiv.org/abs/2609.15589v1), Theorems 1.1/1.3 and Sections 2–3, excludes **graded** MCM modules when Delta(X)>3H². Its stronger constant uses Horrocks splitting and a majorization comparison of slopes. It explicitly distinguishes the full section ring from its degree-one generated subring. It does not allow an arbitrary nongraded local module to be replaced by a graded one.
- Chen, [2609.24142v1](https://arxiv.org/abs/2609.24142v1), Main claim 1.1, proposes a stronger quantitative completed-local result for K_X numerically equivalent to 4H: dim H²_m(M) >= (15H²/8-chi(O_X)) rank(M). Sections 3–6 already contain a width-one normalization and a fixed-source cohomology-survival argument across the Cartier divisor. The text labels this a proposed claim. It is compared, not imported as an accepted extra axiom. Those proof operations are not new bridges here.
- Chen–Sun, [1808.02172v1](https://arxiv.org/abs/1808.02172v1), Theorem 1.4 and Remark 1.5, already construct optimal extensions by elementary transformations across a negative divisor; negativity, rather than the exceptional divisor being projective space, is central.
- Xie, [2608.10962v1](https://arxiv.org/abs/2608.10962v1), Theorem 1.1, has a positive MCM existence result with depth d-1 and **cyclic deficiency module**. Those hypotheses are not inferred from a deformation or from quasi-Gorensteinness here. Bhatt–Hochster–Ma [2410.18372v2](https://arxiv.org/abs/2410.18372v2) concerns asymptotic substitutes and gives context, not a deformation-descent theorem used below.

### Method A: complete construction of the filtered finite model

The following is a **proved technical source-relative proposition**, not the unachieved new-example claim.

**Filtered persistence proposition.** Let (R,m) be a complete Noetherian local C-algebra with residue field C. Let F_0 R=R, F_1 R=m, F_2 R,... be descending ideals with F_i F_j contained in F_(i+j), separated and defining the m-adic topology. Assume an isomorphism of graded C-algebras

    gr_F R = T(X,H) = direct_sum_(n>=0) H^0(X,O_X(nH)),        (C3)

where X is a smooth integral projective complex surface and H is ample and globally generated. No degree-one generation of T is assumed. Then R is a three-dimensional domain, regular away from m; in fact it is normal. If Delta(X)>6H², R has no nonzero finitely generated MCM module.

The assertion is conditional on the precise associated-graded identification (C3), but it does **not** assume the missing finite model, descent of a module, or a grading on a module. Those model properties are constructed next. It does not say that every flat deformation satisfies (C3).

**Step A1: filtered Noether normalization and finite generation.** Choose three sections s_0,s_1,s_2 of H with no common zero, as in C's finite-projection proof. They define a finite surjective f:X -> P², with f^*O(1)=H and degree h=H². Thus T is finite over S=C[s_0,s_1,s_2], a polynomial ring, by the source's full proof, including the non-degree-one-generated case. Choose homogeneous S-module generators bbar_j of degrees d_j>=0. Lift s_i to x_i in F_1 R and bbar_j to b_j in F_(d_j) R.

Continuity defines A=C[[x_0,x_1,x_2]] -> R. This map is injective: the first nonzero homogeneous term of a nonzero series in the three formal variables maps to its nonzero polynomial in the algebraically independent s_i. Denote the maximal ideal of A by n. For every integer q>=0 we claim the exact equality

    F_q R = sum_j n^max(q-d_j,0) b_j.                       (C4)

One inclusion follows from multiplicativity. For the other, start with r in F_q. Express its initial form, in its actual degree k>=q, as a sum of homogeneous polynomials in the s_i times bbar_j. Subtract the corresponding polynomial combination of the lifts. The residual order strictly increases. Repeating degree by degree produces, for each j, a convergent power series coefficient in n^max(q-d_j,0). The chosen topology is m-adic and R is complete and separated, so the residual tends to zero. There are finitely many b_j, giving (C4). This proves both finite generation of R as an A-module and strict control of the filtration, rather than assuming them.

The leading-term product in the domain T shows R is a domain. The finite injective integral map A -> R gives dim R=3. Formula (C4), with D=max d_j, gives F_q contained in n^(q-D)R for q>=D, while n^q R is contained in F_q; hence nR is m-primary. This also follows directly from cofinality and the finite associated-graded normalization.

**Step A2: a finite Rees algebra without standard grading.** Write

    B = direct_sum_(q>=0) n^q u^q,
    C_F = direct_sum_(q>=0) F_q R u^q.

These are ordinary graded algebras, not a Laurent or an analytically completed Proj construction. B maps injectively to C_F. Formula (C4) implies that the finite list

    b_j u^k,       0<=k<=d_j,

generates C_F as a B-module: at degree q use k=min(q,d_j), with coefficient in n^(q-k) u^(q-k). Therefore C_F is Noetherian and finite graded over B. Put V=Proj B, the blowup of Spec A at n, and W=Proj C_F. Since B is generated in degree one, the irrelevant ideal of C_F has the same radical as B_+ C_F (finite graded generation implies this, or (C4) implies it directly). Consequently W -> V is finite, and the charts x_i u cover W. The composite W -> Spec R is projective. On the complement of m all filtration ideals become the unit ideal, so its Proj is canonically Spec R off m. This proves that p:W -> Spec R is an isomorphism there.

**Step A3: the exceptional divisor and its conormal.** On the chart x_i u !=0, every r in F_(q+1) contributes

    r u^q = x_i (r u^(q+1))/(x_i u).

Conversely multiplication by x_i carries F_q into F_(q+1). The homogeneous kernel of C_F -> gr_F R therefore becomes the principal ideal (x_i) on this chart. Its quotient is (T[s_i^(-1)])_0, the coordinate ring of X where s_i!=0. These charts glue to the **given X**, not an altered Veronese. Since W is integral, x_i is a nonzerodivisor. Thus X is an effective Cartier divisor.

The same calculation with q=0 shows m O_W=(x_i) on this chart. Also n O_V is locally generated by x_i, and the other x_j are multiples of x_i on the chart. Hence, writing J=O_W(-X) and I=O_V(-P²),

    J = g^*I,             J|_X = O_X(H),             I|_(P²)=O(1).   (C5)

The finite restriction g|_X is exactly f. No assumption that T is generated in degree one has entered. Degree-one sections covering Proj are enough to identify O_Proj(T)(1) with H.

**Step A4: regularity and normality.** Along X a local equation is regular and its quotient local ring is regular because X is smooth. Lifting generators of that quotient maximal ideal proves that the local ring of W is regular. Every point of W specializes to X: its closure is proper over the local base Spec R, and its nonempty closed image contains the closed point. Regularity therefore holds everywhere by localization. The model is integral, as each chart is a subring of Frac(R), and p is an isomorphism on a dense puncture. Thus R is regular away from m.

For completeness, normality can also be proved, although the MCM argument below does not need to assume it. T is normal by C's section-ring proof, so it has depth at least two at the irrelevant ideal. Choose the first two degree-one normalization sections to be a regular sequence on T: a first nonzero section is regular; the associated primes after quotienting by it have height one by S2, and none contains all T_1, since its radical is the irrelevant maximal ideal. Over C a general second section avoids these finitely many primes. Choose the third to complete the finite projection. Initial-form lifting shows x_0,x_1 is regular on R: for a principal ideal generated by an element with regular initial form, order additivity identifies the associated graded quotient with the quotient by that initial form. Completeness makes the successive division argument converge. Hence depth R>=2. Together with regularity off m this is S2 and R1; Serre's criterion gives normality.

**Step A5: carry an arbitrary local MCM module through the model.** Suppose M is nonzero, finite, and has depth 3 over R. The x_i form a system of parameters and therefore an M-regular sequence. As a finite A-module, M is free by Auslander–Buchsbaum, say A^N with N>0. The generic algebra R tensor_A Frac(A) is a finite-dimensional domain over a field, hence a field. It follows that M has a positive generic rank r over R, and is torsion-free: a kernel of multiplication by a nonzero R-element would become zero over Frac(A) and hence be A-torsion in an A-free module.

M is locally free on the puncture. Indeed CM modules of full support localize to CM modules, and the punctured local rings are regular; apply Auslander–Buchsbaum there. On the regular W take E=(p^* M_tilde)**. It agrees with this bundle off X and has a torsion-free positive-rank restriction P=E|_X. To check the last point, at any nongeneric point of X the reflexive sheaf E has depth at least two, so quotienting by the Cartier equation leaves depth at least one. At the generic point of X it is free over a DVR. There are no embedded associated points of its restriction.

Use C, `lem:balance`, to modify E along X until the HN slopes of P have width at most one; torsion-freeness and the punctured bundle are preserved. Finite pushforward gives g_*E torsion-free on V, trivial of rank N off P², and

    (g_*E)|_(P²) = f_*P

by (C5) and exact finite pushforward. C, `lem:lattice`, applies on this **constructed** V and gives v(f_*P)>=0. Its rank is both N and r h, by generic restriction and finite pushforward on X. Finally C, `lem:factor`, followed by the exact variance-mixture identity on the HN factors, gives

    0 <= v(f_*P) <= 1/2 - Delta(X)/(12h).

When Delta(X)>6h this is impossible. This proves the proposition, for arbitrary finite modules and all ranks. All rings are commutative, all fields here have characteristic zero, and all completions used are the specified m-adic completions. No module descent to a graded module occurs. □

### A concrete deformation exercising the construction, and its limit

The Rees construction is not restricted to a formal renaming of the cone. Consider, as a **mechanism test**, the one-parameter family

    R_lambda = C[[a,b,c,d]] /
       (d²-a⁴-b⁴-c⁴-lambda a²b²c),
    weights(a,b,c,d)=(1,1,1,2).

The monic equation makes this free of rank two over C[[a,b,c]], with basis 1,d. Weight filtration has associated graded T=C[a,b,c,d]/(d²-a⁴-b⁴-c⁴). The smooth X=Proj T is the double plane branched over the Fermat quartic, with H the pullback of O_P²(1). In the a-chart, b=a u, c=a v, d=a² w, the equation is

    w² = 1+u⁴+v⁴+lambda a u² v.

The b- and c-charts have the same smooth exceptional equation w²=1+u⁴+v⁴. This explicitly verifies the finite model and Cartier conormal while retaining a generator of filtration degree two. The first-order deformation class a²b²c is nonzero in the Jacobian algebra C[a,b,c,d]/(a³,b³,c³,d); thus the family is not infinitesimally a coordinate change of the hypersurface. This is only a first-order nontriviality assertion, not a complete classification of its nonzero fibres.

**Crucial limit:** this is a hypersurface, hence CM, and its surface does not satisfy Delta>6H². It verifies a geometric mechanism but does not supply the desired new no-MCM example. No contradiction is sought or obtained.

### Method B: associated graded modules, cohomology, and why the shortcut fails

A different attempted proof would assign a good filtration to an assumed MCM R-module M, declare gr M to be MCM over T, and use Anghel's stronger graded obstruction. The declaration is false for an arbitrary good filtration, even on a free module.

Take R=C[[x,y]], M=R, and use the m-adic ring filtration. On M put

    G_0 M=R,    G_1 M=m,    G_2 M=m,
    G_q M=m^(q-1) for q>=2.

This is a separated good compatible filtration: m^i G_j is contained in G_(i+j), and equality m G_q=G_(q+1) holds for q>=2. Yet the nonzero degree-zero class of 1 in gr_G M is killed by both x and y, because G_1=G_2. Thus gr_G M has depth zero over C[x,y], while M is free of depth two. More precisely it is the direct sum of k in degree zero and the maximal ideal of C[x,y] shifted one degree. This does **not** prove that no better filtration exists; it proves that choosing a good filtration is not the missing descent theorem.

An alternative cohomological version keeps the actual extension E on W. The relevant inequality is the fixed-source budget

    dim H¹(W minus X, E) >= h¹(P)
       - sum_(j>0) h²(P(jH)) - sum_(j<0) h⁰(P(jH)).         (C6)

One can prove this from the Cartier sequences, positive-twist Serre vanishing, and a finite-denominator Cech argument controlling the kernel from H¹(W,E). The model in Method A supplies relative ampleness: J is the finite pullback of the relatively ample O_V(1). But this entire survival argument is already present in Chen, Section 5, including control of the fixed source rather than only one transition. Under K=4H the width window [3/2,5/2) and two-section Koszul estimate control both tails; simply reproducing them would be technical. For the pinned exponent-seven example K=5H, these particular tail estimates and constants do not apply unchanged. No rank-linear deficiency lower bound for that case is claimed here. Method A closes the nonexistence transfer without importing this unresolved quantitative step.

### The actual realization gap: a failed perturbation construction

C supplies, for every prime n>=3, surfaces with

    H²=5 n³,      Delta=n³(n²-10),      K_X numerically (n-2)H.

For n=7, h=1715 and Delta=13377>10290=6h. Method A applies to **any** ring satisfying (C3) for this surface. What is missing is an explicit nontrivial such ring.

The attempted construction was to present the section ring by weighted homogeneous equations and add strictly higher-weight terms. That does not prove preservation of (C3); syzygies generate new initial relations. Here is a prime-ideal diagnostic demonstrating the issue without making any assertion about the source surface. Start with the twisted-cubic equations

    f1=xz-y²,   f2=xw-yz,   f3=yw-z²,
    z f1-y f2+x f3=0.

Perturb only f1 to f1+w³. The same syzygy now yields z w³ in the new ideal. This polynomial is not in the original prime ideal: under (x,y,z,w)=(s³,s²t,st²,t³) it becomes s t^11, which is nonzero. Thus all three displayed initial equations stay the same while the **full initial ideal changes**. An arbitrary high-order perturbation is not a filtered deformation of the required section ring.

A large Veronese is not a free repair. Replacing H by qH changes the obstruction to

    n²-10 > 30 q².                                         (C7)

For n=7 only q=1 can work. A theorem that some sufficiently large q gives convenient generation or embedding says nothing about being below this bound. The diagnostic records all allowable integer q up to 30 for primes n<=100, but establishes no generation bound. Method A itself avoids this issue entirely by allowing higher-degree generators; the obstruction arises only in attempts to replace the actual presentation by a simpler standard-graded one.

**Remaining obligations before a substantial candidate:** compute an actual positive-weight deformation class of the obstructed source section ring modulo coordinate changes; solve its compatibility/obstruction equations to all orders with (C3) intact; establish that a resulting ring is not merely the original cone by an isomorphism forgetting the filtration. The proposition then supplies finiteness, normality, the regular finite model, and no-MCM automatically. Neither a missing descent nor the existence of this deformation has been hidden as a conclusion. This is the strongest retained track, but it remains a scoped discovery gap.

## 4. Target K: an involution-compatible algebraic division-ring construction

### Exact target and strongest source interfaces

The proposed structural extension is a countable characteristic-zero division ring D with actual centre F, finitely generated as an F-algebra, infinite-dimensional over F, algebraic element by element over F, and an involution sigma of the **first kind**: sigma(ab)=sigma(b)sigma(a), sigma²=id, sigma|_F=id. No order, positivity, norm, or topology is imposed. Ideally one would retain two algebra generators. This would add a compatibility with forms and *-algebra structures that the original existence theorem does not supply; it is not a field-extension or product reformulation.

K's main theorem already gives countability, characteristic zero, algebra generation D=F[x,y], and non-local-finiteness over the actual centre. In `thm:lifting`, the starting central field is countable, characteristic zero, and contains every root of unity; the coefficient division algebra is finite-dimensional central. The constant tuple must generate it, and **two** linear free-series directions must remain independent modulo inner directions. All old polynomial identities are retained, the prescribed series gets a monic relation, and the division degree strictly increases. The coefficient fields may be transcendental extensions, and the successive division algebras are not an embedding tower.

The full machinery matters: `prop:word-transfer` handles noncommuting leading words using a killed-pole regularization; `prop:compatible-relations` gives a common dual relation space; `thm:cyclic-compatibility` verifies cyclic sums by repeated blocks and hubs; `prop:eleven-block-correction` solves the resulting affine linear equations; division realization uses symbol and cyclic algebras; `lem:translation-two-directions` restores generation by a central Laurent translation. Countability is recovered only after retaining countably many coefficients. The final actual-centre argument uses finite descent of multiplication-table coefficients. None of these statements includes an anti-automorphism or equivariance under reversing words.

Corpus-wide scans found no second Kurosh manuscript giving that missing involutive lifting. The finite-symbol and Laurent preservation arguments were read as part of K: their hypotheses of finite central dimension and specially chosen independent central parameters are essential. They do not say arbitrary tensor products remain domains or that scalar extension preserves algebraicity of an arbitrary infinite-dimensional algebraic division ring.

### Attack 1: swap a tensor product with the opposite ring

The naive construction D tensor_F D^op has a natural factor-swap anti-involution, but it is **not a domain**. Here is a general algebraic obstruction, stronger than testing a particular quaternion example.

Choose a noncentral a in D, with minimal polynomial p over F of degree d>=2. The commutative field E=F[a] embeds in both factors, and E tensor_F E embeds linearly into D tensor_F D^op. In that subalgebra let X=a tensor 1, Y=1 tensor a. These commute and satisfy p(X)=p(Y)=0. Hence

    (X-Y) q(X,Y)=0,       q(X,Y)=(p(X)-p(Y))/(X-Y).

Both factors are nonzero: X-Y is nonzero in the tensor basis 1,a,...,a^(d-1), and q has degree at most d-1 in each variable with a nonzero coefficient of X^(d-1). Thus the tensor product already contains explicit zero divisors. Localizing it cannot turn the embedding of both these nonzero factors into an embedding in a division ring. This rejects that construction, not the target. No algebraicity claim for this tensor product is made.

### Attack 2: modify the actual colored correction and division realization

Trying to preserve first-kind involutions at every finite stage meets a specific structural obstacle. A finite central division algebra with a first-kind involution is isomorphic over its centre to its opposite, so its Brauer class has exponent dividing two. Index and exponent have the same prime divisors, so its division degree is a power of two. These facts, including proofs, are in Sridharan's lectures in collaboration with Parimala, [2-Torsion in Brauer Groups: A Theorem of Merkurjev](https://people.math.ethz.ch/~knus/sridharan/merkurjev84.pdf), Chapter I, Lemma 5.1 and Theorem 5.4 (printed pages 10–11, PDF pages 18–19). They concern finite-dimensional central algebras and are not applied to an unconstructed infinite-dimensional D. The retained filename `knus-sridharan` reflects the hosting URL, not authorship.

Every actual K lifting step has degree 11 b d. It therefore cannot carry a first-kind involution over that stage's centre. Simply asking the existing linear solver to respect such an involution is impossible at that interface.

There is a partial constructive repair to the **graph only**. Replace 11 vertices by 16 and keep offsets {1,2} for the first letter and {3,4} for the second. There are no returns of length one or two; reverse offsets are disjoint from forward offsets; the two offsets of each color differ by one, so the annihilator argument still propagates along the whole cyclic vertex set. The offset-one cycle also still supports the generation argument, and 16 is invertible in characteristic zero. These combinatorial checks pass, but they do not solve the algebra problem.

In particular, the generic cyclic factor of degree 16 with parameter a_* is not automatically exponent two. Over H_0(a_*), for the cyclic constant extension L_0/H_0 of degree 16, the a_*-valuation of a norm from L_0(a_*) is divisible by 16. Thus a_*^r cannot be such a norm for 0<r<16; the usual cyclic-algebra norm criterion gives this factor exponent 16. Replacing an odd cycle by a power-of-two cycle removes only one necessary-degree obstruction. One must redesign the division realization, and check its Brauer class, rather than assume even degree suffices.

Moreover, a word-reversing involution constrains forward and reverse arrow coefficients together. The existing proof chooses forward linear arrows independently and solves for reverse arrows at degree ell-1. Imposing transpose-style relations can introduce degree-two returns and remove the independence used in the paired-response surjectivity. No invariant affine correction space satisfying the source's full response, cyclic, generation, and two-direction contracts has been constructed.

**Remaining obligation:** an involution-compatible algebraic lifting theorem with a division realization, simultaneous control of both tangent directions, and a compatible scheduling/actual-centre argument. The graph repair alone is technical. This track is parked with a concrete algebraic obstruction, not declared impossible and not claimed as a new theorem.

## 5. Validation, provenance, and handoff

Run from the repository root:

    python frontier/experiments/i28_algebra_discovery/diagnostics.py
    python frontier/experiments/i28_algebra_discovery/verify.py

The deterministic diagnostics use only the standard library and exact integer/rational arithmetic. They verify 35,000 Weyl action identities, 15,625 cocycle identities, 441 module-filtration compatibility inequalities, 341 finite Rees-generator shift identities, 25 weighted Hilbert-function coefficients, all three weighted blowup-chart equations, the nonzero first-order Jacobian class, the twisted-cubic syzygy obstruction, nine polynomial tensor-zero-divisor identities, and four colored-graph designs. Surface and Veronese inequalities are checked for primes through 100. These are meaningful bounded diagnostics of the written constructions; they do not prove scheme regularity, all-order deformation existence, infinite-dimensional analytic estimates, or an involutive division realization. The proofs and the unresolved obligations above remain decisive.

The seal covers this report, frozen source/input bytes, exact contracts/passages, literature bytes including failed retrieval responses, scripts, and deterministic outputs. The verifier separately checks the 35 selected source Git identities against the complete tree and the read-only corpus manifest; the inventory audit hashes all 9,340 cache files without copying them. A frozen ledger is evidence of the input state. Later changes to the live shared ledger are reported separately from immutable source or dependency failures. Retrieval attempts are not silently replaced: the unavailable BOT v2 and blocked Milne URL are retained; BOT v1 and the Sridharan–Parimala lectures supply the needed references. A missing optional HTML parser interrupted one metadata-writing step after downloads completed; those bytes were retained, and recovery records mark file-mtime provenance and the unretained HTTP status honestly. Earlier search-result bodies survive, but their exact query strings were not captured; the final search round has an exact query log. No exhaustive literature or priority claim is inferred from these bounded searches.

The final integrity run passed for 109 sealed artifacts, 57 exact source theorem contracts, all 9,340 cache files, and deterministic diagnostic replay. Its machine-readable result is `../experiments/i28_algebra_discovery/verification.json`. It records live TEN-FINDINGS drift separately; the frozen input digest remains `cd2c6ffc902e7bc3a439b7bf50b44551b6df619e01effccb66dcc408f669d3b0`. This is an integrity result, not independent proof or significance approval.

**Handoff:** the complete filtered-persistence proposition is available for independent proof checking if useful. The task's stronger discovery target remains open at explicit nonconical realization and significance. None of the Ulam obstruction, tensor-zero-divisor calculation, graph variant, or Rees transfer is offered as an additional substantial finding. No acceptance-count change is requested.
