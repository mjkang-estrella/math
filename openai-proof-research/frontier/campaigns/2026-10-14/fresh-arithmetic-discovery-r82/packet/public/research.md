# Arithmetic/algebraic discovery r82 — prefreeze archive

No target was frozen and no candidate is nominated. This record assigns no mathematical gate, contribution rating or campaign count. All statements and operative proof operations of the pinned OpenAI sources at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. The work below interprets their interfaces and investigates new deductions; it does not audit their truth.

The sustained investigations concern multiplicity and symbolic powers (193/194), adjoint evaluation (038), and unequal multipoint positivity (039). Shorter operation/history screens concern 202/203, 057, 065 and 040. These were unequal investigations, not nine full literature clearances. The latest r81, r80, structural r117 and T152AC116 materials were exclusion context at the extents recorded in reading-limits.md. Accepted findings R023–R040 were read, including their operative contribution descriptions. No accepted family was selected for a renamed result.

All calculations here preceded any possible freeze. There was no freeze at any time, no change to an earlier frozen target, and no weaker replacement offered. Exact source and primary identities are in the private provenance ledgers. Public text is original research prose; source bodies remain private under their original rights.

## Multiplicity: test the actual finite-normalization reduction first

Source193's main theorem supplies strict Serre positivity for complementary-dimensional modules over every regular local ring. Its introduction already records the Kurano–Roberts symbolic-power consequence in ramified mixed characteristic. Its tangent-cone corollary also supplies the product-multiplicity inequality and the equality criterion under its explicit graded-intersection dimension at most one hypothesis. Neither was treated as a new deduction.

Source194 supplies Lech's inequality for all flat local maps. Its positive-characteristic proof has the stronger beta-zero/Dutta estimate and the prime-filtration passage. The complete arithmetic r10 rank-isolation body was read: it already constructs the supernatural root windows and derivative interpolation giving all-Betti estimates, not merely a beta-zero bound. The complete r7 checkpoint was also read: positive-dimensional exceptional intersections and the failure of generic-point local Euler counting were already explicit. These antecedents eliminate easy Betti-index and blowup-excess variants.

The concrete remaining idea tested was the symmetric symbolic intersection: for a regular local ring (R,m), primes P,Q with radical(P+Q)=m and dim(R/P)+dim(R/Q)=dim R, can one obtain P^(a) intersect Q^(b) contained in m^(a+b), for all positive a,b, in the mixed-characteristic cases not supplied by the read comparison? This is a feasibility question, not a frozen target or a claim about the full current literature.

The strongest compatible existing reduction found was read in the actual papers, not inferred from an abstract. Sean Sather-Wagstaff's [math/0104175v1](https://arxiv.org/pdf/math/0104175v1), Lemma 2.1 and Theorems 2.2–2.3, use the following dimension inequality. For a quasi-unmixed local A, analytically unramified A/P and A/Q, and radical(P+Q)=n,

    e(A) < e(A_P)+e(A_Q)

should force dim(A/P)+dim(A/Q) <= dim A. The paper proves this when A_red contains a field, or in its mixed-characteristic case where p belongs to a reductive system of parameters. Applied to A=R/(f), the inequality is precisely what excludes a symbolic witness f of order less than a+b. The exact reduction to a complete domain, including the common-minimal-prime step, was read through the end of the proof.

The regular subring in that proof is not an arbitrary Cohen subring. A finite regular local C subset A is chosen so that m_C A is a reduction of n and the residue fields agree. Thus

    rank_C A = e_C(m_C,A) = e(A).

The prime-fiber multiplicity estimate in Lemma 2.1 then forces the contracted primes to meet properly in C. Serre's dimension inequality over C finishes. This operation, including its numerical budget, must be preserved before calling the remaining mixed-characteristic step new.

The later primary [math/0207068v1](https://arxiv.org/pdf/math/0207068v1), Conjectures 1.5–1.6 and Theorem 1.9, supplies a stronger reduction than merely choosing an arbitrary regular base. Its actual proof of implication (5) to (4) selects a multiplicity-preserving finite subring which in general is a hypersurface over a complete p-ring. If r is its generic rank, then

    e(A)=r e(C),   e(A_P)<=r e(C_p),   e(A_Q)<=r e(C_q).

Consequently the strict two-prime multiplicity inequality descends to this C. But C need not be regular. The missing dimension inequality has moved to a hypersurface; it has not disappeared. The rest of Theorem 1.9's approximation proof was not read completely, so it is not independently certified here.

### A concrete budget calculation

Let p>3 be prime, V=Z_p, let t satisfy t^3=p, and put

    B=V[t],     A=V[t^2] = V[[x]]/(x^3-p^2),     x=t^2.

B is a complete DVR with uniformizer t. A is a one-dimensional complete local domain, finite free of rank three over V, with V-basis 1,t^2,t^4. In B, the valuations of the nonzero terms of

    c0+c1 t^2+c2 t^4

are respectively 3v_p(c0), 2+3v_p(c1), and 4+3v_p(c2). They are in different residue classes modulo three, so no leading cancellation between them is possible. The value semigroup of A is {0,2,3,4,...}; in particular A contains no element of B-valuation one.

The associated graded ring for n=(p,x) is F_p[P,X]/(P^2): the initial form of x^3-p^2 has degree two and is -P^2. Its degree-j piece has dimension two for every j>=1, so e(A)=2. On the other hand A/pA=F_p[x]/(x^3) has length three. Since A is one-dimensional Cohen–Macaulay, e((p),A)=3. Thus the regular coefficient subring V gives rank three, not the required multiplicity budget two; (p) is not a reduction of n.

The normalization does not repair the flat-map interface. Indeed B/A is one copy of F_p, represented by t, since pt=t^4 belongs to A. The generic rank of B over A is one, whereas B/nB=B/(t^2) has dimension two over F_p. A finite flat local A-module of rank one would have one-dimensional closed fiber. Hence A to B is not flat, and its multiplicities are e(A)=2 and e(B)=1. Source194's flat-local-map theorem cannot be inserted into this normalization map.

There is also no alternative complete coefficient DVR C between V and A, with the same residue field and A finite over C, that attains rank two. If u is a uniformizer of C, then v_B(u) divides v_B(p)=3. The possibility v_B(u)=1 is excluded by the semigroup just computed. Therefore v_B(u)=3 and p is a uniformizer of C. Completeness and the residue field F_p imply that every element of C has its p-adic digit expansion in V, so C=V. This assertion concerns exactly these coefficient subrings in this one-dimensional example; it is not a classification of arbitrary higher-dimensional alterations.

This example is a diagnostic of the chosen regular-base/normalization routes. It is not a counterexample to either symbolic containment or the two-prime dimension statement. No pair of primes violating those statements is constructed, and this calculation is not proposed as a candidate.

### Test the stronger source operations, rather than stop at the flatness objection

Source193's `ds:descent` explicitly allows a singular Noetherian finite-dimensional Z_(p)-base, connective associative coefficients with central action, and a finite surjection with a group transitive on geometric fibers. It requires neither flatness nor tame ramification. Therefore a claim that rational supported K-theory descent itself fails on the singular base would misread the source.

The numerical comparison is a separate interface. In `ds:ordinary-norm`, the proof uses a bounded finite free resolution of the finite algebra over a regular base to compute the ordinary Euler evaluation as rank times base length. It matches that to the normalized evaluation and only then invokes supported rational descent. The source asymptotic category also remembers uniform central support and negligible-rank quotients; a raw sequence of lengths is not a replacement for that contract. Source194's `thm:complex` requires a nonnegative additive length function and the explicit Koszul length identities. A signed global Euler characteristic cannot simply be substituted as that function.

These stronger contracts were tested conceptually against the hypersurface reduction. I have not constructed a numerical evaluation on the singular-base route that both has total budget e(A) and captures the two localized multiplicities in the way Lemma 2.1 needs. Merely descending a norm class, or knowing e(C)<=e(D) for a flat map, supplies no such two-prime dimension inequality. This is the exact unpaid step of this attempt. It is not a proof that no use of the full source architecture could supply it. No full symbolic-power theorem was frozen.

## Adjoint evaluation: a reduced equality divisor is not a jet certificate

The complete source038 isolation section was read. `lem:rational-support` fixes the rational supporting functional and budget; `lem:isolated-equality` constructs the isolated equality divisor S. In the final lift, the boundary coefficient at a component F of S is its log discrepancy a_F, while the relative canonical coefficient is a_F-1. Adding S gives the exact correction

    (a_F-1)-a_F+1=0.

Kawamata–Viehweg vanishing produces the restriction surjection to the reduced S, and its connected proper image at the point supplies a nonzero value. This is a very specific operative certificate. The primary comparison, Fujita's [alg-geom/9311013v1](https://arxiv.org/pdf/alg-geom/9311013v1), §1(1.6), was read through its reduced-divisor restriction argument. It already uses this vanishing-and-nonzero-value architecture. Its threefold setting is not silently extended by citation alone; the pinned source supplies its own general-dimensional operation.

The history search led to actual I136, where the sharp length-two/very-ampleness question for K_X+(n+2)L and the jet-interface obstacles were already formulated. Before any freeze, I tested the ordinary blowup route. If pi:Y to X blows up a smooth point in dimension n>=2 with exceptional E, then

    pi*(K_X+(n+2)L)-2E-K_Y = (n+2)pi*L-(n+1)E.

Vanishing with this displayed divisor nef and big would supply the first-jet evaluation. Its nefness already requires epsilon_x(L)>=(n+1)/(n+2). No uniform such hypothesis is supplied at an arbitrary point by source039's very-general, sufficiently-many-point theorem. This calculation does not deny another vanishing argument or prove failure of the adjoint statement.

Replacing S by 2S in the source038 lift also changes its exact coefficient cancellation. It does not by itself supply an arbitrary prescribed tangent direction, and a general equality divisor is not the ordinary exceptional divisor of the point blowup. One would need a new comparison preserving the required infinitesimal evaluation, the positivity budget and the minimizer's trigger. The existing minimizer is invoked by failure of generation, not by the rank defect of a length-two evaluation. No such comparison was constructed here. The previously posed full question was not refrozen or replaced by a restricted very-general statement.

## Unequal weights: the stronger prior allocation and refinement are already available

The source039 higher-dimensional manuscript gives graded reshaping, exact backwards finite jet transfer and full-density interior saturation. Its `lem:interior-saturation` counts two-sum decompositions to fill every fixed compact interior in all large degrees; `lem:simplex-interpolation` uses Chinese remainders to separate the required jets. These are stronger premises than just the equal-weight numerical headline.

Actual same-family companions were checked. The positive-characteristic manuscript's complete interpolation and positivity sections use local-parameter powers, the elongated simplex, geometric-generic rank openness, and the curve-multiplicity bound. Characteristic changes do not create a new weighted mechanism. The surface companion's complete jets and nef sections instead use injective homogeneous tests and a positive-square Riemann–Roch argument. Its conclusion covers curves with unequal multiplicities against one common exceptional coefficient; it does not turn those curve multiplicities into an arbitrary vector of exceptional coefficients. The plane Nagata companion was only catalogue navigation in this round, not a fresh proof read or complete family clearance.

More importantly, I136 and the large actual I142 body already contain much more than equal-weight application. I142 supplies arbitrary given coarse and bubble nef inputs in a normal-cone refinement, keeping total pullbacks, algebraic sections, a central-nef to nearby-nef argument via ample perturbations, and a common very-general locus. It does not assume that scalar volume alone makes the bubble nef. The primary [Roé–Ross, 0804.1662v1](https://arxiv.org/pdf/0804.1662v1), Theorem 1.6 and §3, was read at its actual weighted refinement statement and deformation proof/sketch. Normal-cone refinement itself is thus an existing compatible operation, not an unpaid bridge inferred from the absence of a matching headline.

I142 also supplies a full adaptive dyadic allocation independent of the number of occupied levels. Write V=L^n, M=max w_i, Q=sum w_i^n, and let c_P be the sum of the reciprocal intercepts of the original flag simplex. With K>=400 and epsilon>0, its precise sufficient inequality is

    F=(1+epsilon)^(n-1)/(1-K^(-n)),
    R_n=n!(2KM)^n/(1-(1+epsilon)^(-n)),
    FQ+R_n < V(1-8nKc_P M),     8Kc_P M<1.

The actual proof controls the group rounding loss by a geometric series, puts dyadic cubes into a finite hierarchy, uses compatible maximal minors on every cell, and transfers the whole simultaneous jet matrix. It is not merely an unproved scalar packing slogan. Its prescribed positive-slack result is therefore controlling history.

The prefreeze endpoint check is exact: at Q=V and M>0, F>1 and R_n>0, whereas the right-hand side is less than V, so this sufficient inequality cannot hold. Nor can its inequalities alone approach full volume while keeping M fixed: 8Kc_P M is bounded below by 3200c_P M, since K>=400. Allowing epsilon or K to depend on the shrinking volume slack does not produce one positive threshold on M from this estimate. This only limits the displayed sufficient condition, not the nefness of any actual class.

The strongest already-available refinement also cannot be invoked circularly: volume-feasible unequal bubbles must first be shown nef. Applying source038 on a blown-up variety requires an ample input there and does not create the missing weighted nef input. No mechanism closing the uniform volume-boundary step was found. No new weighted target was frozen, and no strict-slack repair or equal-tree variant is nominated.

## Additional screens and disposition

Source202's complete consequences section already includes numerical classifications and a functorial alternating-chain Grothendieck identity (`cor:functorial-awc`). The actual I104 beginning separates Galois, equivariant-bijection, complex and integral questions. Numerical or Grothendieck equality alone is not a compatible label-by-label bijection. No equivariant construction was produced; later linked I108/I110 bodies were navigation, not new proof clearance.

For source203, integral `prop:criteria` and the initial crossed-system identities in `02_inputs.tex` were read. The complete r32 screen is stronger exclusion context than an informal assertion that actions can vary: its explicit M4(O) conjugacy family becomes the same equivariant Morita class. A different equivariant-Morita invariant or rigidity argument would be required. The field and integral companions were identified, but their entire proof bodies were not reread; no general marked-action result was proposed.

For source057, the entire root-orbifold `prop:transfer` proof is already formulated for a general-dimensional smooth proper model with connected trivial-cotangent fibers and the stated codimension-one/root-lift hypotheses. It supplies differential descent, specialness transfer and the fundamental-group surjection. The earlier r12 candidate opening already has finite SNC and arbitrary root orders. This is an exclusion against literal dimension/order variants, not a fresh full audit of that candidate or of the compact/open companions.

Source065's r65 screen was read completely: fixed integral homology and group-ring cap inversion were already tested against the actual degeneration operation, and the blowup issue was not just a numerical class ambiguity. The newly retrieved source files were not fully read, so this is a historical exclusion, not a fresh primary theorem claim. Likewise the complete r48 checkpoint controls the source040 rational Tate-power and torsion-order direction; this round did not independently reread Kahn or the full Bloch source. Those branches were not frozen on a title match.

The principal new work retained here is the mixed-characteristic multiplicity-budget calculation and the precise comparison of singular categorical descent with numerical Euler comparison. It identifies a missing interface in one attempted deduction. It does not solve a full target, refute one, or certify a contribution. No finite mathematical test was used as a gate. No target is nominated. Parent integration, independent review decisions and campaign counts are untouched.
