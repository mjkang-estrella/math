# i02 Hodge cylinders, R2: a cubic tower and two explicit incidence families

Date: 2026-10-08. **Outcome: no nonzero target cylinder, no new Mumford Hodge case, and no substantial new theorem meeting the research objective.** This round constructs and computes two actual families of curves beyond the previously rejected CM/product-support/normal-rational-ample-divisor proposals. Both have zero target projection, for different explicit reasons. A degree-three map to a known elliptic-product quotient explains the extra (3,0) pair but does not produce the missing component.

The independent audit is [i02-hodge-construction-r2.md](../reviews/i02-hodge-construction-r2.md). All writes are confined to the two assigned reports and `frontier/{sources,experiments}/i02_hodge_r2/`. No agents, staging, commits or shared-index changes were made. The immutable OpenAI pin is **fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb**; its accepted theorems were not re-audited.

## 1. Target and prior-art limits

Fix t∈C\{0,1}, write f(x)=x(x−1)(x−t), and put

    X: y^9=f(x),
    N={(a,b,c)∈(Z/9)^3 : a+4b+7c=0},
    Y0=X^3/N,         Y=Y0/C3.

The normal finite quotient Y0 has affine equation z^9=f1 f2^4 f3^7. The block UY⊂H^3(Y) has dimension sixteen and types (2,1),(1,2), eight of each. A projective resolution r:Ytilde→Y contains r*UY as a nondegenerate sub-Hodge structure. The desired construction here is an actual Γ∈CH^2(T×Ytilde), with T a smooth projective curve, for which

    pr_(r*UY) Γ_* : H^1(T)(−1) → H^3(Ytilde)

is nonzero. A curve-family correspondence has this degree because dim T=1. Restricting a family to a suitable curve in a higher-dimensional parameter space would give the same test.

The relevant MathDB target remains [Hodge conjecture #315851](https://mathdb.com/p/315851), recorded as **landmark** in the retained geometry scout's API evidence. No new significance score or current-status claim is inferred here. The actual Mumford target is the repaired partner block U⊂H^3(B), U(1)≅H^1(A)⊗K. Our explicit B9 has not been compared to B with the required rational representation, central character, corestriction, polarization and period data. A successful UY cylinder would therefore still need that comparison before it could solve the stated actual-Mumford case.

Primary prior art was checked before attempting the cycles. Moonen–Oort, Example 5.6, already describes the degree-nine curve, its CM elliptic quotient and six-dimensional new factor ([PDF](https://webspace.science.uu.nl/~oort0109/ModuliHandbook-moonenoort.pdf)). The retained BHPS and H8 reviews record the unproved higher tensor correspondence and existing Mumford/partner/KS reductions. Arapura's final [v2 manuscript](https://arxiv.org/pdf/1201.6403v2), Theorems 3.2 and 3.4, does not apply: its numerical condition is 0≥50 for Y0, as computed in the audit. Cynk–Hulek, [*Construction and examples of higher-dimensional modular Calabi–Yau manifolds*, v3](https://arxiv.org/pdf/math/0509424v3), Theorem 3.3, supplies the exact elliptic-product construction used for comparison below. The source URLs and hashes are retained in [downloads.json](../sources/i02_hodge_r2/downloads.json) and [reused_inputs.json](../sources/i02_hodge_r2/reused_inputs.json).

These searches establish concrete overlaps and scope restrictions. Neither these elementary incidence constructions nor their obstructions are claimed new to the literature.

## 2. The actual cubic tower and the extra holomorphic pair

Let E be the normalization of u^3=f(x). It is a genus-one curve with an order-three automorphism and CM by Q(ζ3). The map X→E is (x,y)↦(x,y^3). Let

    H={(a,b,c)∈(Z/3)^3 : a+b+c=0},
    W=E^3/H.

Then W has the normalized affine equation

    w^3=f1 f2 f3,       w=u1 u2 u3.

There is an explicit map

    Y0 → W,       w=z^3/(f2 f3^2),                 (2.1)

since w^3=z^9/(f2^3 f3^6)=f1 f2 f3. This is a finite quotient morphism globally, not merely a formula valid on the displayed chart. Indeed, put

    M={(a,b,c)∈(Z/9)^3 : a+b+c=0 mod 3}.

Then N⊂M, |M|=243, M/N has order three, and X^3/M=E^3/H. Its generator on Y0 is τ:z↦ζ3 z, induced by δ1^3. Thus (2.1) has degree three.

The cyclic permutation normalizes both N and M and commutes with τ modulo N. It follows that

    Y → Z:=W/C3                                        (2.2)

is also a degree-three quotient by τ. Do not replace τ by δ1: the full residual order-nine phase on Y0 does not descend to Y.

On W, H-invariance leaves exactly H^1(E)_(χ)^(⊗3) and its conjugate in degree three. They have types (3,0),(0,3), one dimension each. The cyclic permutation fixes both. Pullback from Z therefore gives exactly the old two-dimensional block on Y; the remaining sixteen-dimensional block is

    UY = ker(1+τ*+τ*²) in H^3(Y).

The old part is isotrivial as a complex Hodge structure, since E has constant CM isomorphism type. This proves the promised explanation of the extra (3,0) pair without assigning a guessed threefold name to Y.

Cynk–Hulek Theorem 3.3 gives a Calabi–Yau smooth model of W with b3=2. Its theorem is about W; it is not an assertion that Y or Z has that smooth model. In fact Y cannot have a **crepant** resolution with trivial canonical class: X^3→Y has no divisorial stabilizers, so it is étale in codimension one and pulls K_Y back to the ample K_(X^3). Equivalently the normalized cover formula gives

    K_Y0 = π* O(4/3,4/3,4/3),

because each coordinate has three order-nine branch points and one order-three branch point. The permutation quotient also has no divisorial ramification. Hence K_Y is ample as a Q-Cartier divisor. This does not compute the Kodaira dimension of an arbitrary noncrepant resolution; it does prevent inferring a Calabi–Yau model from h30=1 alone.

An immediate cycle test from (2.2) is useful: total inverse images of cycles or families on Z are τ-invariant, hence their UY-projection is zero. Components of a split inverse image would require a separate computation. We do not rule those out by this observation. Likewise, exceptional ruled surfaces on resolutions can supply new H^3 classes, but their r_* projection to the old quotient block is zero. The known W construction has no hidden level-one part that can simply be pulled back to furnish UY.

## 3. Construction I: a genus-four parameter curve and genus-55 fibers

Choose four distinct nonzero complex numbers λ1,…,λ4 and let

    P(s)=∏_(i=1)^4(s−λi).

Let T3 be the smooth normalization of

    v^3=s P(s)^7.                                      (3.1)

Its branch points are 0, the four λi, and infinity. Their exponents modulo three are all one, so Riemann–Hurwitz gives genus four; dim H^1(T3)=8. This family is not confined to CM parameter curves: the six-point cyclic-cover family has varying moduli. Very general members are non-CM, by Torelli and countability of CM principally polarized abelian varieties. No particular numerical choice of λi is asserted to be non-CM.

On T3×Y0 take the closure of the incidence equations

    f1=s f2,        f3=P(s) f2,        z^3=v f2^4.        (3.2)

Their compatibility is exact:

    z^9=v^3 f2^12=s P(s)^7 f2^12=f1 f2^4 f3^7.

For fixed (s,v) in a dense open subset of T3, f2 is a free curve coordinate and the other equations are finite over it. Thus (3.2) is an actual family of one-dimensional algebraic cycles, not just a parameter-count proposal. Its swept divisor on Y0 satisfies

    f3 f2^3=∏_(i=1)^4(f1−λi f2).

Normalization/resolution of the family and closure after passing to Ytilde give Γ3∈CH^2(T3×Ytilde). Vertical or exceptional choices at the finitely many bad parameter values do not affect its projected rational H^1 map.

For additional geometric verification, over an algebraically closed generic parameter field choose κ^3=v and set r=z/(κ f2). Then f2=r^3 and z=κ r^4. A fiber of (3.2) is the fiber product over P1_r of

    f(x1)=s r^3,       f(x2)=r^3,       f(x3)=P(s) r^3.

Each is a connected degree-three genus-one cover. For generic s their branch sets are disjoint: the nonzero critical values of f, scaled by 1/s, 1, 1/P(s), coincide only at finitely many s. Their Galois closures are therefore linearly disjoint, since a common subcover would be everywhere unramified over P1. The generic fiber is geometrically connected of degree 27. Its total ramification degree is 3·6·9=162, so 2g−2=−54+162 and **g=55**. This also precludes a generic extra parameter cover obtained simply by separating components of these displayed fibers.

### Exact projection computation

The residual τ fixes s, v, x1, x2, x3 and sends z to ζ3z. Every equation in (3.2), including z^3=v f2^4, is τ-invariant. Hence

    (id_T3×τ)_*Γ3 = Γ3

at the quotient-cycle level. The induced cylinder map lands in τ-invariants. Applying e=1−(1+τ+τ²)/3 gives

    pr_(r*UY)(Γ3)_* = 0.                              (3.3)

On Y0 the same statement kills every primitive order-nine character before taking C3-invariants. After any resolution the orthogonal projection is still zero by the degree-one trace/pairing argument in the audit.

This is a new irregular parameter curve outside the four-branch exclusion, and the fibers are not a proposed fixed product of the old cover curves. Its failure is the **wrong residual character of the actual incidence map**. Non-CM parameter cohomology alone does not fix that.

## 4. Construction II: retain primitive order-nine characters

To remove the first obstruction, use the smooth normalization T9 of

    v^9=P(s)^7/s^4.                                   (4.1)

The branch exponents modulo nine are (5,7,7,7,7,3), at 0, the four roots, and infinity. Thus

    2g(T9)−2=−18+5·8+6=28,       g(T9)=15.

Each primitive order-nine eigenspace of H^1(T9) now has rank four. In particular τ can act nontrivially on a candidate weight-one source. The previous argument that the parameter action factors trivially through τ no longer applies.

The corresponding incidence equations on T9×Y0 are

    f1^2=s f2,         f3=P(s),         z=v f1.         (4.2)

They are compatible because

    f1 f2^4 f3^7=f1^9 P(s)^7/s^4=(v f1)^9.

Here τ acts on v by multiplication by ζ3. These are genuine equivariant families with the desired nontrivial residual characters available. We next compute the cycle itself, including the finite base change separating the x3 choices.

### A concrete lift and its full cycle class

Take any smooth projective normalization S of a component dominating T9 of the finite cover

    a^9=s,      b^9=P(s),      b^7=v a^4,      f(x3)=P(s).

The conditions are consistent: b=(v a^4)^4/P(s)^3, since 7·4−9·3=1. The cover is nonempty over the generic point. It gives a morphism h:S→X, q↦(x3(q),b(q)), and g(S)≥15 by Riemann–Hurwitz.

On S×X1×X2 form the zero divisor R of the rational function

    y1^2−a(q)y2.

In S×X1×X2×X3 define the codimension-two cycle

    Γhat9 = R · [x3,y3 = h(q)].                       (4.3)

This is an actual family of curves. Its image under X^3→Y0 satisfies (4.2), because y2=y1^2/a gives

    f2=f1^2/s,
    z=y1 y2^4 b^7=y1^9 b^7/a^4=f1 v.

Generic fibers of R over S are also geometrically connected. Over u=y1 they are the fiber product of f(x1)=u^9 and f(x2)=u^18/a^9. These connected degree-three covers have genera 7 and 16, and generically disjoint finite branch sets because a varies. The same Galois-closure argument gives degree nine and ramification 3·18+3·36=162, hence genus **73** for this lifted generic fiber. The genus of its finite quotient image is not asserted to be 73.

Let P_X be the pole divisor of y on X, and A∞ the pole divisor of a on S. As a divisor class on S×X1×X2,

    [R] = pr_S*[A∞] + 2 pr_1*[P_X] + pr_2*[P_X].      (4.4)

Indeed the poles of y1^2−a y2 have exactly these generic orders along the three types of polar divisors; intersections of polar divisors have codimension two and add no divisor terms. Its zero divisor is linearly equivalent to its pole divisor. Thus R has **no H^1(X1)⊗H^1(X2) component**, or any other mixed H^1 component, despite the complicated equations of its fibers.

To contribute to

    H^1(S) ⊗ H^1(X1) ⊗ H^1(X2) ⊗ H^1(X3)

in [Γhat9], the graph class in (4.3) would have to contribute its H^1(S)⊗H^1(X3) term and R its H^1(X1)⊗H^1(X2) term. The latter is zero by (4.4). All remaining Künneth-degree combinations are different. Consequently

    ([Γhat9])_(1,1,1,1)=0.                           (4.5)

Since the pullback of UY is contained entirely in the triple-H^1 component of H^3(X^3), the projection formula for the finite quotient proves that the pushed cylinder Γ9 on Y, and its lift to a resolution, satisfy

    pr_(r*UY)(Γ9)_* = 0.                             (4.6)

This vanishing is valid for the displayed total incidence family without assumptions about End(B9), generic Mumford groups or CM. The generic connectedness check also rules out salvaging these very fibers by an unrecorded choice among generic components.

The second construction therefore removes the first character obstruction and still fails. The exact failure is the decomposable divisor class (4.4). It is not a deduction from the old cover-product domination lemma or the normal-rational-ample-divisor lemma.

## 5. What the computations establish and what is still missing

The independent [check.py](../experiments/i02_hodge_r2/check.py) and [output](../experiments/i02_hodge_r2/check.out) verify the differential basis, quotient tensor orbits, the groups N⊂M, the residual projector dimensions, Arapura's 0-versus-50 inequality, both parameter-curve genera and eigenspace ranks, the tower and incidence exponent identities, and the absence of degree (1,1,1,1) in (4.3)–(4.4). The proof of cycle-class vanishing is (3.3) and (4.4)–(4.6), not a numerical rank guess. The displayed generic-fiber genera use the explicitly stated branch-disjointness condition, not all degenerate parameters.

The useful positive information is concrete but below the success threshold: a finite cubic tower identifies the old block, and actual six-branch parameter curves with additional irregularity support explicit families whose target components can be computed. Neither family supplies a nonzero component. No accepted theorem is being used to promote a Hodge projector or an abstract intermediate Jacobian to a cycle.

The remaining geometric gap is now specific: construct a family whose nontrivial τ-character survives **and** whose incidence class has nonzero triple-H^1 projection. For constructions with one coordinate fixed over the parameter curve as in §4, that requires a nonzero mixed divisor/correspondence class on the other two factors; the displayed meromorphic-function pencil has none. A family allowing all three coordinates to vary without this separation, a genuinely new irregular singular support, or a nontrivial component correspondence over the cubic tower would need its own equations and class calculation. This report has neither constructed nor ruled out those alternatives.

Independently, even a nonzero UY cycle would not identify B9 with the repaired B. The arithmetic and Hodge comparison, including the rational eight-dimensional descent and specified period, remains unproved. No BHPS tensor conjecture was assumed. Thus there is **no new solved non-CM Mumford case or substantial new high-importance theorem to integrate from this round**; retain it as an audited construction failure with reproducible equations and precise scope.
