# Integrated feasibility construction at the full exploratory scope

No theorem in 00-scope.md is frozen or proved here. The following calculations distinguish deductions from supplied inputs and exact obligations still to be established.

## 1. What rational connectedness actually supplies

Write d=2n+1. Buczynski–Peternell Proposition 2.2 gives pi1(X)=0, Hq(X,O)=0 for q>0, X Moishezon, and Pic(X)=Z because b2=1. Its cited foundational Campana/Kollár arguments were not recursively re-proved in this round. Choose the generator A with a positive power big. The contact determinant identity is valid holomorphically and gives L=A^k and -K_X=L^(n+1).

A very free rational curve g exists in this class by the same primary proposition and its proof. We can move it into the open where a big linear system is birational. The moving curve has positive degree against that big line: its image under the corresponding meromorphic map is nonconstant and a general hyperplane meets it positively after resolving the map. Thus deg(g*A)>0. Since g*T_X is ample, deg(g*(-K_X))>0, hence k>0. Consequently L is big. This does NOT prove L nef, ample, globally generated, or of positive degree on every curve.

For any such g, put e=deg(g*L). Its splitting has positive degrees a_i and

    sum a_i=(n+1)e >= 2n+1.

Thus e>=2. Move within the full very free Hom neighborhood. The restriction to the length-two infinitesimal point is surjective because H1(g*T_X(-2p))=0. Hence value–velocity evaluation is submersive, and some nearby curve has theta(g'(p)) nonzero. Its contact differential is a nonzero section

    eta_g in H0(P1, g*L tensor omega_P1)=H0(P1,O(e-2)).

When e=2 this is nowhere zero and the degree count forces the source splitting O(2)+O(1)^(2n). When e>2 it has an effective zero divisor of degree e-2. Rational connectedness has supplied e>=2, not e=2 or an unsplit degree-one family.

## 2. A proper family is available without pretending X projective

Take a projective modification q:V->X, with V smooth projective. Its exceptional image in the smooth target has codimension at least two. A general deformation of g avoids that image: smooth evaluation from a full free-map neighborhood makes the incidence with this codimension-two set have dimension at most dim(Hom)-1 after including one source parameter, and projection along P1 is proper. Choose such a g and lift it to V. The map q is an isomorphism around its image, so the lift is still very free.

Fix the numerical class of this lift. Normalize the reduced component through it in the projective-target unmarked stable-map stack of V. Its universal curve C and its relative square D are proper. The source's normal-products argument applies on normal charts because the entire generic source is smooth geometrically integral. Composing the evaluation with q gives a proper dominating map from the coarse square to X×X, and the full nearby parametrized family on X lifts because its images avoid the exceptional image.

This constructs the proper parameter space, rather than merely assuming it. One can retain V-stable sources; after composition some components may be constant in X. A stable-map compactification directly for X is not needed for this step. The target X and pulled-back bundles are used analytically; no unproved projective embedding of X is inserted.

On the smooth-source open, both source vector formulas and their scalar value are defined for every contact degree e. The question is extension to this compactification and descent; properness alone does not prove either. A rational section of a bundle can have poles along the boundary.

## 3. Why higher degree cannot simply replace the conic

There is a concrete fixed-end calculation even on the PAID model P3. Let V=C4 have symplectic basis e1,e2,f1,f2 with sigma(ei,fj)=delta_ij. Put v0=e1, v1=f1, and u=f1+e2. For a!=0 define

    v_a(t)=(1-t)v0+t v1+a t(t-1)u,
    h_a(t)=[v_a(t)] in P(V).

Homogenizing gives a basepoint-free degree-two map P1->P3. At infinity the value is [u]; at t=0,1 it is [v0],[v1], independent of a. The three vectors are independent, so this is a smooth plane conic. Pullback of T_P3 is O(3)+O(3)+O(2): the Euler sequence on the plane conic gives T_P2|=O(3)+O(3), and its extension by the normal O(2) splits since H1(O(1))=0. Thus these maps are very free and have contact degree FOUR, since L=O(2).

Using the fixed endpoint lifts v0,v1 to trivialize their contact lines,

    theta(h_a'(0)) = sigma(v0,v1-v0-a u) = 1-a,
    theta(h_a'(1)) = sigma(v1,v1-v0+a u) = 1.

Therefore the source scalar formula at (0,1) is 1-a. It varies with a while both endpoints stay fixed. If this scalar extended to a proper family over X×X containing the full Hom neighborhood, its restriction to a proper irreducible fiber component containing this parameter curve would be a constant function, a contradiction. Equivalently, its proper image inside the line bundle would have finite fibers, while this explicit parameter curve produces infinitely many values in one fiber.

This is not a counterexample to any source statement: its degree is four, while the operative source compactification has degree two. It proves that replacing the missing conic by an arbitrary very free curve and repeating the same tensor formula cannot be the missing bridge. A selected smaller family might behave differently, but must be constructed with the requisite full value–velocity directions; it is not supplied by this calculation.

## 4. The scalar-trace alternative, developed rather than dismissed

Suppose a proper integral Y over X×X has a REGULAR scalar contact value xi in p*(L box L). Properness makes its image S0 in Tot(L box L) finite over X×X. This is a local analytic statement too: a proper analytic subspace in a line bundle has finite fibers, since a compact analytic subset of C is finite. Normalize to q:S->X×X and write delta=degree(q).

Locally trivialize M=L box L and let zeta denote the scalar coordinate on S. It is integral over O_(X×X). The field trace of zeta is integral and belongs to the base meromorphic function field; normality of the smooth base makes it holomorphic. Changes of frame multiply it by the appropriate base unit. Thus

    B_tr = (1/delta) Tr_(C(S)/C(X×X))(zeta)

defines a GLOBAL section of M. No unramifiedness, sheet splitting, or simple connectivity is required for this trace construction. An involution over exchange of factors makes B_tr symmetric by functoriality of trace.

There is an exact sufficient jet condition. In local coordinates near a diagonal point let b0(x,y) be any holomorphic representative with diagonal order two and symbol theta^2. If

    zeta-q*b0 belongs to I_Delta^3 · q_*O_S

on every such neighborhood (as an element of the finite module), then trace gives

    B_tr-b0 in I_Delta^3,

because trace is O-linear and Tr(1)=delta. This entails the required constant/linear vanishing and quadratic symbol. It is not enough to know this relation on one germ of one sheet. For example, the split finite algebra A⊕A with scalar coordinates b0 and c has normalized trace (b0+c)/2; an uncontrolled second sheet changes the constant and quadratic terms. This is an algebraic interface control, not a purported geometric counterexample.

The full source identity on the chosen conic controls the coalescing-points germ. It does not by itself control every sheet over the diagonal, where distinct source points can have the same image or the source can break. To make trace a replacement for the source's vector-lift descent, one must prove scalar regularity AND the displayed all-sheet ideal membership. Neither is automatic from a normal compactification. Using a trace alone would conceal this second obligation.

## 5. Exact end of the construction if the missing tensor is obtained

A symmetric global B with [B]_2=theta^2 gives an immersion beta:X->P(H0(L)) by the STIPULATED compact-complex symmetric-jet criterion. Its construction also gives beta*O(1)=L. Pullback of Fubini–Study along a holomorphic immersion is a strictly positive Hermitian curvature form on L. Hence L is positive, Kodaira makes X projective, and -K_X=L^(n+1) is ample. The source classification now identifies the given F and L. This closes the downstream interface without assuming in advance that X is Kahler or that the immersion is globally injective.

The missing operation is therefore genuinely before the global contact tensor. Pointwise adjoint classification cannot be invoked there. No metric statement follows for an initially arbitrary class C input: after projectivity and Fano classification one has the source KE existence, but an initially chosen real structure or curve family is not automatically its twistor fibration.
