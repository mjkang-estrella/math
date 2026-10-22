# r193 — stationary contraction data and the positive-realization interface

PREFREEZE research derivations. No theorem is frozen or nominated. All operative Source317 proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. All source includes and the core primary proof operations were read before this document. Two later checks are disclosed: Ara–Maltsiniotis 2014 physical pages 33–36 (the path/refinement antecedent) and Ara–Maltsiniotis 2015 physical pages 17–18, 22–27, 30–34, 56–67 (positive contractions and their full table transport) were read after the initial DERIVATIONS version, before this final revision. Neither changed a frozen statement; there is none. The complementary r34 history read was later than RESEARCH-NOTES and the first chain calculation, but before this document; there was no frozen statement to change.

## 1. The operation investigated and its exact distinction from the source

Let n belong to {1,2,...,ω}. Write U_n(E)=c_n N_ord(E). Let i:A→E be the inclusion of a full downward-closed subposet, with right adjoint retraction r:E→A. Thus r i=id and r(e)≤e. For ANY small strict n-category X and ANY strict a:U_n(A)→X, set

    Y=X ⊔_{U_n(A)} U_n(E),  j:X→Y,  v:U_n(E)→Y.

There is already a specified strict retraction

    p_r:Y→X,   p_r j=id,   p_r v=a U_n(r).                 (1)

This follows from the pushout universal property; it is not a new theorem. Source thm:couniversal already proves j is a Street weak equivalence, without finiteness, freeness, injectivity of a, or cofibrancy of X.

The stronger data investigated here are stationary strict RIGHT Gray cylinders connecting id to j p_r, by a finite zigzag on each finite template, with natural extension in a and compatible data on finite retraction-stable pieces for a general small E. Each edge would be an actual strict map Y⊗D1→Y, and would equal jπ_X on X⊗D1. A zigzag's intermediate maps must be strict endofunctors fixing X. Equivalently, it is enough to provide such data on U_n(E), under U_n(A), and apply the source's pushout-cylinder lemma. A signed linear homotopy of nerves, an abstract topological deformation retract, or a pointwise selection of cells is not this output. No assertion that the stronger output exists has been frozen.

For a finite template the question includes every finite retract-sieve pair, all n including ω, and every attaching target. For arbitrary small E the desired finite-piece data must really agree or carry specified positive higher coherence, rather than merely give unrelated weak equivalences. This is a direction for the stipulated family, not a change to any old frozen target. Nothing here claims a weak-category, monoidal, other-nerve, other-Ex, or coherator extension.

What can actually be constructed is considerably stronger than a named homology-vanishing gap: an explicit relative chain contraction with recursive overlap corrections; its lift for the prescribed p_r; integral higher compatibility fillers; a finite perturbation formula contracting the simplicial replacement over all finite pieces; and a precise obstruction to a single naive positive cylinder. These are retained below, not substituted as a nominee.

## 2. The source leaf, including the signs

Fix n. Put S=N_nY and T=N_nX. Source cor:attachment-covers makes j a full sieve inclusion, so T is a simplicial subset of S. Let C(S,T) be the normalized integral chain complex, in nonnegative degrees, with its basis the nondegenerate simplices of S not in T. Differential in degree zero is zero. All chains have finite support even when X is infinite.

If E\A has greatest element x, let t=r(x). The source constructs k,g:E→E fixing A, with k(e)=t and g(e)=x on the new elements. Its right prisms and pushout-cylinder lemma give

    id_Y → G ← K,       K=j p_k,

where p_k is generally different from (1). They are stationary on X. Applying the source Alexander–Whitney cylinder-to-nerve map gives two simplicial homotopies.

For a simplicial homotopy H:S×Δ[1]→S from F to G, its normalized prism operator on a q-simplex σ is

    D_H(σ)=Σ_{i=0}^q (-1)^i H(s_iσ, θ_i),                 (2)

where θ_i:[q+1]→[1] is zero through i and one thereafter. Degenerate resulting simplices mean zero. Cancelling the internal prism faces leaves

    dD_H+D_Hd=G_*−F_*.

One can check the endpoint sign in degree zero: the edge H(s_0v,01) has boundary G(v)−F(v). Faces that delete the repeated vertex cancel between successive i; all other faces form D_Hd with the displayed alternating sign. The formula descends through degeneracies by the simplicial identities. A stationary homotopy gives zero normalized prism on T, since every such image factors through the q-simplex σ along a degeneracy.

Let D_0 correspond to id→G and D_1 to K→G. On relative chains set

    h=D_1−D_0.                                           (3)

Then dh+hd=id−K_*=id on C(S,T), because K factors through X. Each input basis simplex has image with ℓ1 norm at most 2(q+1). Neither positivity of (3) nor equality p_k=p_r is asserted. Both local cylinders, and hence (3), are natural in maps of attaching targets under U_n(A). The base case E=A has zero relative complex.

## 3. Explicit overlap correction for two full sieve pieces

This is an elementary chain construction; the entire identity is given to avoid using a gluing theorem as an unexplained filler.

Suppose S=S_1∪S_2, T⊂S_1∩S_2, and let

    C=C(S,T), B=C(S_1,T)⊕C(S_2,T), A_0=C(S_1∩S_2,T).

There is a degreewise split exact sequence of chain complexes

    0 → A_0 --i--> B --q--> C → 0,
    i(z)=(z,−z),             q(b_1,b_2)=b_1+b_2.          (4)

Choose a graded section s of q by assigning each basis simplex to S_1 whenever possible, and to S_2 otherwise. Define t:B→A_0 as minus the S_2 coefficient of each intersection simplex and zero on all other basis elements. Then

    qs=id, ti=id, ts=0,
    i t+s q=id_B.

The failure of s to be a chain map has a precise overlap value

    α=t(d_Bs−s d_C)=t d_Bs,
    d_Bs−s d_C=i α,
    d_A α+α d_C=0.                                      (5)

The first equality uses ts=0. The second holds since q annihilates its left side and i t is identity on ker q. Applying d again and using injectivity of i proves the last equality.

Assume contractions h_A of A_0 and h_B=h_1⊕h_2 of B have already been supplied. Correct the section and define

    s'=s−i h_A α,
    h_C=q h_B s'.                                       (6)

These formulas are finite sums on every finite chain. They satisfy q s'=id and

    d_B s'−s'd_C
      =i(α−d_A h_A α+h_A αd_C)
      =i h_A(d_A α+αd_C)=0.

Therefore

    d_C h_C+h_C d_C
      =q(d_B h_B+h_B d_B)s'=q s'=id_C.                 (7)

There is no assumption that the contractions on S_1 and S_2 agree on the intersection. The term −i h_A α is exactly the correction for that disagreement at chain level. The correction is signed; this is crucial later.

## 4. Apply the correction to actual higher-category attachments

For finite E, induct on m=|E\A|. Fix an order on its new elements solely to select the first two maximal elements when required. If the new part has a greatest element, use (3). Otherwise choose distinct maximal new x_1,x_2 and set

    E_1=E\{x_1}, E_2=E\{x_2}, E_12=E\{x_1,x_2}.

Each is a sieve containing A, and r restricts to it. The actual source labelled-pushout operation identifies

    Y_i=X⊔_{U_n(A)}U_n(E_i)

as full sieves of Y, with full intersection Y_12. These are identities AFTER the arbitrary attachment, not assertions that N preserves arbitrary pushouts. The source nerve-cover lemma gives S=S_1∪S_2 and identifies their intersection. Thus (4) applies to their actual normalized nerves. The inductive contractions in all three smaller templates give (6).

This defines h_{E,A,a,n} in every chain degree, without any bound on X, its cells, or its nerve dimension. The only finite recursion parameter is m. Every branch strictly decreases m. No equality between N_ord(E) and N_nU_n(E) is used; in fact that equality is false already for a 2-simplex in dimension two.

The construction is natural in arbitrary strict f:X→X' under U_n(A), for a fixed ordered pair (E,A). To check the only nonformal part, observe that Y→Y' fixes the distinct new objects and sends old objects to old objects. A nerve simplex belongs to S_i exactly when every one of its new vertices belongs to E_i. Its piece membership is therefore unchanged by f, unless its normalized image is zero by degeneracy; in that case both sections give zero. Nondegenerate new vertices cannot disappear into X'. Thus the graded sections s and projections t commute with the induced normalized-chain maps. The local prisms are natural by the source, and (5)–(6) then prove naturality inductively. Identifications of old objects, arrows, or higher cells are allowed.

Here is an explicit uniform chain-norm bound, proved for these operators rather than imported from presentability. Set B_0(q)=0 for q≥0, B_m(−1)=0, B_1(q)=2(q+1), and for m≥2 put

    B_m(q)=max{2(q+1),
       B_{m−1}(q)[1+2(q+1)B_{m−2}(q−1)]}.               (8)

These functions are nondecreasing in m. They bound ||h_q||_1 for every finite template with m new objects, every n and every X. At a leaf use (3). In the cover step, ||s||≤1, ||i||≤2, ||q||≤1 and ||α_q||≤q+1, since α=t d_Bs and the normalized boundary has at most q+1 faces. Consequently

    ||s'_q||≤1+2(q+1)B_{m−2}(q−1),

and ||h_B,q||≤B_{m−1}(q), which proves (8). For q=0, α=0. These are ℓ1 bounds on SIGNED NERVE CHAINS, not bounds on numbers of cells of a categorical pushout or on lengths of strict homotopy zigzags.

## 5. Recover the prescribed retraction, not the leaf's chosen retraction

Let P=(N_np_r)_*:C(S)→C(T) and J=(N_nj)_*. Then PJ=id. Write π:C(S)→C(S,T) for the quotient. There is a canonical chain section of π onto ker P,

    ℓ([b])=b−JPb.                                       (9)

It is well-defined because replacing b by b+Jt changes the right side by zero. It satisfies πℓ=id, ℓπ=id−JP, Pℓ=0. Thus

    H=ℓ h π

satisfies

    dH+Hd=id−JP,  HJ=0,  PH=0,  ||H_q||≤2B_m(q).        (10)

The p_k appearing at different leaves have disappeared from the endpoints. Formula (10) is for the actual specified p_r in (1). It remains natural in X. No positive-realization conclusion follows.

If square-zero side conditions are useful, on the relative complex replace h by

    h^♭=h d h.

Since dh+hd=id, both dh and hd are idempotent and d h² d=0. Therefore d h^♭+h^♭d=id and (h^♭)²=h(d h² d)h=0. Its norm is at most (q+2)B_m(q)^2 in degree q. Transport it by (9) to obtain the corresponding square-zero version of (10).

## 6. Higher signed compatibility is constructible

Different finite-template orders need not produce the same h. This need not be left as an unnamed coherence gap at the chain level.

Suppose F:C→D is a chain map between two relative complexes already contracted by h_C,h_D. Such maps arise from maps of retract-sieve diagrams compatible with r and the attaching functors; their normalized nerves induce F. The degree-one defect is

    δ_F=h_DF−Fh_C,      dδ_F+δ_Fd=0.

The degree-two operator

    T_F=h_Dδ_F

satisfies

    dT_F−T_Fd=δ_F.                                      (11)

Indeed, for a homogeneous operator z of degree k, write ∂z=dz−(−1)^k z d. Composition with h_D obeys

    ∂(h_D z)=z−h_D∂z.                                   (12)

This follows directly from dh_D+h_Dd=id. It proves (11) and also fills every higher closed compatibility defect. In the square-zero normalization, T_F=−h_DFh_C.

For composable F:C→D and G:D→E,

    δ_GF=δ_G F+Gδ_F,
    Ω=T_GF−T_G F−G T_F

has degree two and ∂Ω=0. Thus S=h_EΩ has degree three with ∂S=Ω. In the square-zero normalization this is the concrete formula

    S=h_E G h_D F h_C.                                  (13)

The same induction applies to the alternating face defects for longer strings: ∂ of a defect vanishes by the previously established face identities and ∂²=0; (12) supplies its filler. Every term on a finite input is finite. This is integral homotopy-coherent data, not a positive globular composition. No model structure on enriched categories is being invoked.

## 7. General small posets: a finite perturbation formula, with the colimit issue retained

Put q=ir:E→E. Let F range over finite full subsets stable under q and set A_F=A∩F. Any finite subset T is contained in T∪q(T), so this is a filtered indexing poset. Source thm:couniversal and lem:filtered give

    Y_F=X⊔_{U_n(A_F)}U_n(F),
    Y=colim_F Y_F,       N_nY=colim_F N_nY_F.             (14)

Transition maps need NOT be monomorphisms. The fixed X really remains fixed. Source Appendix A's guarded presentations show why finite equations and definedness witnesses, including newly created compositions, occur at a finite stage; a claim of injective passage would lose this feature.

Let C_F=C(N_nY_F,N_nX). Normalized chains commute with these filtered colimits: the free-chain construction commutes with colimits degreewise and quotienting by degenerate chains is a colimit construction. Hence C=colim C_F. Given a finite relative cycle in C, choose representatives in a finite stage. Its finitely many boundary equalities hold at some larger common stage F'. Then h_F' fills the represented cycle. This is an explicit finite-witness method once representatives and equality witnesses have been supplied, not a computable uniform bound on the size of F' from chain degree alone.

One can do more than assert individual fillings. Form the normalized simplicial replacement of the diagram F↦C_F. In bidegree (p,q), take the direct sum of (C_F0)_q over strict chains F0⊊...⊊Fp. The horizontal differential δ is the alternating sum of deletions, with the first deletion applying C_F0→C_F1. The vertical differential is d_0=(−1)^p d. Thus

    d_0²=δ²=0,       d_0δ+δd_0=0.

Let h_0=(−1)^p h_F0 on each summand. Then d_0h_0+h_0d_0=id. The operator δh_0 lowers p by one, so the following is finite on every summand:

    H_tot=h_0(1+δh_0)^−1
         =Σ_{k=0}^{p}(−1)^k h_0(δh_0)^k.                (15)

This contracts the total complex for D=d_0+δ. Here is a direct verification. Write A=1+δh_0 and B=1+h_0δ. Both have inverses on finite-support inputs; BH_tot=h_0 and H_tot A=h_0. Since δD+Dδ=0,

    B(DH_tot+H_tot D)A
      =B D h_0+h_0D A
      =D h_0+h_0D+h_0(δD+Dδ)h_0
      =1+δh_0+h_0δ=BA.

Multiplication by the inverses proves the identity. No appeal to an unspecified infinite homological-perturbation series is needed.

For a basis input at bidegree (p,q), whose finite templates have at most M new objects, a bound for the ℓ1 norm of (15) is

    Σ_{k=0}^p [(p+1)!/(p−k+1)!] ∏_{j=0}^k B_M(q+j).     (16)

There are p+1 faces at the first horizontal step, p at the next, and so on; transition chain maps have norm at most one. This establishes the bound term by term. It applies to the simplicial replacement, not to a claimed strict inverse of its augmentation to the ordinary colimit. Formula (15) has constructed signed coherent finite-support data in the full small-poset range. It has not constructed strictly compatible h_F on the ordinary colimit, still less positive cylinders on the categorical colimit.

## 8. A genuine arbitrary-target computation

The retained program private/chain_calculation.py works in n=1 with an actual categorical pushout, not merely the ordinary nerve of E before attachment.

Take A={0<1}; X has one object X and endomorphisms {1,e}, with e²=e≠1. Send both objects of A to X and its arrow to e. The new elements are a,b,c,d, with a,b<c,d, r(a)=0 and r(b)=r(c)=r(d)=1. Relations from old to new are exactly u≤y iff u≤r(y). The pushout has objects X,a,b,c,d. Its old endomorphisms are 1,e; for each new y there are two arrows X→y labelled 1 and e; arrows between comparable distinct new objects are unique. Postcomposing X→y with y→z multiplies its label by the image of r(y)≤r(z), which can be e. This is the Dwyer pushout formula read in Thomason and Ara–Maltsiniotis. The associativity follows from the functoriality of r and of A→X.

Use E1=E\{c}, E2=E\{d}, E12=A∪{a,b}. For the input edge [a,c], (5) gives α[a,c]=[a]. The intersection contraction gives h_12[a]=[X,a]_1. After the corrected section and the prescribed-retraction lift, the actual output is

    H[a,c]=[e, (X→d)_1] − [(X→a)_1, a→d]
           −[e, (X→c)_1] + [(X→a)_1, a→c].             (17)

The four terms are nondegenerate 2-simplices. This exhibits both the overlap correction and a negative coefficient on an actual mixed old/new composite. The program independently checks d²=0, dH+Hd=id−JP, PH=0 and HJ=0 on all 86 nondegenerate simplices in degrees 0–5, and the separate leaf prism identities in degrees 0–4. The degree counts are 5,13,17,17,17,17; maximum ℓ1 norms of H are 3,4,4,4,4,4. It initially had one unmatched parenthesis, corrected before any calculation ran. These finite checks support the signs; the all-degree identities are (5)–(10), not numerical extrapolation.

## 9. Positivity is an actual additional condition

For a right cylinder on directed complexes, write h_q(x)=C(x⊗u). Its necessary chain identity is

    d h_q(x)=h_{q−1}(dx)+(−1)^q(Gx−Fx).                 (18)

Moreover every h_q must take positive chains to positive chains. The ordinary signed homotopy operator is (−1)^q h_q; the sign convention alone does not make its values positive. Stationarity requires the WHOLE chain map on the old subcomplex to factor through the interval augmentation, retaining lower table entries, not just vanishing of top chains.

There is an elementary finite obstruction to simply taking F=U(ir) and G=id in a single right cylinder. Let E be the diamond with least element o, incomparable a,b, and greatest element t, and let A={o}. Put K=C_*(N_ord E) with its directed positive basis. By the strong-Steiner poset identification read in Gagna, U_∞(E)=νK. It is already a 2-category. Suppose a stationary right cylinder const_o→id existed. On vertices its positive 1-chains h_v have boundary [v]−[o]. Thus h_a=[o,a], h_b=[o,b], and h_t must be one of

    [o,t],   [o,a]+[a,t],   [o,b]+[b,t].                 (19)

For completeness, a nonnegative integral flow from o to t in this acyclic graph with total flow one is a single path: conservation at a and b and the augmentation at o leave exactly the three choices. There are only two positive 2-generators, [o,a,t] and [o,b,t].

Apply (18) to the edge [a,t]. Its required boundary is

    h_t−[o,a]−[a,t].

The coefficient of [a,t] in the boundary of a positive 2-chain is the nonnegative coefficient of [o,a,t]. Therefore h_t must contain [a,t]. Applying the same argument to [b,t] forces h_t to contain [b,t]. No path in (19) does both. This rules out that single specified right cylinder in n≥2, including ω. Applying the chain functor to a strict cylinder gives the same obstruction, since the strong-Steiner tensor and counit identify its directed complex with K⊗M[1]. In n=1 the triangular equations are quotiented, so this argument does not apply.

This is NOT a counterexample to the investigated zigzag or to any stipulated source theorem. E has greatest new t, and the source explicitly supplies id→G←K with K=const_o. It is precisely the distinction between a two-edge zigzag and a forced single positive cylinder. Reversing a topological homotopy also does not reverse a Gray cylinder.

Gagna's §§6.3–6.8 avoid (18) by constructing, for every simplex and interval cut, a positive concatenation of two chain values of complementary dimensions. Those maps give simplicial homotopies; they are not a single map K⊗M[1]→K with the desired endpoint data. In addition, equal endpoints alone do not make Gagna's chosen simplicial homotopy stationary on an entire old higher category: cuts can replace a composite old edge by the direct edge with the same vertices. The strict stationarity in Source317 is the stronger factorization it actually proves.

## 10. The stronger positive primary transport, checked late

Ara–Maltsiniotis 2015 §2.11 and B.14–B.16 give an actual all-dimensional transport of a POSITIVE directed-chain homotopy h from f:K→L to g:K→L. Its hypotheses are h(K_q^+)⊂L_{q+1}^+ and dh+hd=g−f, with the augmentation conditions. For a Steiner table x with entries x_j^0,x_j^1, the transported (i+1)-cell has lower entries

    f_j x_j^0+h_{j−1}x_{j−1}^1,
    g_j x_j^1+h_{j−1}x_{j−1}^0,

and top entry h_i x_i. B.15 verifies the successive whiskered sources and targets by table addition; B.16 splits the tables below and above a composition level j and verifies the complete composition formula. Thus this is not merely a theorem asserting existence of some higher cells. If h is a square-zero contraction to a constant, B.18 computes the table for ν(h)ν(h)_x and proves it is the identity on ν(h)_x. The terms h² and h(c0) actually vanish. These operations are paid.

In particular, on a poset with least vertex o, the positive formula

    h[w0,...,wq]=[o,w0,...,wq] if o<w0, and 0 otherwise

satisfies dh+hd=id−const_o and h²=0. Cancelling the two copies of every face containing o proves the identity. This is exactly the prepend operation of §6.3, and it works on the diamond in §9. Its transport is an oplax contraction with the LEFT tensor convention (positive homotopy), not a contradiction of the RIGHT-tensor antihomotopy obstruction (18). AM2020 B.4.1–B.4.2 distinguishes these two tensor placements explicitly. The dual consecutive-edge contraction of AM2015 §6.5 additionally uses the linearly ordered oriental: its sum over consecutive k between i0 and i1 is not available for an arbitrary branching interval.

There are two separate reasons this strongest transport does not finish the current construction. First, h in §§3–7 is an operator on normalized Street-nerve chains C_*(N_nY,N_nX), not a positive directed-chain homotopy on a Steiner presentation of Y. Passing to λY loses cell-boundary and whiskering information, and ν of normalized nerve chains cannot be silently identified with an arbitrary attached Y. Second, even before that representation issue, (6) has negative summands, and (17) exhibits them on actual mixed composites. The replacement hdh gives square-zero side conditions but does not restore positivity. The B.14 tables require positivity and correct lower boundaries at every level, so feeding in the signed correction does not define their cells.

A concrete stationarity check also clarifies the different Gagna construction. Let E={0<1<2}, n≥2, and let x be the Street 1-simplex whose edge is the composite path 0→1→2 in U_n(E). Take Gagna’s endpoint maps f=g=id, and the interval cut 0|1. His §6.6 formula assigns to the top edge the concatenation [0][2]=[0,2], while stationarity would retain [0,1]+[1,2]. Those are distinct 1-cells in U_n(E). Equal endpoint maps alone therefore do not prove the old-side stationarity needed for arbitrary-target pushout gluing. This does not dispute his simplicial-homotopy identity or unit equivalence.

## 11. The exact remaining operation

The signed overlap correction (6), prescribed-retraction formula (10), higher fillers (11)–(13), and finite perturbation formula (15) are constructed. The unpaid step is to realize this nerve-chain data as actual positive, source/target-compatible strict cylinder data under U_n(A), in every higher dimension, with a coherent finite-piece realization for all small E. It must respect each guarded composition and equality created by arbitrary attachments. Positivity at one chain degree, equality of endpoint functors, or an abstract homotopy of realizations does not discharge that step.

Ara–Maltsiniotis already pays the n=2 oplax variant with RDF2. Its actual proof transports mixed arrows (f2,f1) and mixed cells (α2,α1), uses old-side whiskering identities A1/A2 and B1–B4 to make formulas independent of representatives, and checks cocycles and horizontal composition in every mixed case. That construction uses an oplax functor from a CARTESIAN interval product, not the strict RIGHT Gray cylinder demanded here. It cannot simply be reinterpreted as the missing positive map. The signed h_A α term has no such all-dimensional realization in this work.

The r34 original's topological coning of prism boundaries has also been considered. It requires a fresh vertex disjoint from every vertex already used. No such reserve-vertex operation exists in the fixed directed poset or arbitrary attaching target here. Importing that proof without its hypothesis would change the problem. The r41 equivariant local-prism replication is already paid and does not solve the overlap-realization step.

PREFREEZE / no nominee. No weaker signed-chain, restricted-dimension, equivariant, or renamed model-structure result is submitted. The direct-cylinder obstruction is only a route diagnosis. No exhaustion, general impossibility, or new-to-literature claim is made.
