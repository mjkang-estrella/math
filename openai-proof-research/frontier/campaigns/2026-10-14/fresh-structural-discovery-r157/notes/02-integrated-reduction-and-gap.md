# Source168 — integrated reduction and ending boundary

**PREFREEZE / no nominee.** One family was developed: equal-parameter Bruhat/Kazhdan–Lusztig and moment-graph structure. No exact new theorem was frozen, no author-proof nominee is submitted, and no mathematical grade or count is assigned. All old frozen scopes and dispositions are unchanged. These are research calculations, including consequences deliberately not nominated.

## 1. Paid source operations at their full scopes

The canonical Source168 manuscript is `preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026`, at stipulated pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. All five substantive sections, both figure sources, main file, README and bibliography were read. Its statements and operative proofs are inputs, not objects of a truth audit.

For arbitrary Coxeter systems, an arbitrary abstract isomorphism iota:[u,b] -> [u',b'] preserves P_{x,y} and R_{x,y} for every subinterval. The proof supplies substantially more: graph reconstruction; transport of full relative dihedral intervals; actual simultaneous decomposition of the sheaf's stalks AND restriction maps after root-plane localization; and free terminal kernels for every transported geometric reflection schedule. Intermediate images satisfy exact I_e=f_e J_e, where deg(f_e)=(length(y)-length(x)-1)/2. Their graded ranks are preserved across the two schedules. This includes equality of the actual embedded image modules within each system, including elimination of the possible higher-codimension quotient. None of those operations is left unpaid.

A terminal kernel K_x(F) uses ALL upward edges at x later than a threshold in ONE such schedule. Source proves freeness for every such choice; it does not merely compare one basis vector or one rank. The source permits different coefficient polynomial rings for different real realizations. It does not manufacture vertexwise linear identifications of the root-label spaces between arbitrary interval realizations.

## 2. Parabolic refinements: the strongest compatible primary composition

Barkley–Gaetz, arXiv:2404.04246v3, was read in full, including `lem:set-is-combinatorial`, `thm:invariant-I` and all its proofs. The method is an atom-avoidance description of a fibre, not an enlarged-Coxeter construction (the latter was an incorrect pre-read guess, explicitly corrected in note01).

For u,v in W^J, let A^J be the atoms of [u,v] lying in W^J. Their lemma gives exactly

    u W_J intersect [1,v]
      = {y in [u,v] : no a in A^J satisfies a <= y}.                  (1)

For the forward direction, projection to W^J is order preserving and sends uW_J to u. Conversely, if y^J>u, the graded quotient interval has an atom a<=y^J<=y, a contradiction. Thus marked atoms determine the entire bottom fibre as an actual subset of the interval, not just its size.

Apply Source168 to every upper subinterval and use Deodhar's formulas as stated in this primary:

    R^{J,z}_{u,v} = sum_{y in bottom fibre} (-z)^{length(y)-length(u)} R_{y,v}, z=-1,q;
    P^{J,q}_{u,v} = sum_{y in bottom fibre} (-1)^{length(y)-length(u)} P_{y,v}. (2)

All sums are finite, even if W or W_J is infinite, since y<=v. Hence an abstract interval isomorphism preserving just these marked atoms already preserves both parabolic R types and the type-q P-polynomial. This is the primary equivalence applied to the stipulated theorem, not a new compatibility operation.

If the full subsets [u,v] intersect W^J are marked, the same argument applies to all relevant subintervals. Parabolic reciprocity and its degree bound then recover both P types. Atom-only marking does not give the type-minus-one conclusion: the primary's explicit Boolean rank-three example has P^{J,-1}=1 versus 1+q. That example is credited, not submitted as a discovery or weakened target. Deodhar's 1987 original proof was not acquired; the actual Barkley–Gaetz transfer proof was read. No transitive-completeness claim is made.

## 3. Arbitrary simultaneous edge constraints: saturation is already paid

Fix the full Source168 real realization, A=Sym(V), with all root forms in degree one, and its sheaf B(b). Fix x<=b, upward star U, and ANY subset F of U. Let

    M=B^x, K(F)=ker(M -> E_F), E_F=direct_sum_{e:x->y in F} B^e,
    C_F=coker(M -> E_F), N_F(q)=(1-q)^N Hilb(K(F);q), N=dim V.

The numerator N_F need not have nonnegative coefficients: K(F) need not be free. Exactness always gives

    N_F(q)=P_{x,b}(q) -(1-q) sum_{e:x->y in F}P_{y,b}(q)
                        +(1-q)^N Hilb(C_F;q).                     (3)

Every individual lower-end map M -> B^e is surjective: choose a lift in the upper stalk, extend that stalk value to a global section using source generation, and restrict its value at x. Its kernel is free by the length-one resolution of B^e and graded Schanuel. This holds for EVERY single edge, whether or not that singleton is terminal in a realizable schedule.

More strongly, put p=product_{e in U minus F} alpha_e. Then

    K(F) = (K(U) :_M p).                                           (4)

Indeed p kills restrictions along U minus F. Conversely p is a nonzerodivisor on every B^e for e in F, since the roots incident to x are pairwise nonproportional and B^e is free over A/(alpha_e). Thus p m in K(U) forces exactly the F conditions on m. This is a single colon, not an unspecified saturation or infinite process. Source already provides the free full costalk K(U), its graded rank, and all actual sheaf maps. Therefore arbitrary-subset kernels are computable from the full LABELED embedded costalk by ordinary module algebra. A proposed missing existence/computability theorem here would be false.

Each K(F) is also reflexive. Let K_e be a singleton kernel. It is free and full rank in M. Each equals the intersection of its height-one localizations in M tensor Frac(A); finite intersections commute, and K(F)=intersection_{e in F}K_e. Thus K(F) is exactly its height-one intersection. The normal-domain criterion (Stacks tags 0AVB/0AVC, actual proofs read) gives reflexivity. This does not imply freeness or identify its Hilbert series from the ranks of the K_e. Crucially, the local lattices must lie in one identified rational vector space. Abstract ranks or local isomorphism types alone do not supply their relative positions.

For F,G, K(F union G)=K(F) intersect K(G), but K(F)+K(G) need not equal K(F intersect G). Plain inclusion-exclusion therefore does not compute every subset Hilbert series from the terminal ones. Formula(4) is the stronger compatible reduction used here.

## 4. What the full root-plane decomposition already computes

At a height-one prime only one selected edge can survive, and its map is surjective. Thus C_F has codimension at least two. A height-two prime supporting C_F must contain at least two selected labels, hence is precisely their root-plane prime (alpha,beta). No other height-two support is possible.

Use Source168 `loc:decomposition` at such a plane Pi. It is a simultaneous decomposition into models O_c with multiplicities m_c, retaining both endpoint maps. In a model containing x, let

    k_c = #{e in F : label(e) in Pi and upper(e) <=_D c}.

The localized cokernel is a direct sum of cokernels of

    R -> direct_sum_{i=1}^{k_c} R/(l_i),                            (5)

where R=A_(Pi) and the l_i are pairwise nonassociate lines in its two-dimensional regular local ring. The kernel is (product_i l_i)R. The length of the cokernel is binom(k_c,2): in the corresponding two-variable polynomial ring its numerator is k_c(1-q)-1+q^{k_c}; divide by (1-q)^2 and evaluate at q=1. Extending the other variables to the residue field and localizing preserves this finite length. Grading shifts disappear from this leading local multiplicity.

The multiplicities m_c do not require a new source algorithm. At every a in the finite relative upper set above x,

    P_{a,b}(1) = sum_{c >=_D a} m_c.                                (6)

Descending subtraction computes them, with all relevant c inside [x,b]. It follows from ordinary prime-filtration additivity of Hilbert series that

    N_F(q) = P_{x,b}(q) -(1-q) sum_{e:x->y in F}P_{y,b}(q)
            +(1-q)^2 sum_{Pi} sum_{c>=_D x}m_c binom(k_c,2)
            modulo (1-q)^3.                                      (7)

For completeness, a graded prime filtration of C_F contributes terms q^s Hilb(A/p). Primes of codimension at least three vanish modulo (1-q)^3 after multiplication by (1-q)^N. Every codimension-two supporting prime is linear, so its contribution is q^s(1-q)^2, congruent to (1-q)^2. Its number of occurrences is the length of (C_F)_p. This proves the stated coefficient formula without inferring any equality of C_F itself.

The sum in (7) is intrinsic under the source interval transport with F marked. One can write it as a sum over unordered pairs of F-edges and then sum the m_c over common relative upper vertices of that pair. For each pair, any contributing c belongs to a full relative interval [x,c]_D containing both edges. `dih:transport` transports that entire interval into the target plane fixed by the two image edges. These intervals agree on overlaps because they use the same vertex map and plane; applying the inverse gives the reverse inclusion. The upper subintervals needed in the descending equation(6) lie in the same union. Thus their posets and all P_{a,b}(1) are matched. There is no need to identify an entire ambient dihedral coset outside [x,b].

Accordingly the first three Taylor coefficients of the arbitrary-subset numerator at q=1 are already paid by source plane decomposition plus classical commutative algebra. This is an integrated reduction, not a partial-result nominee. Low-rank numerical agreement cannot promote it to equality of the full numerator.

## 5. Primary planar reconstruction and labeled pullback are also paid

Braden–MacPherson, arXiv:math/0008200v2, actual construction in section1.4 and actual section4 planar-relations proof were read. In their projective geometric setting the FULL boundary image is determined by extension on all relevant planar subgraphs. The proof uses a transverse polynomial subring A_0 over which both boundary and edge modules are free; the denominator ideal of an element is principal, and the extension construction eliminates its possible linear factors. This is stronger than merely matching local lengths and is fully credited.

It supplies the full labeled boundary module, so one can then project it to E_F or use(4). A projection of that boundary need not retain the freeness over A_0 used in the principal-ideal argument. This is why one cannot erase the image/elimination step and infer a partial-image theorem directly. The primary's SL3/Pappus example also explicitly warns that pairwise constant-value congruences alone do not equal all planar extension conditions.

Lanini, arXiv:1103.2282v3, Definitions2.3–2.4, pullback definition, Lemma5.1 proof and following remark were read. A moment-graph isomorphism carries vertexwise automorphisms of a COMMON label space, sends roots to unit multiples, and agrees at adjacent vertices modulo their edge label. The descending boundary-image/projective-cover proof then compares the actual BMP sheaves. Under those hypotheses it already compares every K(F), C_F, colon module, and graded resolution, after twisting by the specified ring maps. A conditional theorem that assumes these label automorphisms would merely repackage this primary operation and is not a nominee.

Source168 deliberately avoids assuming those automorphisms for an arbitrary abstract interval isomorphism. Its numerical comparison of terminal filtrations cannot be silently upgraded to one common semilinear map simultaneously intertwining all edge restrictions.

## 6. Exact finite calculation, with an explicit resolution

`code/finite_bmp.py` constructs the ordinary rational BMP boundary images for the 14-element interval [1234,3412] in S4. It uses exact Fraction elimination, actual root quotients and sections above each vertex. Ordinary P-polynomial recursion supplies the degrees needed for minimal boundary generators; all stalks in this example have generators in degrees0,1. This is implementation input/bookkeeping, not a truth test of Source168. The receipt retains every stalk degree and edge map, not just the final ranks.

It computes homogeneous kernels and their minimal-generator dimensions through degree5 for every subset at the two singular stalks 1234 and1324: 32+16=48 subsets. Six have at least three minimal generators although their generic rank is two, proving nonfreeness for these finite modules. No claim about later generator degrees is based solely on that truncation.

At x=1324 write A=Q[a,b,c], all variables of degree1, and B^x=A e_0 plus A e_1 with deg(e_0)=0, deg(e_1)=1. In the constructed homogeneous basis, the four outgoing maps on a vector f e_0+h e_1 are

    to1342: f+(a-c)h mod (b+c);
    to1423: f+a h     mod c;
    to2314: f         mod a;
    to3124: f         mod (a+b).

Choose F={1342,2314}. Set B=b+c and C=a-c; a,B,C are independent linear coordinates. The two equations are f=a p and a p+C h=B q. The Koszul calculation gives generators

    g1=(-a C, a),  g2=(a B,0),  g3=(0,B),

all of total degree2. Indeed reducing a p+C h=B q modulo a gives h=B t+a r and q=C t+a s, whence p=B s-C r. This proves generation in EVERY degree, independently of the finite degree cutoff. The only relations are multiples of

    B g1+C g2-a g3=0.

For if r g1+s g2+t g3=0, its first coordinate gives C r=B s, so r=B z and s=C z by coprimality; its second gives t=-a z. Thus

    0 -> A(-3) -> A(-2)^3 -> K(F) -> 0,
    N_F(q)=3q^2-q^3.                                               (8)

Here A(-d) means a free generator in degree d. Equivalently the image cokernel is C_F=A/(a,B,C), in degree0: its generators from the two edge summands become negatives via the constant stalk generator, and the degree-one stalk generator imposes C, with a and B already zero. Formula(3) is exactly

    3q^2-q^3 = (1+q)-2(1-q)+(1-q)^3.

The whole defect in this example is codimension three. All height-two lengths are zero, consistent with(7). This explains concretely why the lower-codimension reduction does not itself deliver a full Hilbert numerator. It does NOT contradict the source terminal theorem: this pair is not a terminal set of a source-eligible transported schedule, since those kernels are free. Nor does it disprove full marked-subset invariance under poset isomorphisms.

A second bounded diagnostic checks all self-isomorphisms of the two indicated upper intervals and transports all their star subsets, comparing the saved degree0..5 Hilbert and generator data. There are four automorphisms of the 14-vertex interval and eight of the 10-vertex interval, giving 128 subset comparisons each and no mismatches in the recorded degrees. Its actual results are in `receipts/finite-transport.json`. It is a finite self-comparison only, not cross-Coxeter invariance, an exhaustion theorem, or an independent mathematical gate.

## 7. Unpaid operation and why there is no nominee

The full-scope question investigated was transport of the FULL arbitrary marked-subset kernel/image Hilbert data under arbitrary abstract Bruhat-interval isomorphisms, without supplying compatible root-label automorphisms. The paid work includes:

* every source terminal filtration and its exact embedded transitions;
* all ordinary and the precise marked parabolic consequences;
* full labeled BMP construction and primary planar reconstruction;
* arbitrary F via the single colon(4), singleton freeness and reflexivity;
* all codimension-two contributions and the numerator congruence(7);
* all arbitrary-subset modules when Lanini's actual label-isomorphism hypotheses are present.

After that composition, a complete argument would still have to transport the higher-codimension image/elimination data, or construct compatible simultaneous embedded maps that imply such transport. Neither the terminal rank identities, ordinary P/R reciprocity, reflexivity of K(F), nor the planar multiplicity formula performs that operation. A reflexive kernel can retain a nonfree global presentation, and C_F need not be reflexive. The finite Koszul example exposes a nonzero codimension-three defect, but does not show whether that defect is intrinsic for ALL abstract interval isomorphisms.

Attempts to infer full equality from local lengths, to replace all subsets by terminal subsets, or to use reflexivity without a common ambient identification do not close. The strongest labeled saturation and primary pullback do close their own full scopes and are credited rather than called unpaid. No new method transporting the residual data was found, and no proof-feasible full new statement emerged. This is a research boundary for this round, not a claim of an open problem's novelty, impossibility, priority, or exhaustive clearance. The partial congruence, conditional pullback and finite nonfreeness example are all declined as nominees. No additional family was screened to fill the round.
