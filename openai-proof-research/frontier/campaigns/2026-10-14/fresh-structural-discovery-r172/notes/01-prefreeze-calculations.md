# Prefreeze calculations: short words, arithmetic cells, and finite models

Status: research calculations, not a frozen statement or author-proof nominee. No correctness, contribution, acceptance or count is assigned. Constants below depend on the fixed source parameter, track number and finite generating set. The operative source proofs are stipulated. The primary comparison was completed before writing this note; precise protected references are in private/operative-comparison.md.

## Fixed setting and the distinction being tested

Fix one allowed quadratic parameter and one sufficiently large finite track number m in SOURCE253. Let G=A_m, with the source finite generating set S, symmetrized and with identity entries discarded. Set alpha=(sqrt(5)-1)/2, O=Z[alpha], and K=Q(sqrt(5)). Each generator on each polygon chart sends (i,z) to (j,z+(p alpha,q alpha)) modulo Z², with integer p,q. Let B bound the absolute values of these increments for S and its inverses. The four line normals are fixed. A fixed integer D clears all intersection denominators. All constants in this note may depend on these fixed data, and no uniformity in m or the quadratic parameter is claimed.

Finite orbit boxes approximate this action, not the regular action of G. Most points can be fixed by a nonidentity element. Boundary estimates alone therefore do not establish an almost-free finite model. The calculation below pays both the boundary error and the short-word support estimate and then applies the primary Cartesian amplification operation. It uses neither a claim of residual finiteness nor an effective enumeration of the source's existential finite relation set.

## 1. One arrangement for all words up to length R

Work in the closed unit square with its coordinate edges included as cuts. Pull back every fixed generator chart edge by all translations (p alpha,q alpha), |p|,|q|<=BR, and use all relevant integer lifts. Keep only resulting lines meeting the square. These lines refine every itinerary chart of every word of length at most R: at an itinerary step the prefix displacement has both integer coordinates bounded by BR. Track choices introduce no new directions or larger displacement bound.

If a retained line has equation ell(z)=t, then t belongs to O, its ordinary absolute value is bounded by a fixed constant (because the line meets the square), and |bar(t)|<=C(R+1). To check the latter despite reducing coordinates modulo one, every integer lift needed for a translated point has size O(R); conjugation of p alpha and of such integers has size O(R). Fixed original edge levels contribute only a fixed constant. In the two embeddings, the O-lattice therefore puts at most C(R+1) distinct levels in each direction. There are O(R) lines and O(R²) two-dimensional chambers. This is an upper bound on the universal arrangement, independent of the exponentially many words.

Every vertex v of this arrangement is in D^{-1}O² and satisfies |bar(v)|<=C(R+1), by solving one of finitely many fixed two-by-two systems. For a line not through v,

    z=ell(v)-t is a nonzero element of D^{-1}O,
    |bar(z)|<=C(R+1),   |z bar(z)|>=D^{-2}.

Consequently its Euclidean distance from v is at least c/(R+1). The norms of the four normals are fixed; they are absorbed in c. This also applies to square edges and to parallel nonincident lines.

Take a vertex in the closure of any nonempty chamber. Within a ball of radius c/(2(R+1)) about that vertex, only lines through the vertex can occur. The chamber occupies one angular sector of those lines. The minimum positive sector angle is fixed, because there are only four unoriented line directions. A point on its bisector, at a suitably small fixed fraction of that radius, has a ball of radius c'/(R+1) inside the chamber. The ball contains an axis-parallel square of side c''/(R+1). Concurrent vertices and boundary vertices obey the same argument; clipping by the square just supplies more of the already included lines.

A nonidentity element represented by a word of length <=R acts nontrivially on at least one chamber and one input track. Indeed its local translation and output track are constant there. If it acted trivially on every ordinary chamber, it would fix the dense set of non-cut Stone points and hence be the identity homeomorphism. A nonzero integer increment modulo alpha is nonzero on the torus, so a nontrivial chamber translation moves every point in that chamber. A different output track also moves every point. Thus such a word moves all points of one square of side c''/(R+1), on one track.

## 2. A simultaneous deterministic orbit-frequency bound

Choose z_*=(sqrt(2)/10,sqrt(3)/10) modulo Z². Neither a coordinate nor either inclined linear form at this point lies in O. This follows from linear independence of 1,sqrt(2),sqrt(3) over K; the coefficients of the four forms lie in K. Every O² translate remains off all allowable cuts. Thus all points below have unique Stone lifts, and the integer labels give a faithful copy of a free Z² orbit on each track.

The source gap estimate says every consecutive index interval of length M gives a C/M-net on the circle under u -> u alpha modulo one. Choose M=ceil(C_0(R+1)) with C_0 large enough. Every M-by-M integer block therefore has a point whose orbit location falls in any specified axis-parallel square from section 1. The two coordinates may be chosen independently. This holds for every translated index block, with no limiting equidistribution argument and no union bound over words.

Let L=2N+1, D_N={1,...,m} x {-N,...,N}², and restrict to the inner index square at distance BR from its boundary. If L>=4BR+4M, this inner square contains at least (L/(4M))² disjoint M-by-M blocks. A nonidentity word of length <=R therefore moves, under its true action, at least the fraction

    1/(16m M²) >= c_0/(R+1)²

of D_N, using points in the inner square on its selected track. All words enjoy the same bound, though their selected chambers and tracks may differ.

## 3. Completion to permutations and the common good set

For each positive generator s, restrict its actual orbit permutation to

    E_s={x in D_N : s x in D_N}.

This is a bijection E_s -> sE_s. The two complements have equal cardinality, so complete it by any bijection between the complements, for example lexicographic matching of their labels. Call the resulting permutation sigma_N(s), and define sigma_N(s^{-1})=sigma_N(s)^{-1}. The inverse agrees with the actual inverse wherever both endpoints lie in D_N, because it inverts the prescribed partial bijection. Arbitrarily and independently completing both signs would not justify this compatibility.

Every word of length <=R follows its exact true trajectory from any point in the BR-inner square: every prefix displacement is <=BR, and all successive generator edges are prescribed edges of the completed permutations. Consequently all such words are simultaneously correct on this same inner square. The exceptional fraction is at most

    beta_R(N)=1-((L-2BR)/L)² <=4BR/L,

when L>=2BR. In particular every identity word of length <=R has normalized Hamming length <=beta_R(N). Every nonidentity word of that length has Hamming length >=c_0/(R+1)², by section 2 counting only points in the inner square. There is no subtraction of an independently estimated boundary error from the support fraction.

## 4. Cartesian amplification and its full parameter budget

Act diagonally on D_N^k. Evaluation of a word commutes exactly with this product construction. For a permutation with moved fraction p, its k-fold product has moved fraction 1-(1-p)^k. Hence:

* an identity word of length <=R moves a fraction at most k beta_R(N);
* a nonidentity word of length <=R fixes a fraction at most exp(-c_0 k/(R+1)²).

For 0<epsilon<=1/2 choose

    k=ceil(c_0^{-1}(R+1)² log(1/epsilon)),
    L odd and >= max(4BR+4M, 4BR k/epsilon).

All identity words of length <=R then have defect <=epsilon and all nonidentity words of length <=R move at least 1-epsilon. Taking the least admissible odd L gives degree d=(mL²)^k and

    log d <= C(R+1)² log(1/epsilon)
             [log(R+2)+log(1/epsilon)+log log(e/epsilon)].

The use of log log(e/epsilon), which is nonnegative, avoids a spurious negative term. Ceilings are absorbed using epsilon<=1/2. For epsilon=1/r and R=3r, r>=2,

    d <= exp(C r² (log r)²).

This is a uniform calculation for a fixed group and generating set, not a numerical constant or a claim uniform over the source family.

For a finite chunk B_S(r), choose one representing word w_g of length <=r for each g, with w_1 empty, and put phi(g)=sigma_N(w_g)^{x k}. If g,h,gh belong to the chunk, the word w_g w_h w_gh^{-1} has length <=3r and is trivial. Bi-invariance of Hamming distance gives multiplicative defect <=epsilon. If g !=h, w_g w_h^{-1} is a nonidentity word of length <=2r, giving separation >=1-epsilon. Thus the generator-assignment calculation really supplies a chunk model. It is not an assertion that evaluating different words gives the same permutation. A fixed-chunk sofic profile and the simultaneous radius/accuracy growth just displayed are different functions.

## 5. Small supports show the r^{-2} loss is intrinsic to this orbit action

Here use the source generating set S_m and m>=6, with five selected tracks and one spare. This is compatible with the source's sufficiently large fixed m. Let beta=1-alpha<1/2. For a=k alpha, b=l alpha modulo one, suppose the positively oriented arc [a,b) has length h<beta. It is the intersection of the two length-beta circular arcs

    [a,a+beta) and [b-beta,b).

There is no second intersection component: in a lift, the union spans length 2beta-h<1. Both arcs are translates of the complement of [0,alpha): their translating indices are k-1 and l. A common translation on the five tracks is balanced on the spare track. It is a product of five source balanced-translation generators per unit displacement, so translating a test by either endpoint costs O(|k|+|l|+1).

Complements are supplied by multiplying the constant permutation by the inverse conditional permutation. For even permutations g,h on these five tracks,

    [g on U,h on V]=[g,h] on U intersection V.

For example g=(12)(45), h=(23)(45) have a nontrivial three-cycle commutator. Conjugating and taking a bounded number of products supplies every even permutation on the intersection; the required bound is an absolute finite constant because Alt(5) is fixed. Thus every desired even conditional permutation on [a,b) has word length O(|k|+|l|+1). Applying the same intersection identity to an x-interval and a y-interval yields every even conditional permutation on their rectangle with word length O(n) when all endpoints have indices in [-n,n]. There is a fixed number of intersections, so no recurrence with depth growing in n is hidden here.

The 2n+1 orbit endpoints cut each coordinate circle into 2n+1 arcs. For sufficiently large n, each has length between c/n and C/n, and all have length <beta. Their (2n+1)² rectangles form a Boolean partition, modulo the discarded geometric boundary. On any one rectangle a conditional three-cycle has word length <=C_1 n and moved area fraction <=C_2/n² (with counting measure on tracks normalized by m). Thus the minimum nonzero moved measure in the radius-r ball is bounded above by C/r², after choosing n proportional to r. Section 1 gives the matching lower bound c/r² for this action.

The rectangle copies of Alt(5) have disjoint support and commute; each is faithful and their intersections are trivial. They give an embedded Alt(5)^{(2n+1)²}, each individual factor lying in B_S(C_3 n), while the whole product lies in B_S(C_4 n³). This implies |B_S(C_4 n³)|>=60^{(2n+1)²}. It is a coarse growth calculation, not a claimed best growth bound, and not a new target.

For the product of the actual measured action, the small-support example forces k>=c r² log(1/epsilon) to achieve (1-epsilon)-movement uniformly on the ball. This only concerns independent amplification of that action. It does NOT lower-bound arbitrary finite permutation models: boundary completions can move extra points, other actions exist, and different correlated constructions might be smaller. In a finite orbit box, a corresponding upper bound on moved proportion includes the added boundary fraction. No finite-model optimality conclusion is drawn by dropping that fraction.

## 6. Simplicity and finite presentation: the exact obstruction, fully composed

Any homomorphism from the infinite simple G to a finite symmetric group is trivial: a nontrivial homomorphism would have trivial kernel and inject an infinite group into a finite one. Fix any finite presentation on S, which exists by the source (Tietze transport from a finite presentation to this finite generating set suffices). For R above its maximum relator length, the assignments in section 4 make every defining relator epsilon-close to the identity, while every nonidentity generator moves >=1-epsilon. Their distance from every exact action on that same set is therefore >=1-epsilon for every retained generator. This supplies a concrete sequence exhibiting permutation instability, but that implication is already paid by primary results on amenable groups, residual finiteness and stability.

There is also one finite chunk that has no exact injective model into any finite group. Include all presentation relator prefixes, their successive multiplication triples, the generators, and identity. Any exact chunk map then yields generator images satisfying every relator, hence a homomorphism from G to a finite group; injectivity on a nonidentity generator contradicts triviality. In a permutation model of degree d, every nonzero defect is at least 1/d. Thus defect <1/d on this chunk is impossible with nontrivial separation. This yields only the familiar linear degree obstruction in inverse error. It does not match the exponential upper estimate and does not promote the short-support argument into a universal lower bound.

## 7. The other integrated route: the source random partitions

The source construction offers a different chain: bounded covariance changes of regularized random fields produce almost-equivariant finite polygon partitions; matching same-shaped cells to a baseline produces finitely supported Reiter measures on F_m. For fixed finite generator data and fixed auxiliary field parameters, a cutoff N has O(N²) active sites with a fixed number of binary fields, and O(N) possible supporting lines. Thus there are at most 2^{C N²} field configurations. A partition has at most C N² cells; all bijections between cells form at most (C N²)! possibilities, an overcount which also bounds the permitted shape-preserving matchings. The source uses bounded ordinary cells, whose translating identification is unique, so a matched pair introduces no further choices. The resulting measure can therefore be supported on at most exp(C N² log(N+2)) elements. This is a support bound at the source cutoff, not yet a bound as a function of epsilon alone.

Passing to G does not require an algorithm deciding membership in right cosets. A finitely supported measure on F_m splits over right cosets of G; left multiplication by G preserves each such coset. If the sum of generator variations is small relative to total mass, one nonzero coset restriction has no larger variation-to-mass ratio. Translate that coset to G and normalize. Layer-cake integration of this nonnegative finitely supported function selects a level set whose sum of generator symmetric differences divided by its size is bounded by the same ratio. Its cardinality is no larger than the original support. This pays subgroup compatibility and the Reiter-to-Folner conversion without a computability claim.

The source first chooses auxiliary eta,kappa to control geometric signal errors and then takes N large to control the remaining signal, covariance and tail errors. Constants in those later estimates may depend on the earlier parameters. I have not extracted a uniform dependence sufficient to replace N by one asserted elementary expression in epsilon. Such a dependence cannot be supplied by merely reading the displayed powers of log N. Moreover orbit boxes from sections 2–4 lie in an action of G; they are not subsets of G with small Cayley boundary. The model-degree estimate is not a polynomial or exponential Folner-function bound for G.

## 8. What has and has not been paid

The strongest integrated operation here is: universal arithmetic itinerary arrangement -> uniform chamber inradius -> deterministic orbit-block support -> inverse-compatible completion -> Cartesian amplification -> chunk multiplication and separation -> exact-action obstruction. All its compatibility steps have been carried out. The local Alt(5) construction additionally checks the sharp r^{-2} support scale for this action. These are concrete prefreeze calculations, not merely the name of an unresolved conjecture.

The primary proof already uses the completion and Cartesian amplification literally. The source already pays the arithmetic norm and gap estimates, conditional commutators, fixed-track finite generation, finite presentation, simplicity and amenability. I have not identified a fully paid nonroutine operation beyond these compatible mechanisms. No new result is frozen or nominated on the strength of the bound above.

Two precise statements remain unproved in this investigation, and neither is proposed as a theorem: (i) a uniform lower degree bound for arbitrary finite approximate models substantially stronger than the fixed-chunk 1/epsilon obstruction; (ii) an explicit quantitative Folner estimate obtained from the random partition method with all eta,kappa-dependent constants and matching choices accounted for. Local product groups do not solve (i), since approximate images need not be exact commuting faithful actions. The cutoff support estimate does not solve (ii), since it leaves the parameter dependence unpaid. The old higher-finiteness and exact-multiplier targets are not altered, restricted, or retried.
