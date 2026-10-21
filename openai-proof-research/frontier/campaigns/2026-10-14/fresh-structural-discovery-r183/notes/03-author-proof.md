# Author proof of frozen S183N

This proof addresses the unchanged bytes in FROZEN-THEOREM.md, SHA256 31f7da24fdd8721b5a8d3e0bbc2083130e66ca9965eb1dc887ee9baa2d8efda0. It is research author work for independent review, not a manuscript/release or a correctness/contribution grade. Source323 at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and all its operative proofs are stipulated true.

## 1. Precise source interface and notation

Let T=omega∪{*}. All vector spaces until Section8 are real. E is the source completion of c00(omega1), with coordinate vectors e_alpha and coordinate functionals e_alpha*. Write [D] for closed linear span. The source partition is omega1=union_k C_k, every C_k unbounded. A pure k path uses C_k and successive ordinal ranges; a mixed path uses both successive ordinal ranges and successive color ranges. A path is its actual sequence (phi_i,j_i,p_i), not just the resulting functional. Each phi_i is a nonzero rational finite Type I functional with declared weight j_i; p_i increases, dominates j_i and the finite rho-values for the accumulated supports; the next weight is the fixed source injection sigma of the entire prefix code. The first weight is arbitrary. These are precisely ch:path-rule and the preceding definitions in source sections/norming.tex. The frozen descriptive phrase “The norming construction” refers to this section, whose actual title is “A dual space with coded norming functionals” and label is sec:norming; no alternative construction is intended.

The following paid source operations are used with their full hypotheses.

(a) ch:norm, ch:coordinates and ch:predual: coordinate vectors have norm1; coordinate, ordinal-interval and rectangle projections used here are contractions; on C_k,
||sum a_alpha e_alpha||≤||(a_alpha)||_(s_k), s_k=k+2;
X0=[e_alpha*]⊂E*, and E→X0* is the canonical isometric isomorphism. Every vector has countable coordinate support, by finite-support norm approximation.

(b) path:bounded: every actual path, and its allowed crops, defines a functional of norm≤1 by pointwise convergence of finite partial sums. path:rigidity: finitely many distinct paths of one family have tails with pairwise disjoint active weights; deleting the finite prefixes changes each functional by an element of X0. Type II consequently gives
||sum a_P QP||≤||(a_P)||_(q_t), Q:E*→W=E*/X0.
These facts do not require CH. For pure t=k, s_source(t)=s_(k+1); for t=*, s_source(*)=s_1. The parameter inequalities are s_source(t)'≤q_t and q_t'≤s_source(t), with 1<q_t<infinity.

(c) branch:reduction: for every infinite-dimensional closed F⊂E there are a nonzero limit gamma≤omega1, infinite-dimensional closed H⊂P_<gamma E, and a bounded U:H→F. Either H⊂P_Ck E and R=P_Ck P_<gamma, or R=P_<gamma and every P_Ck|H is strictly singular. In both cases RU=I_H and P_<beta|H is strictly singular for every beta<gamma. Paths supported below gamma, and on C_k in the pure case, satisfy P(Uh)=P(h).

(d) ev:small and the first part of branch:separation: finitely many strictly singular maps can be made simultaneously small on suitable unit vectors in an infinite-dimensional closed subspace. The gliding-hump/perturbation calculation has coefficient bound4 and perturbation eta=1/8000 when sum epsilon_i≤1/32000. We repeat its compatibility with arbitrary prescribed prefixes below.

(e) pair:exact: in every infinite admissible block sequence of a chosen family, in every tail and at ANY prescribed integer weight J≥1, there is a finite block y and a Type I phi of weight J in that family such that ||y||≤500, phi(y)≥1/2. The support of phi is within the ordinal range of y, and within its color range in the mixed case. The proof includes its weak-Cauchy, weight-window, Ramsey and norming-tree estimates in the source; we do not replace it by a bound merely for selected weights.

(f) twist:lemma: if ||B:E*→W||≤1/10, B*(W*)⊂J_E(E), and B(E*)⊂closure B(X0), then X=ker(Q-B) is a Banach space, restriction identifies E isomorphically with X*, and closure B(X)=closure B(X0). We supply its analytic argument in Section6, as well as checking all inputs.

No CH is used in (a)–(f). In the source predual section CH is used for the cardinality of the family of ALL paths. We replace that operation by Sections2–4. In particular, source branch:separation alone is not our selector lemma: a perfect separated subset need not meet a fixed small nonmeager subset at all.

## 2. Cofinal actual-path spaces and small nonmeager selectors

Call (gamma,k) admissible if gamma<omega1 is a nonzero limit and C_k∩gamma is cofinal in gamma. Call (gamma,*) admissible if gamma<omega1 is a nonzero limit and
for every beta<gamma and l<omega there exists alpha with beta≤alpha<gamma and col(alpha)>l.
For an admissible pair, Z_(gamma,t) is the set of actual paths of family t whose supports lie below gamma and whose total support is cofinal in gamma. A mixed path already has strictly successive nonempty finite color ranges, so its colors tend to infinity.

Give the collection D_(gamma,t) of all possible single pieces with their declared weight and metadata the discrete topology. It is countable: gamma is countable, coefficients are rational, supports are finite, and weights/metadata are integers. Membership as a legal Type I piece is simply a restriction of this countable set; it needs no effective decision procedure. The set of infinite sequences whose every finite prefix is a valid source path is closed in D_(gamma,t)^omega, since a violation is witnessed by a finite prefix. Fix beta_n increasing cofinally in gamma. Requiring some piece to reach or exceed beta_n is open. Thus Z_(gamma,t) is a G_delta subspace of that closed Polish space and is Polish with the relative product topology. Its basic opens are nonempty finite-prefix cylinders [r]. The empty prefix is allowed.

We need, in particular, extendibility of EVERY valid prefix r. If r is nonempty, let J be its dictated next weight; otherwise choose any J≥1. Choose alpha beyond the support of r and beyond any prescribed beta<gamma; in the pure case use C_k, and in the mixed case choose its color beyond both the color range of r and any prescribed l. Admissibility supplies alpha. The source Type I rule permits the one-child functional phi=e_alpha*/m_J: e_alpha* is a terminal in the pure family and belongs to a pure color, hence is an allowed terminal for the mixed family. Choose integer p larger than preceding metadata and at least J and all rho-values on the accumulated finite support. The resulting extended prefix is legal. Repetition crossing beta_n (and colors n for mixed paths) gives a member of Z. Two different permitted coordinates at the next step give incompatible extensions, so Z has no isolated points. There are infinitely many such coordinates in a pure admissible tail; in the mixed case arbitrarily high ordinal/color requirements give infinitely many choices as well.

Here is a continuous OPEN surjection pi_(gamma,t):omega^omega→Z, so no descriptive-set-theoretic coding theorem is needed. At stage n, for each finite prefix r, list all its proper finite valid extensions that cross beta_n and, for the mixed family, contain a coordinate of color>n. There are countably infinitely many: existence follows above, and one can add further pieces. Fix a surjective enumeration by omega. Given a∈omega^omega, select at stage n the a(n)th listed extension of the prefix obtained so far. Their union is a legal cofinal path. Each stage adds a piece; hence fixing sufficiently many input coordinates fixes any prescribed finite output prefix, proving continuity. Conversely, given any cofinal path extending the prefix reached at stage n, choose its longer prefixes successively crossing the next requirements. These choices supply an input tail coding exactly that path. It follows both that pi is surjective and that the image of each input cylinder is exactly the output cylinder above its chosen prefix. Therefore pi is open.

Assume non(M)=aleph1, and fix once and for all a nonmeager L⊂omega^omega of cardinal aleph1. For each admissible pair put A_(gamma,t)=pi_(gamma,t)[L]. This is nonmeager in Z. To verify this, if C is closed nowhere dense in Z, its inverse image is closed; every nonempty input open set has nonempty open image, which meets Z\C, so that inverse image has empty interior. Countable unions show that inverse images of meager sets are meager. If pi[L] were meager, L would be meager, a contradiction. Since Z has no isolated points, every countable subset is meager, so |A_(gamma,t)|=aleph1.

Define A_t as the union of these sets over all admissible countable gamma for that t. The number of pairs is at most aleph1, and countably many families are involved, so |union_t A_t|≤aleph1. For instance, choose a strictly increasing sequence in C_0 and let gamma be its supremum; this is an admissible pure pair. Its selector already has cardinal aleph1. Thus |union_t A_t|=aleph1 exactly. All these choices depend on the source construction and L, and are completed before any subspace F is considered.

## 3. A category clique lemma

Let Z be a Polish space without isolated points, A⊂Z nonmeager, and R⊂Z² symmetric open dense. Let (U_n) be a countable base of nonempty opens and define
B_n={z∈Z: there is no w∈U_n with (z,w)∈R}.
Its complement is the projection of the open subset R∩(Z×U_n), hence open. For every nonempty open V, density of R gives a point of R∩(V×U_n); openness gives a nonempty open V'⊂V for which every z∈V' has such a witness w. Thus B_n is closed nowhere dense. Outside B=union_n B_n, every section R_z={w:(z,w)∈R} is dense open.

Choose z_alpha∈A recursively for alpha<omega1. At stage alpha the previously chosen indices are countable. Avoid B, every singleton {z_beta} for beta<alpha, and every closed nowhere dense complement Z\R_(z_beta). Their union is meager: singletons are nowhere dense in this T1 no-isolated-points setting, and all previous choices avoided B. The nonmeager A is not contained in this union, so a choice exists. Then (z_beta,z_alpha)∈R for every beta<alpha; symmetry gives the other orientation. The points form an omega1-sized R-clique. Notice that no regularity property of A, Luzin hypothesis, uncountable Baire-category intersection, or enumeration of the relations R is involved. The same A can be used in this existence assertion for every such R separately.

## 4. Dense separation in every prescribed product cylinder

Fix an infinite-dimensional separable closed F⊂E. There is a countable set S of coordinates supporting F: take supports of a countable dense family and then their union. The coordinate restrictions outside S vanish on all F by continuity. Some countable ordinal lambda bounds S. Thus P_<lambda|F=I, so the least ordinal gamma in branch:reduction is countable, not omega1. Apply that reduction and obtain H,U,t and R as in Section1(c). In particular ||U||≥1, since R is contractive and RU=I on nonzero H.

The pair (gamma,t) is admissible. In the pure case, if C_k∩gamma were bounded by beta<gamma, P_<beta|H would be the identity after increasing beta within the limit gamma, contradicting strict singularity. In the mixed case, failure of admissibility supplies beta<gamma and l with no coordinate in [beta,gamma) of color>l. Then on H,
I_H=P_<beta|H+sum_(j≤l) P_[beta,gamma) P_Cj|H.
Every term is strictly singular: this holds for the first term by minimality and for each other term by composition with a bounded projection. The finite sum would be strictly singular, impossible for the identity of an infinite-dimensional space. Equivalently ev:small simultaneously makes the displayed terms too small on a unit vector. Thus Z=Z_(gamma,t) is one of the path spaces already selected.

Path evaluation is continuous on Z for EVERY x∈E. For a finitely supported x, only its coordinates below gamma can contribute. A sufficiently long prefix has passed all those coordinates, by cofinality; all its extensions give exactly the same value on x. For general x, approximate in norm by finite vectors x_n. The functions P↦P(x_n) converge uniformly, because ||P||≤1 for all P. This proves continuity. Consequently, for each d>0,
R(F,d)={(P,Q)∈Z²: ||P|F-Q|F||>d}
is open: it is the union over x∈B_F of the open sets |P(x)-Q(x)|>d. It is symmetric.

Set eta=1/8000 and
 d_F=1/[2000 ||U||(1+eta)].
We prove R(F,d_F) dense. Let [r]×[s] be any nonempty product of prefix cylinders in Z, including the possibility of empty or identical prefixes. Choose beta<gamma strictly beyond the combined ordinal supports of r and s; in the mixed case let l dominate their combined colors. Select positive epsilon_i with sum_i epsilon_i≤1/32000.

Inductively choose unit h_i∈H so that ||P_<beta_i h_i||<epsilon_i/3 and, in the mixed case, sum_(j≤l_i)||P_Cj h_i||<epsilon_i/3, where beta_i is beyond the previous block and the initial two prefixes and l_i is beyond the corresponding colors. This is exactly the finite collection of strictly singular maps to which ev:small applies. Remove the initial ordinal segment and, in the mixed case, the initial colors. Contractivity bounds the change by less than 2epsilon_i/3. Approximate by a finite vector cropped to the remaining ordinal/color sets to obtain z_i with ||h_i-z_i||<epsilon_i. In the pure case retain C_k. Thus z_i is an infinite admissible sequence after BOTH prefixes, with ||z_i||≥1/2.

The ordinal prefix projections on [z_i] have norm≤1. Their differences isolate each coefficient, so on finite sums |a_i| ||z_i||≤2||sum a_j z_j||, hence |a_i|≤4||sum a_j z_j||. The map Vz_i=h_i therefore obeys
||(V-I)sum a_i z_i||≤4(sum epsilon_i)||sum a_i z_i||≤eta||sum a_i z_i||.
It extends to V:[z_i]→H, with ||V||≤1+eta. Its range lies in closed H; I denotes inclusion into E.

Let J be the next weight dictated by r, or any positive weight if r is empty. Apply pair:exact in this sequence at J, obtaining y and phi with ||y||≤500 and phi(y)≥1/2, with phi's ordinal/color range within that of y. Append phi to r and choose legal metadata large enough for the ENTIRE accumulated prefix, not just phi. Its next weight is then fixed by the original source code. Extend this new prefix with one-child pieces strictly beyond the full ordinal/color range of y and thereafter cofinally in gamma; Section2 proves this is possible. Let P be the resulting path. The old prefix and the future pieces vanish on y, so P(y)=phi(y)≥1/2.

Independently extend s first with a one-child piece of ITS own dictated weight strictly beyond the full range of y, and continue cofinally; call the result Q. All old pieces of s precede y, and all its new pieces follow y, so Q(y)=0. This remains valid when r=s: the two extensions diverge by their different first appended supports. No relation between their dictated weights is required. Both paths remain actual uncropped paths; any coding comparisons needed for later Type II combinations are supplied by source rigidity, not imposed at this construction step.

They have support below gamma (and on C_k in the pure case), so the exact lift identity applies:
(P-Q)(UVy)=(P-Q)(Vy).
Since ||P-Q||≤2,
(P-Q)(Vy)≥1/2-2eta||y||≥1/2-1000/8000=3/8.
Also ||UVy||≤500||U||(1+eta). The test vector is nonzero by the positive evaluation, hence
||P|F-Q|F||≥3/[4000||U||(1+eta)]>d_F.
This proves density in every prescribed product cylinder, with a positive margin independent of the prefixes. In particular it proves the stronger interface that the source's existential perfect separated tree does not by itself give.

Apply Section3 to the fixed nonmeager A_(gamma,t) and this R(F,d_F). We obtain omega1 distinct paths in A_t with pairwise restriction distance>d_F on F. For a general infinite-dimensional closed F⊂E, choose an infinite-dimensional separable closed F0⊂F, for example the closed span of a countable linearly independent sequence. The norm of any restricted difference on F is at least its norm on F0. The preceding conclusion for F0 proves clause1 of the frozen theorem for F, with the same family and positive constant. No separability assumption remains in clause1.

## 5. The selected-path operator and its adjoint

Keep the A_t from Section2. By Section1(b), for finitely supported scalars on A_t the map e_P↦QP is a contraction from ell_(q_t)(A_t) to W. Complete it to S_t. This uses actual distinct paths, including metadata, exactly as in source path:rigidity. Even if two actual paths could define the same functional, this does not affect boundedness; the separated subfamilies in Section4 necessarily have distinct functionals.

Partition C_1 into two sets each of cardinal aleph1. Inject A_0 and A_* into these two parts respectively. For k≥1 inject A_k into C_(k+1). Denote all the injections by iota_t. Their ranges are pairwise disjoint, and their source-color exponents are s_source(t) from Section1. For y∈E* put b_t(y)=(y(e_(iota_t(P))))_(P∈A_t). Testing finite scalar vectors against the source coordinate upper estimate and using finite-dimensional duality gives
||b_t(y)||_(s_source(t)')≤||y||.
Taking a supremum over finite subsets proves membership in this ell_p space, even for uncountable A_t. Since s_source(t)'≤q_t, the standard inclusion ell_(s_source(t)')⊂ell_(q_t) has norm1, so ||b_t(y)||_(q_t)≤||y||.

Enumerate T as t_0=*, t_(n+1)=n. Fix tau_(t_n)=2^(-n-1)/10. These are strictly positive and sum exactly1/10. Define
B y=sum_(n≥0) tau_(t_n) S_(t_n)b_(t_n)(y).
The series converges in operator norm and ||B||≤1/10. Let V_A=closure span{QP:P∈A_t,t∈T}. Each S_t image lies in V_A, by finite-support density in ell_(q_t), so B(E*)⊂V_A. Conversely disjoint label ranges give
B e_(iota_t(P))*=tau_t QP.
These coordinate functionals belong to X0, and hence closure B(X0)=V_A.

For w*∈W*, S_t*w* belongs to ell_(q_t')(A_t) with norm≤||w*||. Because q_t'≤s_source(t), it also belongs to ell_(s_source(t)) with no larger norm. Its support is countable since q_t' is finite. The coordinate upper estimate and finite-tail approximation give a norm-convergent vector
v_t=sum_(P∈A_t) (S_t*w*)(P)e_(iota_t(P))∈E,
||v_t||≤||w*||.
The sum v=sum_t tau_t v_t converges in E. Testing on y∈E*, and passing first through finite coordinate sums and then the absolutely controlled family sum, gives
(B*w*)(y)=w*(By)=y(v).
Thus B*w*=J_Ev, with no bidual-only lift or formal infinite series substituted for an actual E-valued vector. All requirements in frozen clause2 preceding X are proved.

## 6. The new predual is complete and has dual E

For clarity, the following is the paid source twist operation with its constants, now applied to the selected map. Let b=||B||≤1/10 and L0=Q-B. For every w∈W choose a Q-lift of norm≤(11/10)||w||. Lift its B-error and iterate; the resulting series has total norm at most C||w||, where
C=(11/10)/(1-(11/10)b).
It is an L0-lift of w. Therefore L0 is a bounded surjection, Cb<1, and X=ker L0 is a closed subspace of the Banach space E*, hence complete.

As E=X0* canonically, restriction onto X0 gives E**=X0^perp⊕J_E(E). Q* identifies W* isometrically with X0^perp. Surjectivity and the lift bound yield
X^perp=L0*(W*)={Q*w*-B*w*:w*∈W*}.
Indeed a functional on E* vanishing on ker L0 factors boundedly through L0 by that bound. This annihilator is a graph over X0^perp with values in J_E(E). The latter therefore maps bijectively onto E**/X^perp=X*, and this map is precisely restriction E→X*. It is a bounded isomorphism by the open mapping theorem.

Set G=closure B(X)⊂V_A. The map A:W→V_A/G defined by A(L0 y)=By+G is well-defined; different lifts differ by X. Its norm is at most Cb<1. For y∈X0, L0y=-By, so A(By)=-By+G. Density B(X0) in V_A implies A|V_A equals minus the canonical quotient V_A→V_A/G. If G were proper, this quotient would have norm1, a contradiction. Hence closure B(X)=V_A. This proves the predual and density assertions in clause2 without an assumption that B(X) itself is closed.

## 7. Excluding actual Banach quotients and computing real densities

For any separable infinite-dimensional closed F⊂E, set C_F=closure{y|F:y∈X0}⊂F*. It is separable. In fact a countable dense set in F has a common countable support S, all other coordinate evaluations vanish on F, and restrictions of X0 lie in the closed span of {e_alpha*|F:alpha∈S}.

The bounded restriction map induces
T_F:W→F*/C_F, T_F(Qy)=y|F+C_F.
It is well-defined because all X0 restrictions lie in C_F, and bounded because one can take the infimum over representatives of Qy. If T_F(V_A) were separable, let M be its separable closure. The inverse image of M under the norm quotient F*→F*/C_F would be separable. Explicitly choose a countable dense sequence (m_n) in M and fixed lifts u_n in F*, and a countable dense set (c_j) in C_F. For any z in that inverse image and epsilon>0, choose m_n within epsilon/2 of its quotient; the quotient norm gives c∈C_F with ||z-u_n-c||<epsilon/2, and then choose c_j close enough to c. Thus {u_n+c_j} is dense. This inverse image contains all selected path restrictions P|F, because QP∈V_A. Clause1 supplies an uncountable positively separated subset of them, impossible in a separable metric space. Consequently T_F(V_A) is nonseparable.

The identity closure B(X)=V_A implies closure T_F(BX)=closure T_F(V_A). Thus T_F(BX) is nonseparable. For x∈X, Qx=Bx, so T_F(Bx)=x|F+C_F. It follows that the evaluation image {x|F:x∈X}⊂F* is nonseparable. Write R_X:E→X* for the restriction isomorphism. For each separable infinite-dimensional closed F'⊂X*, take F=R_X^(-1)(F'); composition with R_X|F identifies its X-evaluation image with the one just considered. A bounded isomorphism preserves norm separability. Hence every such F' has a nonseparable evaluation image.

To see directly why this forbids a genuine Banach quotient, suppose q:X→Y is a bounded surjection onto a separable infinite-dimensional Banach space. Its adjoint q*:Y*→X* is bounded below (the open mapping theorem, or the quotient norm, gives the lower bound). Choose a separable infinite-dimensional closed G⊂Y*. Then F'=q*(G) is a separable infinite-dimensional closed subspace of X*. Under the isomorphism G→F', evaluation at x∈X is g↦g(qx). These evaluations lie in the bounded linear image of the separable space Y in G*, so are norm separable, a contradiction. Quotients by closed kernels have precisely this surjective Banach-space form. Nothing here treats a merely algebraic quotient, a dense nonclosed kernel, or a one-dimensional functional as an infinite-dimensional quotient.

Finite rational-coordinate vectors are dense in E and have cardinal aleph1, while ||e_alpha-e_beta||≥1 for alpha≠beta. Therefore dens E=aleph1 and dens X*=aleph1. To show dens X≤aleph1, choose a norm-dense D⊂S_(X*) of cardinal aleph1, and for each f∈D choose x_f∈S_X with |f(x_f)|>1/2. Their closed linear span is X: otherwise a Hahn–Banach g∈S_(X*) vanishes on it, while ||f-g||<1/2 for some f∈D contradicts that choice. Finite rational combinations of the x_f give the desired density bound. X is infinite dimensional because X*≅E; if X were separable, its identity map would be a forbidden separable infinite-dimensional quotient. Hence dens X=aleph1. Clause2 is proved.

## 8. Complex field and both complex densities

Give X_C=X+iX exactly the frozen norm. Phase rotation proves complex absolute homogeneity; the triangle inequality follows from X's, and
max(||x||,||y||)≤||x+iy||_C≤||x||+||y||≤2max(||x||,||y||).
Thus X_C is complete and its underlying real space is isomorphic to X⊕_infinity X. Source ev:finite-sum, whose proof was read in full, says this sum has no separable infinite-dimensional real quotient when X has none. A bounded complex surjection from X_C onto a separable infinite-dimensional complex Banach space would, on restriction of scalars, give just such a real quotient. This proves absence of the asserted complex quotients. The finite-sum theorem is essential here; a real restriction of a single complex functional would not prove this assertion.

The displayed norm equivalence gives dens X_C=aleph1. Its real dual is isomorphic to X*⊕X* and hence has density aleph1. For any complex Banach space Z the map from real functionals g on Z_R to complex functionals f_g(z)=g(z)-i g(iz) is a real-linear isometric bijection, with inverse f↦Re f. Complex linearity is immediate; norm equality follows by rotating each z to make f_g(z) real and nonnegative. Apply this with Z=X_C to get dens X_C*=aleph1. This proves clause3 at its precise norm and full scope.

## 9. What is proved, paid, and not asserted

Sections2–4 construct the fixed small hereditary separator; Sections5–8 establish all analytic compatibility requirements and the frozen consequences. The new interface claimed for consideration is the arbitrary-prefix dense separation lemma with a uniform-in-prefix positive margin, which lets one nonmeager set provide a simultaneous small selector for all subspaces without enumerating them. The category clique lemma itself is elementary/classical, and the source exact pairs, coding, path coset bounds, twist, quotient criterion, field transfer and density arguments are paid. The completed ALAT and ADK primary mechanisms are also paid; this author proof does not claim their coding or fusion as new.

A collection of continuum many source branch functionals is not simply relabeled by omega1. The selector is constructed first, and its hereditary separating property is proved before it enters B. The density and adjoint series are checked in norm; no only-weak-star limit stands in for an E-valued vector. The model hypothesis is used solely to supply L, and every E, Z, completion, subspace, and quotient map is interpreted in the same universe. No theorem about preserving a ground-model Banach space or its quotient property under forcing, no Cohen-model corollary, and no unconditional ZFC counterexample is claimed.

There is no remaining stated mathematical obligation deliberately left conditional inside the frozen theorem beyond its explicit hypothesis non(M)=aleph1 and the stipulated source operations. This is an author assertion of a full proof, subject to independent adversarial correctness and separate contribution review, not a self-issued pass. Reading/access/isolation limits are recorded separately and do not constitute global impossibility or priority claims. All older frozen targets and dispositions remain unchanged.
