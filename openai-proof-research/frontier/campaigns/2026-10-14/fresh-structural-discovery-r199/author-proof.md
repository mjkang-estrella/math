# Author proof for frozen T323C199

This is a discovery-stage author proof, not an independent correctness review, contribution review, manuscript, or release. The exact scope is the immutable `frozen-statement.md` (SHA256 509645cdcabf8bf700027acb5ed1edff6d064b631fbfd6fe0b487b010994e229). All references to Source323 mean the authenticated September 23, 2026 manuscript at commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Its statements and operative proof operations are stipulated true.

The proof's additional construction is a single family of at most omega_1 actual paths per operation family, selected in a Cohen extension before any subspace is specified. It separates every new separable infinite-dimensional subspace. The source's analytical construction then applies to those selected paths. We give the support, completion, and finite-path compatibility arguments explicitly.

## 1. Ground data and the source interfaces

Work schematically over a ground universe M of ZFC. This notation is for the ordinary forcing argument; Section 10 states its syntactic relative-consistency interpretation. Fix an uncountable ground cardinal lambda and write P=Add(omega,lambda). All ordinals below omega_1 in the argument are ground ordinals, since P is ccc.

In M choose the data of Source323's real coordinate construction: a partition (C_k) of omega_1 into unbounded sets; the families t=0,1,...,*; parameters s_k=k+2, r_k=s_k', q_k with s_{k+1}'<=q_k<s_k', and mixed parameters s_*=r_*=2, s_1'<=q_*<2; and the source integer sequences, coherent finite closures F_p(beta), and coding injections sigma_t. These choices can all be made in M. Fix them throughout. One may choose the q_t rationally inside their indicated intervals, although the proof only needs their ground-model values.

Let D=c_00(omega_1,Q), with the norm given by the source finite rational norming set K. In any extension N of M with the same omega_1, write E^N for the internal real Banach completion of D. Its coordinate predual is

    X_0^N = closed real span {e_alpha*: alpha<omega_1} in (E^N)*.

The following source operations are used, with their full scope.

1. `ch:norm`, `ch:coordinates`, `ch:predual`: ordinal and rectangle projections are contractions; every vector has countable support; the coordinate norm on color C_k is bounded above by the ell_{s_k} norm; and evaluation identifies E^N isometrically with (X_0^N)*.
2. `path:bounded`, `path:rigidity`: each actual infinite coded path is a norm-at-most-one functional on E^N. For finitely many distinct paths in one family, deleting finite initial pieces produces tails with the ell_{q_t} upper estimate. The deleted pieces lie in X_0^N.
3. `pair:exact`: in every admissible infinite block sequence, at every prescribed weight J and in every tail, there is a finite block y and a Type I piece phi of weight J with ||y||<=500 and phi(y)>=1/2. The piece is supported in the ordinal range of y and, in mixed mode, in its color range.
4. `branch:reduction` and the first, block-approximation part of the proof of `branch:separation`: for every infinite-dimensional closed F in E^N there are a nonzero limit ordinal gamma<=omega_1, a closed infinite-dimensional H, a bounded U:H->F, and a projection R equal either to P_{C_k}P_{<gamma} (pure case) or to P_{<gamma} (mixed case), with RU=I_H. All P_{<beta}|H, beta<gamma, are strictly singular. In mixed mode all color projections on H are strictly singular as well. There are admissible finite blocks z_i supported below gamma and unit h_i in H such that ||z_i-h_i||<epsilon_i and sum epsilon_i<=1/32000. The map V z_i=h_i satisfies

       ||V-I|| <= eta=1/8000,       ||V||<=1+eta.

   All paths in this family supported below gamma obey P R=P, and hence P U h=P h. For the new argument we need the prescribed-weight operation and this lift, rather than the source's subspace-dependent full binary tree of paths.
5. `twist:lemma`: with Y a closed isometric predual of E, Q:E*->W=E*/Y, and a map B:E*->W satisfying ||B||<=1/10, B*(W*) subset J_E(E), and B(E*) subset closure B(Y), the space X=ker(Q-B) is a Banach predual up to isomorphism: restriction E->X* is an isomorphism, and closure B(X)=closure B(Y).
6. `ev:criterion`, `ev:finite-sum`, `ev:fields`: a separable infinite-dimensional quotient supplies a separable infinite-dimensional closed dual subspace with norm-separable evaluations; two real no-SQ spaces have a no-SQ finite direct sum; complexification of a real no-SQ space is again a counterexample.

No improved constant or strengthening of these interfaces is needed. In particular, the exact-pair argument, its Ramsey estimates, path rigidity, and the entire graph/predual argument are paid source operations.

## 2. Completion and finite-construction compatibility

**Lemma 2.1.** Suppose M subset N subset N' are forcing universes with the same omega_1 and with the fixed ground data above. The finite rational norming expressions, valid finite path data, and the norm on D are identical in these universes. There is a canonical isometric embedding E^N -> E^{N'}, which respects all the source coordinate projections. A bounded map between separable subspaces coded in N extends, with the same norm, to the closures of those subspaces in N'. Identities of such maps persist on these closures.

**Proof.** Every expression admitted to K is produced by finitely many operations on finitely supported rational arrays and natural-number metadata. A finite expression uses only finitely many ordinals below omega_1, rational coefficients, and integers; all those objects already belong to M. Validity is checked by the fixed ordinal/color orders, the fixed finite-closure maps and coding injections, and finite numerical inequalities involving the fixed parameters. It has the same meaning in all three universes. If a valid expression is found in N', its finite syntactic witness belongs to M and passes the same tests there. Conversely every expression in M is still valid. The same argument applies to a finite path together with its declared weights and metadata. The norming sets need not be countable globally for this conclusion.

For d in D, the set of values {|f(d)|:f in K} is a ground-model set of rationals. Its supremum is determined by its rational cut, which is unchanged. Thus ||d|| is unchanged. The norm inequality ||d||<=||d||_1 shows that completing D gives the same real Banach space as first allowing finite real coefficients and then completing, internally in each universe.

Represent an element of E^N by a Cauchy sequence in D in N. In N' this sequence is still Cauchy, because all its distances are the same, and defines an element of E^{N'}. Two sequences have the same limit exactly when their pairwise distances tend to zero, which is also unchanged. This defines an isometric embedding. Coordinates and the source projections commute with these embeddings, first on D and then by limits.

For a separable N-subspace, a countable dense set and its rational span determine its final closure. A bounded map on it is determined by its values on that dense set; its norm is the supremum over rational finite combinations from the dense set, so the norm does not increase or decrease on completion. It therefore extends uniquely. An identity true on the dense set remains true by continuity. We do not assert that E^N or an internally closed N-subspace is complete or closed as an external subset of E^{N'}. We take its closure in N' when needed. Nor do we assert preservation of strict singularity or weak convergence. Those properties will only be used inside the intermediate universe that supplies the block data. QED.

## 3. Countable path forcings and ground-model reservations

A pair (gamma,t) is called admissible here if gamma is a nonzero countable limit ordinal and one of the following holds:

* t=k is pure and C_k intersect gamma is cofinal in gamma;
* t=* is mixed and, for every beta<gamma and l in N, there is alpha with beta<alpha<gamma and col(alpha)>l.

These are ground conditions on ground sets, absolute to our extensions. Let T_{gamma,t} consist of the empty path and all finite actual paths of family t whose supports lie below gamma. In a pure family their supports lie on C_k. Order by end extension of the full data (piece, declared weight, metadata). In mixed mode require the same mixed succession as the source. These are precisely valid source finite paths; the tree imposes no new norming rule.

**Lemma 3.1.** T_{gamma,t} is a countable tree with countably infinitely many immediate successors at every node. It is forcing-equivalent to one Cohen real by a ground-model coding. A generic branch is an actual infinite path whose support has supremum gamma.

**Proof.** There are countably many finite rational arrays below a countable gamma, and countably many weights and metadata. Thus the tree is countable. Given a finite prefix, its next weight is the source sigma-value, or any chosen initial weight when the prefix is empty. Pick a coordinate alpha below gamma beyond its support, on C_k in pure mode, or beyond its largest color as well in mixed mode. Admissibility guarantees such a coordinate. If the prescribed weight is j, the expression

    phi = (1/m_j)e_alpha*

is a valid Type I piece with one coordinate child in the specified family. Choose metadata p larger than the preceding metadata and at least j and the rho-maximum of the new finite union of supports. There are infinitely many possible p. These give infinitely many distinct immediate successors. Every such successor admits further extensions by the same argument. All valid immediate successors form a countably infinite set.

In M choose, for every node a, a bijection from N to its immediate successors. Recursively these bijections identify the tree with N^{<N}. The map

    (n_0,...,n_{r-1}) -> 1^{n_0}0 ... 1^{n_{r-1}}0

identifies N^{<N} with the dense binary subtree consisting of the empty string and all finite binary strings ending in 0. It preserves extension and incompatibility. This is an explicit dense Cohen coding, so no extra generic-existence principle for a special path forcing is being invoked.

For each n the nodes of length at least n are dense. For every beta<gamma the nodes with a coordinate above beta are dense, using the one-child extension just described. Hence the generic union is infinite and has support cofinal in gamma. Every finite prefix is a valid source prefix. The union is therefore an actual path, with all the source's norm bounds. In mixed mode its colors also tend to infinity, either directly from strict mixed succession or from the corresponding dense sets. QED.

There are at most omega_1 admissible pairs. Fix in M an injection

    r : {(gamma,t,xi): (gamma,t) admissible, xi<omega_1} -> lambda.

The distinct Cohen coordinate r(gamma,t,xi), read through the fixed coding of Lemma 3.1, gives a path P_{gamma,t,xi}. Put

    A_t = {P_{gamma,t,xi}: (gamma,t) admissible, xi<omega_1}.

This is a set defined in M[G], of cardinality at most omega_1, before any subspace F is considered. All its members are actual paths of family t in E^{M[G]}. Paths at different gamma have different support suprema. Two paths at the same (gamma,t) and different reserved coordinates are distinct: the set of pairs of finite prefixes that are incompatible is dense in T_{gamma,t} squared, since two comparable prefixes can be extended to incompatible ones. Product genericity meets it. Thus the reservation also gives genuinely distinct path data where required. The construction of B below could in any event use the sets A_t without repetitions.

## 4. Capturing every new separable subspace

We recall and prove the exact elementary forcing facts we need. Add(omega,lambda) is ccc: for an uncountable family of finite conditions, the finite domains have an uncountable Delta-system subfamily; thin further so their values on the finite root agree. Two remaining conditions have a common extension given by their union. Thus there is no uncountable antichain. In particular omega_1 and all cardinals are preserved. The usual proof of cardinal preservation uses the countable sets of possible ordinal values on maximal deciding antichains; it is also read in the primary forcing reference recorded in the packet.

A name for a countable sequence with values in a ground-model set is supported by countably many Cohen coordinates. Indeed, for each sequence position choose a maximal antichain deciding its value (below a condition forcing that it has the required type, with a default value elsewhere if needed). Every antichain is countable. The union of the finite coordinate supports of all these countably many conditions is a countable set S in M; include the support of the initial condition too. Each decided value is a ground object. The resulting name is an Add(omega,S)-name.

For disjoint ground coordinate sets S and A, Add(omega,S union A) is exactly the product Add(omega,S) x Add(omega,A), by restriction and union of finite functions. A generic for the A-factor is generic over M[G|S]. To see this for a dense set D named over the S-factor, the pairs (p,q) for which p forces q in D form a dense subset of the product: below (p_0,q_0), strengthen p_0 to decide a q<=q_0 that the name asserts belongs to D. Meeting that product dense set proves the assertion. The same proof applies to A consisting of any two coordinates, grouping all other coordinates as another factor.

**Lemma 4.1.** For every separable infinite-dimensional closed F subset E^{M[G]}, there are a countable ground set S subset lambda, an intermediate universe N=M[G|S], and a separable infinite-dimensional internally closed F_N subset E^N whose image has closure F in E^{M[G]}.

**Proof.** Choose a countable dense sequence (x_n) in F. For every n,m choose d_{n,m} in D with ||d_{n,m}-x_n||<2^{-m}. The doubly indexed sequence consists of elements of the ground set D, hence has a name supported by some countable S by the preceding argument. Its norm-Cauchy properties are absolute by Lemma 2.1. Inside N take each limit x_n^N in E^N and then its closed real linear span F_N. The canonical embedding sends x_n^N to x_n. Its final closure is consequently F.

F_N is infinite-dimensional in N. Otherwise an N-finite basis for F_N, together with approximation by rational combinations, shows that all x_n lie in the corresponding finite-dimensional final span. That span is closed and contains F, contrary to its infinite dimension. Thus the full source subspace reduction can be applied inside N. QED.

Apply Source323's reduction and block approximation inside N to F_N. It gives gamma,t,H,U,z_i,h_i,V as in Section 1. This gamma is countable: the countable dense sequence of F_N has countable coordinate support, bounded below omega_1, so some countable initial-segment projection is already the identity on F_N. The least non-strictly-singular projection selected by the source has a nonzero limit ordinal gamma below that bound (or at most that countable bound).

**Lemma 4.2.** The resulting (gamma,t) is admissible in the ground sense of Section 3.

**Proof.** In pure mode, H is supported on C_k below gamma. If C_k intersect gamma were not cofinal, an earlier initial projection would be the identity on H, contradicting its strict singularity inside N.

In mixed mode, suppose for some beta<gamma and l there were no coordinate beyond beta of color greater than l. Increase beta within gamma if necessary to cover the endpoint. All coordinates below gamma then lie either below this beta or in the finitely many colors 0,...,l. By `ev:small` applied inside N to the earlier projection and these finitely many strictly singular color restrictions, choose h in H of norm one with

    ||P_{<beta}h|| + sum_{k<=l} ||P_{C_k}h|| < 1/2.

But h is the sum of its early part and its remaining parts in those colors. Contractivity of the tail ordinal projection gives ||h||<1/2, a contradiction. This proves the required mixed admissibility. Since it is a statement about fixed ground ordinals and colors, it holds in M as well. QED.

In the full extension extend U and V to the closures of their intermediate spaces using Lemma 2.1. The bounds ||V-I||<=eta and ||V||<=1+eta and the identity RU=I persist. All finite blocks z_i remain admissible. No preservation of the intermediate strictly singular operators is used.

## 5. The additional dense-separation operation

Fix the data supplied inside N above. The countable tree T=T_{gamma,t} is a ground-model object; its set of nodes is unchanged in N and in M[G]. Write [T] for the actual infinite branches, with their resulting norm-at-most-one functionals.

**Lemma 5.1 (dense pair separation).** There is a dense open subset D_F of T x T belonging to N such that if two branches extend a pair in D_F, then in every later completion with the same ground data their restrictions to the final closure of F_N differ in norm by at least

    delta_F = 3 / (8 * 500 * ||U|| * (1+eta)),   eta=1/8000.

**Proof.** First choose the following cofinal refinement of the source block approximation, once inside N and independently of the path conditions.

Here is the needed cofinal refinement, to remove any implicit tail assumption. Inside N fix an increasing cofinal sequence (beta_i) in gamma. When constructing h_i and z_i by the source's small-restriction step, require their lower ordinal cutoff to exceed beta_i as well as all earlier supports. In mixed mode require their lower color cutoff to exceed i as well as all earlier colors. These add only one earlier ordinal projection and finitely many color restrictions to the same source step; strict singularity and `ev:small` supply the unit vector. Finite approximation and the same prescribed epsilon_i give exactly the same norm bounds and ||V-I|| estimate. Thus the resulting blocks are cofinal in gamma and, in mixed mode, in color. The source operation fully permits these larger cutoffs. We henceforth use this refinement. It is made in N before D_F is defined.

Now let p,q be arbitrary nodes. Take a tail of (z_i) strictly after all their support coordinates, and after all their colors in mixed mode; the refinement guarantees such a tail. Let J be the next weight required after p, or choose any initial weight if p is empty. Apply `pair:exact` inside N in the chosen block tail. It gives y in the finite real span of finitely many of those z_i and a rational Type I piece phi of weight J with

    ||y||<=500,       phi(y)>=1/2,

with the source support/range conditions. Append phi to p, assigning metadata larger than its preceding metadata and at least J and the rho-maximum of the new finite support union. This is a valid next path node, even though its coefficients in y may be new reals: phi and its finite validity witness are ground finite rational objects by Lemma 2.1.

Now append to this new prefix a one-child Type I piece at a coordinate strictly beyond the ENTIRE support of y, and beyond its whole color range in mixed mode, with the next prescribed weight and valid larger metadata. Call the resulting prefix p'. Append a corresponding legal one-child piece to q, also strictly beyond y, with q's own prescribed next weight, to obtain q'. These choices exist by admissibility of (gamma,t). They need not use the same weight or coordinate. The extra dummy pieces are essential: phi's maximum support need not be the maximum support of y, so stopping just after phi would not protect the evaluation on y from all future pieces.

For ANY infinite branches P extending p' and Q extending q', the old prefix pieces lie before y, and all pieces after their dummy barriers lie after y. Hence

    P(y)=phi(y)>=1/2,        Q(y)=0.

These equalities are determined by finite supports; they are valid also for branches added after N. Both paths are supported below gamma and on C_k in pure mode, so PR=P and QR=Q. On the final closure of H this gives PU=P and QU=Q by RU=I. Therefore

    (P-Q)(UVy) = (P-Q)(Vy)
               >= (P-Q)(y) - 2||Vy-y||
               >= 1/2 - 2 eta ||y||
               >= 3/8.

Also ||UVy||<=500||U||(1+eta). The norm bound on P and Q, source support identity, and extended operator bounds have all been verified in the final completion. Dividing proves the asserted delta_F separation.

Define D_F to consist of all pairs extending some pair (p',q') obtained by this construction, with y,phi and the associated finite support barriers chosen inside N. It is a set in N, is upward-closed under stronger conditions, and is dense because we started with arbitrary p,q. Every pair in it retains one such finite witness and the proved separation. It is immaterial whether the set of possible witnesses has a simple descriptive complexity: it is a dense subset of a countable forcing belonging to N, exactly the kind of set met by a generic filter. QED.

The cofinal refinement in this proof is part of the post-freeze proof development. It does not change any frozen hypothesis, conclusion, or constant. It makes explicit an additional compatibility condition that was implicit in the prefreeze phrase “beyond both prefixes.”

## 6. Simultaneous separation on all new subspaces

**Lemma 6.1.** The sets A_t constructed in Section 3 satisfy the stronger construction assertion in the frozen statement.

**Proof.** Let F be ANY separable infinite-dimensional closed subspace of E^{M[G]}. Use Lemma 4.1 to capture its dense sequence in N=M[G|S], and use Lemmas 4.2 and 5.1 to choose the admissible pair (gamma,t) and D_F in N. Only countably many of the distinct reserved coordinates r(gamma,t,xi), xi<omega_1, belong to S. Thus

    I_F={xi<omega_1: r(gamma,t,xi) not in S}

has cardinality omega_1 in the full extension.

For any distinct xi,zeta in I_F, their two Cohen coordinates are product-generic over N by the factorization in Section 4. Their ground dense codings into T carry this to a T x T-generic pair over N. It therefore meets D_F. Lemma 5.1 gives

    ||P_{gamma,t,xi}|F - P_{gamma,t,zeta}|F|| >= delta_F.

The same delta_F works for ALL distinct xi,zeta in I_F, since D_F and its numerical bound were chosen from F_N before either coordinate is considered. Consequently these are omega_1 distinct separated restrictions from A_t.

This argument applies to every F in the full extension, including subspaces chosen using the entire family A_t or the later operator B. The countable-name support argument is about the dense sequence that codes the individual F; it does not require its definition to mention only countably many generic coordinates. There is no circular independence assumption about F and B. No intersection of omega_1 dense sets inside one recursively chosen generic is performed: each pair of independent coordinates is already generic for all dense sets of its intermediate universe.

All A_t, F, I_F, and restrictions are internal sets in the full extension. The intermediate-universe argument proves the full internal universal quantifier over F. QED.


## 7. The selected paths satisfy both operator interfaces

We now work entirely inside M[G], and omit universe superscripts. Set E=E^{M[G]}, Y=X_0, W=E*/Y, and let Q:E*->W be the quotient map. Let A_t be the sets just constructed.

For each t define, first on finitely supported coefficient families,

    S_t : ell_{q_t}(A_t) -> W,      S_t e_P = QP.

This extends to a contraction. Indeed, for finitely many distinct actual paths, `path:rigidity` removes finite prefixes to leave tails with pairwise disjoint active weights. Every deleted prefix belongs to Y, so it does not change the coset. The source Type II rule bounds every rational ell_{q_t}-unit combination of finite tail segments. Passing to the bounded path limits, applying Q, and approximating real coefficients gives

    ||sum_P a_P QP|| <= (sum_P |a_P|^{q_t})^{1/q_t}.

This is the proof of `twist:path-map`, restricted to A_t; it never uses CH or a listing of all paths. Completion gives S_t.

Since |A_t|<=aleph_1, choose injections iota_k:A_k->C_{k+1} for pure families and iota_*:A_*->C_1 for the mixed family, with mutually disjoint ranges. Split C_1 into two sets of size aleph_1 to accommodate the mixed family and pure family 0. Other pure families already use distinct colors. These are injections of path DATA, not an assertion that every functional in E* has a label.

Write s_src(k)=s_{k+1} and s_src(*)=s_1. The source exponents satisfy

    s_src(t)' <= q_t,       q_t' <= s_src(t).

For y in E* put

    b_t(y) = (y(e_{iota_t(P)}))_{P in A_t}.

The coordinate ell_{s_src(t)} upper bound and finite-dimensional duality imply, by taking suprema over finite subsets,

    ||b_t(y)||_{s_src(t)'} <= ||y||.

The natural inclusion ell_p(A)->ell_q(A), p<=q, has norm at most one, including for arbitrary index sets; hence ||b_t(y)||_{q_t}<=||y||. This proves the coefficient-side compatibility, rather than assuming that arbitrary bounded coefficient families can be summed against path cosets.

Enumerate the countably many families as t_1,t_2,... and choose tau_{t_n}=2^{-n}/10. All tau_t are positive and sum_t tau_t=1/10. Define

    B y = sum_t tau_t S_t b_t(y),       y in E*.

The series converges absolutely in W and ||B||<=1/10. Set

    V = closed real span {QP: P in A_t, t a family} in W.

Finite approximation in each ell_{q_t} space gives B(E*) subset V. Conversely, disjointness of all label ranges gives the exact identity

    B(e_{iota_t(P)}*) = tau_t QP.

Thus V=closure B(Y), and in fact closure B(E*)=V as well. This verifies the exact range condition of the source twisting lemma. No equality with the coset span of unselected paths is asserted or needed.

For the adjoint-side compatibility, take an arbitrary w* in W*. The coefficient family S_t*w* lies in ell_{q_t'}(A_t), with norm at most ||w*||. Since q_t'<=s_src(t), it also lies in ell_{s_src(t)} with no larger norm. The source coordinate upper estimate makes the series

    v_t = sum_{P in A_t} (S_t*w*)(P) e_{iota_t(P)}

converge in E, with ||v_t||<=||w*||. Its support is countable because q_t'<infinity. The vector v=sum_t tau_t v_t converges in E and has norm at most ||w*||/10. Testing against an arbitrary y in E*, using the finite-sum identity and then the norm-convergent series, gives

    (B*w*)(y) = w*(By) = y(v).

Consequently B*w*=J_E v and B*(W*) subset J_E(E), exactly as required. Both exponent inequalities have therefore been used with their correct directions; the generic selection has not altered the source functional-analytic compatibility.

## 8. Twisting and exclusion of every separable infinite-dimensional quotient

Apply `twist:lemma` with the just verified data and define

    X_R = ker(Q-B) subset E*.

It is a closed real subspace of the Banach space E*, and hence Banach. Restriction

    R_X : E -> X_R*,        (R_X e)(x)=x(e),

is an isomorphism, and closure B(X_R)=V.

For clarity, the source's mechanism here is stronger than merely constructing an algebraic dual pairing. The quotient perturbation Q-B is onto by a convergent lifting series. In E** the annihilator of its kernel is the graph

    {Q*w* - B*w*: w* in W*}

over Y-perp, with graph values in J_E(E). Since E=Y* isometrically, E**=Y-perp direct-sum J_E(E). The graph gives the restriction isomorphism onto X_R*. The source then factors B through Q-B modulo closure B(X_R); its norm is smaller than one, whereas a nonzero quotient map on closure B(Y) has norm one. This proves closure B(X_R)=V. All of this is the paid source lemma, applied with every hypothesis verified in Section 7.

Let F subset E be any separable infinite-dimensional closed subspace. Define

    C_F = closure {y|F: y in Y} subset F*.

This is separable: a countable dense subset of F has supports in a common countable set A subset omega_1; coordinate functionals outside A vanish on F; and all Y-restrictions lie in the closed span of the remaining countably many coordinate restrictions.

Restriction induces a well-defined contraction

    T_F : W -> F*/C_F,      T_F(Qy)=y|F+C_F.

To verify boundedness with the quotient norm, replace y by y-y_0 for y_0 in Y, restrict, and take the infimum. If closure T_F(V) were separable, its inverse image under F*->F*/C_F would be separable. Indeed, choose countably many lifts of a dense set in that quotient image and a countable dense set in C_F. Given a point of the inverse image, approximate its coset by a chosen lifted coset; the quotient norm makes the residual close to C_F; approximate that residual by the chosen dense subset. The countably many sums are dense. This uses the closed inverse image of the closure of T_F(V), so all its members have lifts in F* and the quotient norm is the appropriate one.

That inverse image contains every P|F for P in every A_t. Lemma 6.1 supplies aleph_1 of these restrictions separated by delta_F>0. A separable metric space has no uncountable positive-separated subset (use a countable dense set and balls of radius less than delta_F/2). We have a contradiction. Therefore T_F(V) is nonseparable.

Since B(X_R) is dense in V and T_F is continuous,

    closure T_F(B(X_R)) = closure T_F(V).

For x in X_R, Qx=Bx. Thus the set of evaluations {x|F:x in X_R} has the nonseparable image T_F(B(X_R)) in F*/C_F and is itself nonseparable.

Now take any separable infinite-dimensional closed F' subset X_R*. Its inverse image F under R_X is separable, infinite-dimensional, and closed in E. Composition with R_X|F identifies the two evaluation families by a bounded linear isomorphism, preserving norm separability. Thus every such F' has nonseparable X_R-evaluations. The necessary direction of `ev:criterion` rules out a bounded surjection from X_R onto a separable infinite-dimensional real Banach space. Equivalently, every separable Banach quotient X_R/M with M closed is finite-dimensional. This proves the real quotient assertion with its full universal quantifier.

## 9. Density and the complex space

The ground rational finite vectors form a dense set in E of cardinality aleph_1. The coordinate vectors (e_alpha)_{alpha<omega_1} are pairwise at distance at least one, by the source lower coordinate estimate. Hence dens E=aleph_1. The isomorphism E->X_R* yields

    dens X_R* = aleph_1.

Choose a norm-dense set D* in the unit sphere of X_R* of cardinality aleph_1. For each f in D*, choose x_f in the unit sphere of X_R with |f(x_f)|>1/2. The closed span of these x_f is X_R: otherwise Hahn--Banach supplies a unit g annihilating their span, and an f in D* with ||f-g||<1/2 gives |f(x_f)|<1/2, a contradiction. Rational finite combinations give dens X_R<=aleph_1. It cannot be separable, since it is infinite-dimensional (its dual is isomorphic to E) and would be its own forbidden quotient. Therefore

    dens X_R = dens X_R* = aleph_1.

Define the complexification X_C=X_R+iX_R with the source norm

    ||x+iy||_C = sup_theta ||cos(theta)x - sin(theta)y||.

Its underlying real space is isomorphic to X_R direct-sum_infinity X_R, with the source two-sided norm comparison. It is a complex Banach space. `ev:finite-sum` says this real sum has no separable infinite-dimensional real quotient. Any complex-linear bounded surjection onto a separable infinite-dimensional complex Banach space would also be a real-linear surjection of the underlying real spaces onto a separable infinite-dimensional real space. Hence no such complex quotient exists.

The equivalence with the finite real sum gives dens X_C=aleph_1. For the dual density, recall the isometric real-linear bijection between the real dual of a complex space's underlying real space and the underlying real space of its complex dual:

    g -> [z -> g(z)-i g(iz)],       inverse f -> Re f.

Complex linearity is direct, and phase rotation in the unit ball proves norm equality. The real dual of the underlying real X_C is isomorphic to X_R* direct-sum_1 X_R*, which has density aleph_1. Thus dens X_C*=aleph_1 as well. The complex no-quotient and both density assertions in the frozen statement are proved.

## 10. Forcing quantifiers and relative consistency

The construction applies to every ground cardinal lambda>=aleph_1, with no assumption about the ground continuum or about an existing counterexample. The only ground analytical objects fixed in advance are the source's finite rational coordinate/norming data. The Banach completions E, X_0, their full duals, W, B, and X_R are formed internally in the complete forcing extension. In particular, the proof does not claim that a ground-model Banach space remains complete after adding reals, nor that ground weak-star compactness or strict singularity is automatically preserved.

The source operations through the block reduction are applied anew inside the intermediate universe N. Only finite rational validity, norm identities on coded dense sets, and continuous extensions are transported to the full extension. The dense-set argument then quantifies over every final separable subspace via its countable supported name. This proves the asserted forcing statement

    1_Add(omega,lambda) forces the simultaneous real/complex conclusion.

The notation M and M[G] can be eliminated by the definable forcing relation. The preceding arguments use names, countable maximal antichains, product factorizations, and ZFC proofs of the stipulated analytical interfaces; thus they constitute a proof in the forcing calculus. No existence of a transitive set model of all ZFC is a hypothesis. Relative-consistency conclusions have the usual syntactic/finite-fragment interpretation, the same convention as Source323's models section.

If lambda^(aleph_0)=lambda in the ground model, the extension has continuum exactly lambda. It has at least lambda reals, since its coordinate generics are pairwise distinct: for any two coordinates and any condition, decide a fresh bit differently. For the upper bound, each real has a name specified by countably many countable deciding antichains; there are at most |P|^{aleph_0}=lambda such descriptions. Since P is ccc, lambda retains its cardinal identity. This proves the continuum clause without a regularity assumption beyond the explicitly imposed cardinal arithmetic.

From Con(ZFC), pass by the constructible-universe argument to Con(ZFC+GCH), then force with Add(omega,aleph_2). GCH gives (aleph_2)^{aleph_0}=aleph_2. We obtain

    Con(ZFC) -> Con(ZFC + c=aleph_2
       + real and complex no-SQ spaces with dens X=dens X*=aleph_1).

On the positive side, Source323's `intro:small-density` proof supplies, from Con(ZFC), a model of MA+c=aleph_2 in which every real and complex Banach space of norm density exactly aleph_1 has an infinite-dimensional separable quotient. Its use of dens<b and the real-to-complex transfer is explicitly paid upstream.

Consequently, over ZFC+c=aleph_2, the density-aleph_1 separable-quotient assertion and its negation are each relatively consistent from Con(ZFC), over each field and with simultaneous signs for both fields. This proves the entire frozen consistency scope. We make no positive assertion for unrestricted Banach densities at this fixed continuum and no claim to reduce the source's measurable-cardinal assumption for the unrestricted positive model.

## 11. What is and is not new in this author proof

The source already constructs the coordinate dual, proves weak-Cauchy block selection, prescribed-weight pairs and arbitrary-subspace lifting, bounds finite path tails, and twists a predual when enough path cosets can be coded. The classical Cohen facts already provide countable supports and mutually generic pairs. Neither collection alone, at its displayed interface, supplies the selected path family used here.

The additional operation is Lemmas 4.1--6.1: produce one aleph_1-sized family BEFORE F is specified, turn exact pairs into dense conditions in TWO full path forcings using support barriers, and then handle every new F by intermediate completion and the remaining independent coordinates. The cofinal-block refinement and the two dummy barriers are part of the compatibility proof. The result changes the source's CH-only negative model into a theorem about every uncountable Cohen extension and yields the two signs at the same continuum aleph_2. This describes the proposed residual; it is not a contribution grade or a claim of worldwide priority.

No mathematical obligation within the frozen statement is intentionally left conditional beyond the explicitly stipulated source and ordinary ZFC forcing theory. Independent adversarial correctness review and separate contribution review remain to be performed by the parent workflow. No formal proof for this nominee has been constructed or claimed.
