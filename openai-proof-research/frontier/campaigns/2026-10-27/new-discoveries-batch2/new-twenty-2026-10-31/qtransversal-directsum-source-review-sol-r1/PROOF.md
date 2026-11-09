# Independent ordinary proof audit: MathDB 373611

Verdict: full ordinary PASS for the exact source-defined operation, including arbitrary given presentations and every mixed subspace. This is an independent personal verification of the proposed mathematics, not two independent reviews merely because there are two derivations. No mathematical program, formal system, experiment or enumeration was used. Credit remains zero. The exact theorem also has an authenticated public July 2026 proof; see REVIEW.md.

## Literal endpoint and assumptions

Let F=F_q be any finite field (q any prime power), E1,E2 finite-dimensional F-vector spaces, A=(A_i)_{i in [k]}, B=(B_j)_{j in [l]} arbitrary finite indexed families of subspaces presenting M1,M2 in Fulcher Definitions 2.12-2.13. Repetitions and redundant slots are allowed. Write E=E1 directsum E2 and let pi1,pi2 be its projections. Define precisely

D=((A_i directsum E2)_{i in [k]},(E1 directsum B_j)_{j in [l]}).

For every subspace X<=E, the rank of the transversal q-matroid presented by D is

r_D(X)=min_{Y<=X}(r_A(pi1Y)+r_B(pi2Y)+dim X-dim Y).

This is Fulcher Definition 2.7, so D presents M1 directsum M2. It is equality for the given families, not existence of an unspecified presentation. Fulcher Notation 4.3 p9 defines D under arbitrary presentations before the coordinate theorem. Theorem 4.7 p11 displays it again and Conjecture 4.8 uses that notation. The malformed operation bytes in the frozen MathDB literal are retained untouched; their interpretation comes from these actual displays. No correction earns credit.

## Hall bridge and the induced-rank envelope

For any finite family C=(C_i)_{i in [s]} on V put f_C(W)=#{i: W is not contained in C_i}. Fulcher's partial q-transversal definition means that EVERY vector basis of I has an injection to slots avoiding the matched subspaces; the injection may depend on the basis. It does not mean that some basis works or that a fixed matching works for every basis.

This is equivalent to f_C(W)>=dim W for every W<=I. Forward: extend any basis of W to a basis of I, take its avoiding injection, and restrict to that basis of W. Its dim W distinct slots all fail to contain W. Reverse: for any basis (b_a) of I form neighbor sets N_a={i:b_a notin C_i}. For J a subset of its indices, subspace closure gives union_{a in J}N_a={i:span(b_a:a in J) not<=C_i}; this union has cardinality at least |J|. Hall gives the required injection. Since the initial basis was arbitrary the universal-basis property follows. This reproduces the full substance of Saaltink Theorem 15 pp8-10, not an assumed convention. Definition 14 literally prints 'a dimension n subspace' for a partial transversal; that cannot literally describe independent subspaces (it excludes zero when n>0). The proof uses arbitrary m-dimensional T, and Fulcher Definition 2.12 explicitly removes that dimension restriction. We rely on the actual proof and Fulcher definition, not on an invented repair of Saaltink's sentence.

Saaltink Section 3.1 pp6-7 states the induced rank formula

R_C(S)=min_{W<=S}(f_C(W)+dim S-dim W).                 (1)

Its hypotheses hold: each g_i(W)=1_{W not<=C_i} is zero at zero, monotone and submodular. If U,V both lie in C_i the submodular inequality is all zero; if exactly one lies in it both sides are one; if neither lies in it the right side is two and bounds the left side. Sum over slots. The summands have rank at most one, with zero rank when C_i=V (so the printed 'rank 1' terminology need not exclude a whole-ambient slot). Empty sums give f=0. Saaltink Corollary 16's union is induction from the sum of ranks on ONE lattice, not a disjoint-set union. No representability is involved.

For completeness the envelope itself is justified here. Every minimum is attained because the finite-dimensional space over a finite field has finitely many subspaces. R_C is nonnegative, at most dim S by W=0, and monotone: if S<=T and W<=T, use S intersect W in the first minimum; its f value is at most f(W), and dim S-dim(S intersect W)<=dim T-dim W by the natural injection into T/W. For submodularity choose minimizers U<=S,V<=T, use U+V and U intersect V in the minima at S+T and S intersect T, and apply dimension modularity and submodularity of f. This yields R_C(S+T)+R_C(S intersect T)<=R_C(S)+R_C(T). Finally R_C(I)=dim I iff every W<=I satisfies f_C(W)>=dim W, hence iff I has the original universal-basis independence.

A q-matroid rank is determined by its independent spaces: if independent I<=S has rank below rank S, some line L<=S increases its rank, since otherwise repeated submodularity would make all sums with lines rank-constant up through S. Adding that line preserves independence because rank increases by one and dimension by one. Iteration from zero reaches an independent space of dimension rank S. Conversely monotonicity bounds every independent dimension by rank S. Thus (1) is exactly the rank of the original definition. This closes the independence-to-rank bridge without assuming the desired direct-sum theorem. The same argument recovers Saaltink Theorem 18 from the next formula: independence is equivalent to dim(T intersect C_I)+|I|<=s for every I, including I empty.

## First route: intersection minima

Put C_I=intersection_{i in I}C_i and C_empty=V. Then

r_C(X)=min_{I subset [s]}(dim X-dim(X intersect C_I)+s-|I|).       (2)

For W<=X set I(W)={i:W<=C_i}. Its term in (1) is at least the I(W) term in (2), since W<=X intersect C_{I(W)}. Hence min(1)>=min(2). Conversely for every I use W=X intersect C_I in (1); f_C(W)<=s-|I|, so min(1)<=that I term; minimizing gives the other inequality. Equality f_C(W)=s-|I| need not hold and was not used. For s=0 the sole term I=empty is zero, agreeing with (1) at W=X.

Write A_I=intersection_{i in I}A_i, B_J similarly, with empty intersections equal to their own entire ambient spaces. Each subset of the concatenated slot set is uniquely a pair (I,J); intersection of its padded entries is A_I directsum B_J. Therefore (2) gives

Q(X)=r_D(X)=min_{I,J}(dim X-dim(X intersect (A_I directsum B_J))+k-|I|+l-|J|).       (3)

Let d(X) denote the right side of the endpoint. Substitute (2) into each component rank. Finite nonempty index sets of choices permit commuting the three minima; for fixed Y<=X,I,J the term is

dim X-dim Y + dim(pi1Y)-dim(pi1Y intersect A_I)
 +dim(pi2Y)-dim(pi2Y intersect B_J)+k-|I|+l-|J|.

Consider the actual linear map L:Y -> (E1/A_I) directsum (E2/B_J), y |-> (pi1y+A_I,pi2y+B_J). Its kernel is Y intersect (A_I directsum B_J). Its image is contained in the direct sum of its two marginal images, so dim im L is AT MOST the sum of the two marginal image dimensions. Rank-nullity thus bounds the displayed term below by

dim X-dim(Y intersect (A_I directsum B_J))+k-|I|+l-|J|,

which is at least the corresponding I,J term of (3). Every expanded term is at least Q(X), so d(X)>=Q(X). Conversely fix I,J and choose Y=X intersect (A_I directsum B_J). Its two quotient images vanish; the same expanded term is exactly that I,J term of (3). Thus d(X)<=every such term and d(X)<=Q(X). Equality follows. No assumption that Y or X splits, and no equality of joint and marginal image dimensions, has entered.

## Second route: nested minimizers

Directly from the padded family, f_D(Z)=f_A(pi1Z)+f_B(pi2Z). Call its envelope Q(X). From (1) with W=P, r_A(P)<=f_A(P), and similarly for B. Inserting Y=Z in d and then minimizing over Z gives d(X)<=Q(X).

Conversely fix Y<=X, P=pi1Y, R=pi2Y. Choose minimizers T1<=P,T2<=R in (1) for the component ranks. Set Z=Y intersect (T1 directsum T2). The map Y -> (P/T1) directsum (R/T2) has kernel Z, hence

dim Y-dim Z<=dim P-dim T1+dim R-dim T2.

Monotonicity gives f_A(pi1Z)<=f_A(T1) and f_B(pi2Z)<=f_B(T2). Use Z in Q to conclude

Q(X)<=dim X-dim Y+[dim P-dim T1+f_A(T1)]+[dim R-dim T2+f_B(T2)]
     =dim X-dim Y+r_A(P)+r_B(R).

This holds for every Y; minimize to get Q(X)<=d(X). This route uses exact restrictions of the original projections, not quotient splittings or independent-projection assumptions. The two routes verify the same theorem and yield no extra outcomes.

## Adversarial reasoning checks (not experiments)

* Some-basis versus every-basis: in F_q^2 take C=(L,L), L=span(e1). The basis (e2,e1+e2) avoids both slots and has an injection, but a basis containing e1 fails. Indeed (1) gives rank one on the plane by W=L, so the universal quantifier is essential, even in characteristic two.
* Naive embedding is wrong: if E1=E2=F_q and A=(E1),B=(E2), both factors have rank zero. The exact padded entries are both E and give rank zero. Naively embedding the original entries gives the two axes, whose presented q-matroid is the free plane. This is not the asserted operation.
* The sum of marginal quotient ranks need not equal the joint rank: take A_I=B_J=0 and Y a diagonal line. The sum is two while the joint rank is one. Our first route needs only the inequality in the correct direction. In the two free-line case d(X)=1 on a diagonal line, achieved at Y=0, even though the Y=X term is two.
* Empty families have rank zero, not free rank. A zero-rank summand plus a free one can still give positive rank on a diagonal line; a split-subspace-only proof misses this. Both formulas choose subspaces inside the actual mixed X and handle it.
* Whole-ambient slots contribute zero to f; adding one increases s and |I| together at an optimizing intersection, leaving the actual rank unchanged. Repeated proper slots count separately and can change the rank, so neither proof discards multiplicity or assumes minimality.
* X=0 yields zero. A zero-dimensional summand, k=0 or l=0, or both, gives the same formulas with unique zero projections/empty intersections. Loop spaces and nonminimal presentations impose no extra restriction. Only subspace containment, Hall, dimensions and rank-nullity were used, with no characteristic-dependent division or sign argument; every prime power including characteristic two survives.

The generality is therefore the full source conjecture under its finite-field standing assumptions. We claim neither a new representation theorem nor an infinite-field target nor independent formal verification.
