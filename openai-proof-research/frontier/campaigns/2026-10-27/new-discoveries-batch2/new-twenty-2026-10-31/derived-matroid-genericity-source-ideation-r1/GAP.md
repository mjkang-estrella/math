# MathDB355016 — precise remaining gap, credit zero

This is an ordinary handwritten investigation, not a solution of the full conjecture. No mathematical computation was executed. All claims below quantify over finite ground sets and arbitrary fields unless a field is specified. New-to-this-lane progress is not a novelty claim.

## Restored endpoint and construction

Let R be a matrix over F representing M on E, Q its row space, V=ker R=Q-perp. For S subset E put W(S)={v in V: supp(v) subset S}. Rank-nullity gives dim W(S)=n_M(S)=|S|-r_M(S). For each genuine circuit C of M, the space W(C) is one-dimensional and its nonzero elements have support exactly C. Choose q_C in this line. Changing each choice by its own nonzero scalar preserves all independence assertions. The Oxley–Wang matroid N has ground set C(M) and representing columns q_C.

Write s(A)=union of the circuits in A. A0 consists of A subset C(M) with |A|>n_M(s(A)). For a family H, epsilon(H) consists of H together with (P union Q) minus {c} for P,Q in H, P intersection Q not in H, c in P intersection Q. Upward closure adds supersets on C(M); min selects inclusion-minimal members. A_(i+1)=up epsilon(A_i), and A=union_i A_i stabilizes since C(M) is finite. The alternate circuit construction starts B0=min A0, iterates epsilon, and finally takes min of the union. The source prints an indexing blemish 'i>=1' for the recurrence while using the step from A0 throughout; the intended recurrence from i=0 is used here. Definition 4.1 also has a type-level shorthand H subset C where H must be a family of subsets. Neither blemish is treated as a solution.

The exact assertion is A subset D(N), for every representation R of every finite representable M, without a genericity hypothesis. Ground set is C(M), not E. Source weak order is delta M >= N precisely when D(delta M) subset D(N). Extra R-dependencies are allowed.

## A new mechanism relative to r361: whole supported-kernel spaces

**First-step lemma.** Every set in up epsilon(A0) is dependent in N. In particular a counterexample cannot have depth zero or one.

Proof. For A in A0 all its circuit vectors lie in W(s(A)), whose dimension is at most |A|-1. Supersets preserve dependence. Consider two initial parents P,Q in A0 with J=P intersection Q not in A0 and c in J. Put U1=W(s(P)), U2=W(s(Q)). Their intersection contains W(s(J)), because s(J) is contained in both supports. Since J not in A0,

    dim(U1 intersection U2) >= n_M(s(J)) >= |J|.

The dimension identity for the sum of two finite-dimensional subspaces now gives

    dim(U1+U2) <= (|P|-1)+(|Q|-1)-|J|
                  = |P union Q|-2.

All q_D with D in T=(P union Q) minus {c} lie in U1+U2. There are |P union Q|-1 of them, so T is dependent. This includes cases where the vectors on J are themselves dependent: their span is not substituted for W(s(J)). Taking upward closure proves the lemma. QED.

This goes beyond the source's initial dimension bound and r361's failed induction. It uses genuine circuit support semantics to replace the invalid assertion that J is represented-independent. It does not show that T belongs to A0: U1+U2 need not equal W(s(T)) or W(s(P) union s(Q)). Confusing these spaces would destroy the argument's scope.

## Sustained extension and exact obstruction at the next step

For every H in A1 the preceding proof constructs a subspace L_H of V containing its circuit vectors, of dimension <=|H|-1. An initial witness uses W(s(H)); an elimination witness uses U1+U2; when H is a proper superset of a witness add the lines F q_D of the additional circuits. Each added line increases dimension by at most one. These are genuine supported-kernel envelope certificates, not abstract arbitrary columns.

If for every legal pair P,Q in A_i one could choose such envelopes with dim(L_P intersection L_Q)>=|P intersection Q|, the same dimension proof would propagate to A_(i+1). This is a sufficient unproved condition, not assumed. At depth zero it holds because both envelopes contain W(s(J)). At depth one the envelopes can be sums of supported spaces, and containment of W(s(J)) has not been established.

There is a sharper necessary obstruction for any first failure. Suppose P,Q are already known R-dependent, J=P intersection Q is unmarked at that stage, and T=(P union Q) minus {c} is R-independent. Adding a single column q_c to the independent family T leaves relation-space dimension at most one. Because P is dependent there is a nonzero relation, so the relation space of the union is exactly one-dimensional. The relations supported on P and Q must be proportional. Their common nonzero support K lies in J and contains c (otherwise T is dependent). Thus J has exactly one relation and rank |J|-1, and each parent has exactly one relation and rank |P|-1 or |Q|-1.

If P,Q belong to A1 and L_P,L_Q are the certificates above, dimension forces L_P=span(q_D:D in P), L_Q=span(q_D:D in Q). Consequently

    dim(L_P intersection L_Q)= (|P|-1)+(|Q|-1)-(|P union Q|-1)
                               = |J|-1.

But J not in A1 implies J not in A0, so dim W(s(J))>=|J|. Therefore W(s(J)) cannot be contained in both envelopes. At least one full supported-kernel direction is missing from their overlap. This is the specific residual for a depth-two realization or for a proof excluding such realizations. Unmarked has never been replaced by R-independent.

No theorem currently supplies the required overlap property, and no actual M realizing the missing direction together with a legal depth-two derivation is supplied here. There is no full universal proof, finite refutation, or qualified dormant Pi candidate.

## Independent hand construction testing a stronger proposed invariant

The tempting invariant 'every minimal A0 family is cyclic in every represented derived matroid' is false. This is a diagnostic, not a counterexample to MathDB355016.

Take M=M(K4), vertices a,b,c,d, edges ab,ac,ad,bc,bd,cd, with R the vertex-edge incidence matrix over F2 with the row d deleted. A subset of columns is independent exactly when its edge set is a forest: cycle indicators lie in the kernel; a nonempty forest has a leaf whose incidence row forces the coefficient on its edge to vanish, iteratively (one can use all four rows since their sum is zero). Thus R genuinely represents M and all simple cycles are genuine circuits. Kernel dimension is 6-3=3.

Let x be cycle abcd (edges ab,bc,cd,ad), y cycle abdc (ab,bd,cd,ac), z cycle acbd (ac,bc,bd,ad), and t triangle abc (ab,ac,bc). Their circuit vectors are their F2 indicator vectors. x+y=z. The three squares x,y,z are distinct nonzero vectors and have rank two. Their span consists exactly of 0 and the three square indicators; it excludes t. Thus {x,y,z,t} has rank three, with t a coloop in this restriction.

Let H be these four circuits. Their union is all six edges, nullity three, so H is in A0. Every triple contains at least two squares; any two distinct squares together cover all six edges. Hence every triple has support-nullity three and is not in A0. Distinct genuine circuit vectors are never proportional, so a pair has rank two, and support-nullity at least two; a singleton circuit has nullity one. No proper subset of H lies in A0. H is therefore minimal in A0 but is not cyclic in N: its only minimal represented dependency is {x,y,z}, which omits t.

This explicitly blocks direct use of Jackson–Tanigawa with X=min A0 as prescribed circuits, or even as prescribed cyclic sets, for all representations. Using two parents J+{t1}, J+{t2} inside this K4 does not refute the target: all vectors stay inside the same three-dimensional W(E), and any four-element elimination child is dependent. Attempting to attach new outside-support circuits while keeping these size-four parents in A0 also fails: if a genuine new circuit has an edge outside E, its kernel vector is outside W(E), forcing nullity of the enlarged support to be at least four. Such a size-four parent is no longer in A0. This is the concrete reason the abstract five-column diagnostic cannot simply be glued onto K4.

## Limits

The first-step lemma is a partial universal helper with zero accepted credit. It is not claimed new to literature or significant enough for acceptance. The K4 diagnostic uses the source's known characteristic-two dependency but draws the explicit coloop obstruction to the companion's hypotheses; it is not a new solution. Formal feasibility remains unassessed beyond ordinary finite linear algebra; no Lean/API probing or execution took place. The unresolved overlap lemma is not converted into a purported bounded solver task.
