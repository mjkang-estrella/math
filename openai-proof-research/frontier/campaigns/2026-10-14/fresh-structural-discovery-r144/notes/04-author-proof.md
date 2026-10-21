# Author proof for the frozen r144 scope

This is a discovery handoff, not a manuscript or an independent review. The exact statement is in 03-frozen-scope.md (SHA256 98d8a82c64798cfeeb033fe73f708b1cea643159b8b334b4174528269d15882f). No grading or counting is performed here. All ground sets and intervals below are those of that statement.

## 1. Relative-rank facts and finite supports

Write r(A|X) for relative rank in M, and cl(X) for M-closure. Only ranks with finite first argument are subtracted. In particular all q_n are finite integers. We use the standard contraction rank chain rule and monotonicity: contraction by a larger spanning set cannot increase rank. The chain rule is also the explicit (R3) interface in Gollin–Joo, section 2.1. Finitary means every circuit is finite, equivalently every dependent set has a finite dependent subset. It implies finite character of closure.

**Finite witness fact.** For finite A and arbitrary X subset E,

    r(A|X) = min {r(A|F) : F is a finite subset of X}.                 (1)

To prove this, choose a basis C of the finite restriction (M/X)|(A minus X). It has r(A|X) elements and A is contained in cl(X union C). Finite character supplies, for every a in A, a finite subset F_a of X such that a is spanned by F_a union C. Their union F is finite. Hence r(A|F) <= |C| = r(A|X), while the reverse inequality follows from F subset X. This proves (1), including dependent X and elements of A already in X.

**Exact support lemma.** If Y is M-independent and A is finite, there is a finite R subset E such that for every X subset Y,

    r(A|X)=r(A|X intersection R).                                  (2)

Extend Y to an M-basis D. Each a in A minus D has a unique fundamental circuit in D+a, and this circuit is finite. Let R subset D be the union of these circuits with the elements a removed, together with A intersection D. Then R is finite and A subset cl(R). Fix X subset Y, and put K=X intersection R.

For finite S subset D minus R, independence of D gives r(S|R)=|S|. Since K union A is contained in cl(R), monotonicity and the trivial upper bound give r(S|K union A)=|S|, as well as r(S|K)=|S|. Apply the finite rank chain rule to obtain

    r(A|K union S) = r(A|K).

More generally, for K' subset K the same identity holds with K'. For any finite F subset X, write F=(F intersection R) union (F minus R) to deduce

    r(A|F)=r(A|F intersection R) >= r(A|K).

Equation (1) and K subset X now prove (2). Thus the same finite support works for ALL X in the independent interval 2^Y. This is stronger than merely saying rank has finite witnesses separately at each X.

For each n choose such a support R_n relative to Y and A=E_n. The function q_n on 2^Y depends only on X intersection R_n. If membership in X_k converges pointwise to membership in X, then q_n(X_k)=q_n(X) for all sufficiently large k. A finite union of R_n protects any specified finite list of tests under arbitrary changes away from that union.

## 2. Probe identities and endpoints

Fix M,T,(E_n) as in the frozen scope, put c_n=r(E_n|T), q_n(X)=c_n-r(E_n|X), and ell(X)=liminf q_n(X).

For M-independent X subset Y, q_n(X)<=q_n(Y). More precisely, if F is a finite subset of (Y minus X) intersection E_n, independence and the contraction chain rule give

    r(E_n|X)=|F|+r(E_n|X union F)
              >= |F|+r(E_n|Y),

so q_n(Y)-q_n(X)>=|F|. In particular a proper independent extension by at least one element raises every sufficiently late probe by at least one.

If e is outside X and X+e is M-independent, contraction changes r(E_n|X) by either zero or one, since the rank of one element is one. If e belongs to E_n, the chain rule gives the exact change one. Consequently

    q_n(X+e)=q_n(X)+1 eventually,     ell(X+e)=ell(X)+1.             (3)

The extended-integer convention is used for infinite ell. Deletion has the opposite effect. For two independent sets with finite symmetric difference, apply (3) through their common intersection. The eventual change is the number added minus the number deleted, even if their union is dependent. In particular balanced finite exchanges preserve ell.

There are two useful endpoint divergences. As T is independent,

    r(E_n) >= |T intersection E_n| + r(E_n|T).

Therefore q_n(empty)<=-|T intersection E_n| tends to minus infinity. Every finite M-independent set differs from empty by finitely many additions, so also has ell=-infinity.

If D is any M-basis, r(E_n|D)=0 and q_n(D)=c_n. The increasing finite sets E_n exhaust E, and M/T has infinite rank; hence c_n tends to plus infinity. Indeed every finite independent set in M/T is contained in E_n for all sufficiently large n. Thus ell(D)=+infinity for every M-basis. Finally q_n(T)=0 for every n.

## 3. Interpolation on every independent interval

**Crossing lemma.** Suppose I subset Y are M-independent and

    ell(I)<0<ell(Y).

There is B with I subset B subset Y and ell(B)=0.

If a=ell(I) is a finite negative integer, add -a elements from Y minus I. Enough elements exist: if the gap had finite size h<-a, the finite-change identity would give ell(Y)=a+h<0, a contradiction. The resulting set has ell=0. If instead b=ell(Y) is finite positive, delete b gap elements; a gap of size h<b would imply ell(I)=b-h>0, again impossible. Deleting b yields ell=0. These cases include either combination with one infinite endpoint.

It remains that ell(I)=-infinity and ell(Y)=+infinity. Choose finite supports R_n from (2) on the whole interval 2^Y, and put H_j=union_(n<=j) R_n. Start X_0=Y. Construct X_j from X_(j-1) by finitely many deletions, always leaving I included.

At stage j, if q_n(X_(j-1))<=0 for some n>=j, make no change. Otherwise all those integer probes are at least one. Enumerate the eligible elements

    (X_(j-1) minus I) minus H_j

in any countable order, and delete them one at a time, stopping at the first deletion after which some probe with index n>=j is nonpositive.

The stopping time is finite. If all eligible elements were deleted, the resulting set Z would satisfy I subset Z subset I union H_j, hence differ finitely from I and have ell(Z)=-infinity. Fix n>=j with q_n(Z)<0. The finite support R_n implies that the same negative value occurs after finitely many eligible deletions. Thus some stopping time occurs no later. Just before the stopping deletion all tail probes are positive integers; one deletion decreases each by zero or one. At the stopping time, therefore,

    q_n(X_j)>=0 for all n>=j,
    q_m(X_j)=0 for at least one m>=j.                               (4)

All probes with n<=j remain exactly unchanged during the stage because H_j is protected. There is no conflict at n=j: if it was positive before the stage it remains so; the zero witness then has a larger index.

Let X_infinity=intersection_j X_j. It contains I and is contained in Y, so is M-independent. For each fixed n, the finite-support lemma shows q_n(X_j) eventually equals q_n(X_infinity).

A first stage j_0 that deletes exists. Otherwise every X_j would equal Y and the no-change rule would witness a nonpositive probe in every tail of Y, contradicting ell(Y)=+infinity. Fix n>=j_0. After stage j_0 its probe is nonnegative by (4). Up through stage n each later stage either does nothing or restores nonnegativity via (4); all stages j>n preserve it exactly. Consequently q_n(X_infinity)>=0 for every n>=j_0.

Every stage j leaves some witness q_m(X_j)<=0 with m>=j, either by the no-change condition or by (4). Later deletions can only decrease this fixed probe, so its limit remains nonpositive. For j>=j_0, the preceding nonnegativity makes the witness in X_infinity exactly zero. There are such witnesses arbitrarily far out, while the whole tail is nonnegative. Hence ell(X_infinity)=0. Take B=X_infinity.

This proves the crossing lemma for all endpoint cases. The construction is the decreasing-stage pattern of source185, Lemma local-interpolation, with exact independent-interval supports replacing its summable losses. It neither uses a density-zero class nor constructs an ultrafilter.

## 4. Matroid axioms and identification of bases

Define I_N={X in I_M:ell(X)<=0}. We verify the independence axioms (I1), (I2), (I3), and (IM).

(I1): empty belongs to I_N by endpoint divergence.

(I2): If X subset Y and Y belongs to I_N, then X is M-independent and q_n(X)<=q_n(Y) for every n. Thus ell(X)<=ell(Y)<=0, proving heredity.

We first identify the globally maximal members. If B is M-independent with ell(B)=0, any proper M-independent extension Y has, for all sufficiently large n, q_n(Y)>=q_n(B)+1. Hence ell(Y)>=1, and no proper extension is in I_N. Conversely suppose I belongs to I_N with ell(I)<0. Extend I to an M-basis D; ell(D)=+infinity. The crossing lemma supplies B between I and D with ell(B)=0. It is a proper extension of I, since their ell values differ. Thus I is not maximal. We have proved both that every member extends to a maximal member and that the maximal members are exactly B_N={B in I_M:ell(B)=0}. In particular T is a basis.

(I3): Let I be N-independent and not maximal, and B a maximal N-independent set. Then ell(I)<0 and ell(B)=0. If B were contained in cl_M(I), monotonicity under spanning containment would give r(E_n|B)>=r(E_n|I), hence q_n(B)<=q_n(I) for every n. Taking lower limits contradicts 0=ell(B)>ell(I). Therefore there exists e in B outside cl_M(I). This e is outside I, I+e is M-independent, and (3) gives ell(I+e)=ell(I)+1<=0, since ell(I) is a negative integer or minus infinity. Hence I+e belongs to I_N, as required.

(IM): Let I belong to I_N and I subset Z subset E, with no assumption that Z is M-independent. The M-maximal-extension axiom supplies a maximal M-independent J inside Z containing I. If ell(J)<=0, then J belongs to I_N and is maximal there inside Z, since any N-independent extension would be an M-independent extension. If ell(J)>0 and ell(I)=0, take I itself, which is already globally maximal in I_N. If ell(J)>0 and ell(I)<0, apply crossing to I subset J. It yields B with I subset B subset J and ell(B)=0. The global maximality already proved makes B maximal inside Z. This proves (IM) in all cases.

These are the independence axioms of an infinite matroid, so N exists with precisely the asserted independent sets and bases. Equivalently, the argument verifies the operative interval condition in Gollin–Joo Lemma3.1; the independence-axiom proof explicitly includes restrictions which are not independent in M.

## 5. Generalised truncation, wildness, and finitarization

The ground set is E and I_N subset I_M by definition. If I is N-independent but not an N-basis, then ell(I)<0. For ANY e outside I with I+e M-independent, equation (3), without reference to a chosen second basis, gives ell(I+e)<=0. This is exactly Definition1.1(III) of Gollin–Joo; hence N is a generalised truncation of M.

All finite M-independent sets have ell=-infinity by section2, and are N-independent. Conversely every N-independent set is M-independent. Thus the finite independent sets agree. Since M is finitary, the family of sets all of whose finite subsets are N-independent is exactly I_M: the finitarization of N is M.

Every N-basis B is infinite, since finite independent sets have ell=-infinity. It also has infinite M-relative corank. Otherwise r(E|B)=k<infinity would bound r(E_n|B)<=k for all n, and c_n tends to plus infinity, so q_n(B)>=c_n-k would tend to plus infinity, contradicting ell(B)=0. In particular B is not an M-basis. N differs from M, and it differs from every positive (or zero) finite-rank truncation because its bases are infinite. It differs from each negative integer truncation because a basis of a (-k)-truncation is obtained from an M-basis by deleting k elements and has M-relative corank k. Thus N is wild in the generalized-truncation sense.

No assertion about all circuit-cocircuit intersections follows from this terminological use of wild. Nonfinitarity does follow: N has finitarization M but is different from M.

Finally every countable finitary infinite-rank M admits the input T. Choose a basis D; it is countably infinite. Partition D into two infinite sets T and U. T is M-independent and U is independent in M/T, so M/T has infinite rank. The preceding construction then applies.

## 6. Borel complexity

Identify subsets of E with points in the Cantor space 2^E. I_M is closed: a failure of M-independence is witnessed by a finite dependent subset, so its complement is open.

For finite A and integer k, equation (1) gives

    {X : r(A|X)<k}
      = union { {X:F subset X} : F finite, r(A|F)<k }.

Each set {X:F subset X} is clopen, and the union is open. Thus {X:r(A|X)>=k} is closed. In particular, for c_n=r(E_n|T),

    C_n={X:r(E_n|X)>=c_n}

is closed. Extend q_n to arbitrary X by the same finite relative-rank formula. Its integrality implies ell(X)<=0 exactly when q_n(X)<=0 for arbitrarily large n. Therefore

    I_N=I_M intersection intersection_m union_(n>=m) C_n.           (5)

The union is F_sigma and the countable intersection is Pi^0_3; intersecting with closed I_M preserves Pi^0_3. This is an upper bound, not a completeness assertion.

Likewise O_n={X:q_n(X)>=0}={X:r(E_n|X)<=c_n} is open, using (1). For an integer sequence, liminf=0 is equivalent to eventual nonnegativity and infinitely many nonpositive values. Consequently

    B_N=I_N intersection union_m intersection_(n>=m) O_n,          (6)

which is Borel. No claim of Pi^0_3 complexity for B_N is needed, nor is a Borel selection of the interpolating sets asserted. Equations (5) and (6) complete the full frozen scope.

## 7. Compatibility and review focus

The full quantifiers include every countable finitary M, every allowed T, and every finite exhaustion, with dependent ambient restrictions in (IM). The argument uses neither a quotient map from a free matroid nor an arbitrary transfer of a uniform basis family: those would not supply the exact support identity (2) for conditional ranks on 2^Y. The assembly of separate ultrafilter/prototype classes in source185 is not used. The new operation asserted for review is replacing that assembly by a global integer-valued conditional-rank threshold, with support protection across arbitrary independent intervals. The strongest classical reductions, the source interpolation proof, and the Gollin–Joo basis criterion have all been incorporated rather than discounted.

The free-matroid specialization is particularly transparent: q_n(X)=|X intersection E_n|-|T intersection E_n|. This yields one Borel uniform matroid, generally not self-dual. Bowler–Geschke's actual nonanalyticity theorem concerns self-dual uniform matroids and is therefore not an obstruction to the statement here. This observation is a scope distinction, not an assessment of the theorem's contribution.

Author-side verification priorities for a separate reviewer are the exact finite-support identity, the finite stopping and tail preservation in section3, the use of spanning containment in (I3), and arbitrary-restriction maximality in (IM). No finite experiment is substituted for these proofs. No correctness or contribution verdict is assigned here.
