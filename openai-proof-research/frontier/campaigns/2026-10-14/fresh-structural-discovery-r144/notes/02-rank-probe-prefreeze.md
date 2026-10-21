# Prefreeze feasibility: corank probes on arbitrary countable finitary matroids

This is the continuation of the same r144 Source185 work, after the primary Gollin–Joó theorem and its full relative-rank/MA proof were read. No old frozen scope is modified. The Borel packing/covering counterexample asked about in r114/r118 is not asserted: the proposed matroid need not be self-dual, and no pair or covering obstruction is claimed.

Let M be countable and finitary; let T be independent with |T|=infinity and r(M/T)=infinity; exhaust E by finite E_n. Define integer probes

    q_n(X)=r_M(E_n | T)-r_M(E_n | X),  X independent in M.

These are finite differences of finite numbers, not infinity minus infinity.

Feasibility calculations:

1. Monotone: X subset Y gives q_n(X)<=q_n(Y). If X,Y are independent and e in Y minus X belongs to E_n, the inequality improves by at least1. If Y=X+e, equality q_n(Y)=q_n(X)+1 holds for all such n. Thus any finite independent addition/deletion shifts the eventual profile by its net size.

2. Finite balanced exchanges also preserve the eventual profile even when the union is dependent: for independent X,X' differing finitely, put K=X intersection X'. Once E_n contains X triangle X', the contraction rank chain rule through K gives

    q_n(X')-q_n(X)=|X' minus X|-|X minus X'|.

3. Endpoint divergence: q_n(empty) tends to minus infinity because T has arbitrarily large finite independent subsets eventually in E_n; for any basis B of M, q_n(B)=r(E_n|T) tends to plus infinity because r(M/T)=infinity.

4. Crucial finite-support operation. Fix an M-independent ambient Y and finite A⊂E. Extend Y to a basis B of M. The fundamental circuit of each e∈A minus B is finite by finitarity. Let R⊂B be the finite union of those circuit supports and A intersection B. Then A⊂cl R. Since R together with B minus R is independent, contracting any subset of Y minus R cannot change ranks inside cl R. Consequently

    r(A|X)=r(A|X intersection R) for every X⊂Y.

This gives exact finite-coordinate dependence on the compact interval 2^Y, not merely semicontinuity. It allows a deletion stage to protect ALL earlier tests exactly by avoiding finitely many elements of Y. A global coordinate identification with a basis would not prove this assertion.

5. Crossing calculation. For I⊂Y independent and liminf q(I)<0<liminf q(Y), finite endpoint limits are corrected by finitely many additions/deletions. In the -infinity/+infinity case start at Y, and at stage j, if a nonpositive probe exists beyond j, do nothing. Otherwise delete gap elements outside the finite support of tests1,...,j until some test beyond j becomes0. Each deletion changes every test by0 or1. The deletion procedure stops: deleting all eligible elements leaves only finitely many elements above I, hence liminf=-infinity, and a fixed negative test already witnesses this after finitely many deletions. After a stage that deletes, all tail tests are nonnegative. Later stages protect earlier tests exactly. The decreasing limit has an eventually nonnegative profile with zeros arbitrarily far out, hence liminf0.

This is the proposed bridge. Need full written verification of the decreasing limit, inherited witnesses, finite-endpoint cases, exchange with an arbitrary new basis, and maximal extension inside a set which is not M-independent. None can be replaced by a finite sample.

6. Candidate independence is I_N={X∈I_M: liminf q_n(X)<=0}; candidate bases have liminf0. Every candidate independent set extends to a candidate basis by crossing to a basis of M. For arbitrary I⊂Z, first maximize I in M|Z to obtain an M-independent J. If liminf q(J)<=0, J is already maximal inside Z. Otherwise cross [I,J] to a candidate basis. Exchange uses: if an M-independent nonbasis I spanned a candidate basis B, monotonicity of contraction ranks would force0=liminf q(B)<=liminf q(I)<0, a contradiction.

7. Borel calculation. For finite A, r(A|X)=min{r(A|F): F finite subset X} by finitarity. Thus {X:r(A|X)>=k} is closed in Cantor space. Since I_M is closed, the set I_N is the intersection of I_M with

    intersection_m union_(n>=m) {X:r(E_n|X)>=r(E_n|T)},

a Pi^0_3 set. The bases are Borel by imposing liminf0. T is a new basis with infinite M-relative corank; this excludes the trivial and all integer truncations.

Strongest actual comparison before freeze: source185 local-interpolation proves the decreasing-stage method for specially built real density probes within one ideal class; its global uniform self-dual matroid uses ultrafilter/ordinal/prototype assembly. Gollin–Joó v1, Lemma3.1 and Theorem4.1, instead build relative-rank-incomparable classes with MA. Their task system and maximality criteria are fully read. The proposed replacement uses a single sequence of conditional finite ranks and an exact finite-support lemma on independent intervals; no MA filter or source uniform matroid is inserted as a quotient of M. It does not claim their stronger arbitrary prescribed collection of less-than-continuum many classes or uncountable-ground theorem.

History check: component-pruned rank_history_scan selected12604 authored candidate paths, matched10. Numbers are navigation, not clearance. Operative r15,r21,r114,r118 passages read; r118 Source185 section27–31 has the same old descriptive interface. Neither old descriptive nor connected target is nominated. Compound/flat derivative admissions and omitted branches remain in the limitations. No claim of exhaustive history or current worldwide priority.
