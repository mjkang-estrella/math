# Sustained mechanisms and exact stopping points

No full new endpoint is proved. The deductions below are ordinary mathematical deductions, not Lean-certified results or discovery-credit claims.

## 331781: valuation dynamics, beyond a finite sweep

Primary body: Cobeli–Prunescu–Zaharescu arXiv:1511.04315v1, definition (1.1), valuation interpretation in the introduction, Lemma 1 proof, and Section 6.2 Conjecture 3. Their Theorem 1 controls the 2-tomography; it does not control all odd-prime tomographies of the original positive-integer input. Replacing the initial sequence by its radical changes the process, so the paper's binary tomography results for that new sequence cannot be substituted.

Let T be the absolute-difference operation on nonnegative integer sequences, (Ta)_j=|a_j-a_(j+1)|. For each prime p, the valuation of the Z-process is exactly T applied iteratively to a_j=v_p(j+1). This follows from v_p(ab/gcd(a,b)^2)=|v_p(a)-v_p(b)|, at every step, without assuming squarefreeness.

Reduce coefficients modulo 2. Because |x-y| and x+y have the same parity, T modulo 2 is the linear operator I+E, where E shifts the sequence one position. In characteristic two, (I+E)^(2^g)=I+E^(2^g): inductively squaring removes the middle term. Thus, for n=2^g+1,

    v_p(W(n)) = v_p(1)+v_p(n) mod 2 = v_p(n) mod 2.

All primes occurring anywhere in the first n inputs are at most n. Unique factorization now gives

    W(n) = (n / largestSquareDivisor(n)) * B_g^2

for some positive integer B_g. In particular, the conjectured expression is a divisor of the actual W(n). This proves the squarefree *part*, not equality: even positive valuations disappear under the parity map. Confusing these two assertions would be a false proof.

For p>sqrt(n), every initial valuation in the first n positions is 0 or 1. T preserves that range, so parity determines the exact final valuation for those primes. Hence for each fixed g the only primes requiring nonlinear computation satisfy p<=sqrt(n). The Python/NumPy computation uses integer absolute differences for all such primes at g=14 and15. Both match the conjecture. These are diagnostics; no certificate or universal claim follows. The original C++ run failed because no compiler is installed; the unused source is retained, not represented as executed.

Decisive next lemma: for every prime p and every g, the first entry of T^(2^g)(v_p(1),...,v_p(2^g+1)) is at most 1. A proof of this sparse-row squarefreeness would complete the exact conjecture via the parity argument. Alternatively, any computed valuation >=2 is a substantive exact counterexample candidate. The mod2 operator argument alone provides no upper bound, and arbitrary bounded input sequences can preserve large values at a selected finite row (e.g. suitably placed isolated spikes). A valuation-specific cancellation argument is essential. Soliton noninteraction in the source is itself conjectural; it cannot be used as an axiom.

Novelty limit: this parity mechanism is routine characteristic-two linearization, consistent with the source's Pascal/Sierpinski discussion. It is not a claimed mathematical advance. A later full Z-process proof was not located in the bounded search, which is not evidence of its absence.

## 331205: product obstruction, then non-product optimization and stabilizer reduction

Primary bodies inspected: Lee arXiv:1508.05524v3, definitions (1)–(3), Conjecture1, Theorems3–5, Theorem3 product construction and proof; Bajnok–Matzke arXiv:1412.1608, Theorem5, Proposition6 proof and Proposition7 proof beginning. The latter already uses products of symmetric sets. The 2018 published Lee article was located by its publisher PDF search result, with numbering Conjecture6 and Theorems7–8, but its full proof body was not separately downloaded/read. No claim that 2017 is the final published version.

Write F(N,e,r) for the proposed divisor minimum. For A=A1 x A2 in G1 x G2,

    A-A = (A1-A1) x (A2-A2),

so |A-A| is the product of the two difference sizes and exp(G1 x G2)=lcm(e1,e2). A violation

    F(N1*N2,lcm(e1,e2),r1*r2) > F(N1,e1,r1)*F(N2,e2,r2)

would give a constructive counterexample whenever the factor bounds are achieved. The diagnostic tested 7,669,491 such parameter combinations, factor orders <=64, product order <=2048, with realizable order/exponent pairs. No violation occurred. This is a limited algebraic consistency test, not an exhaustive subset search or proof. Companion Proposition6 shows why mere products are an old mechanism, not a new discovery even if the search were extended.

I then tested non-product subsets by a mixed-integer formulation. Variables x_a indicate A, y_d indicate A-A, with x_a+x_b-y_(a-b)<=1, sum x_a=r, objective sum y_d. Translation permits x_0=1. Each returned witness was checked independently by computing its difference set as a Python set. Nine tests in Z4^2, Z8 x Z4, Z9 x Z3 matched F. Solver-reported optimality is retained only as diagnostic evidence: no exact rational infeasibility certificate, Lean proof, or global theorem follows from a floating-point MILP solver.

Structural continuation: let H be the stabilizer of D=A-A, h=|H|, and B=image(A) in G/H, s=|B|. Then D is the full preimage of B-B, so |D|=h|B-B|, and s>=ceil(r/h). Kneser's theorem gives |D|>=h(2s-1) for the aperiodic quotient difference set. This settles cases when that bound reaches F, but does not close the exponent gap. For example in Z9 x Z3 with r=10, F=21 while aperiodic Kneser only gives19. A quotient with stabilizer of size3 gives the required21. The unresolved case is an aperiodic 10-set difference of size19; the MILP found none but supplies no accepted proof of impossibility. A general exponent-sensitive classification of these aperiodic small-doubling sets, not another cyclic product construction, is the decisive new ingredient needed for the full conjecture. Proving one parameter instance would still receive zero discovery credit.

## 331222: why the tempting infinite-grid proof stops

Theorem6.2 and Remark6.4 of arXiv1508.06020 prove finite-grid lower bounds and all countable-minimum cases. Each hyperplane has at least one coefficient that is not a zero divisor; the finite proof uses injectivity along that coordinate. This hypothesis must not be replaced by merely a nonzero coefficient.

For a field, a direct induction proves the arbitrary-cardinality statement: assume lambda hyperplanes with lambda<min|Ai|. Partition equations by the last index of a nonzero coefficient. Choose x1 avoiding the <=lambda forbidden values from equations whose last index is1; choose x2 avoiding forbidden values after x1 is fixed from equations whose last index is2; continue. A nonzero field coefficient has at most one root, so each choice is possible and the final point avoids the cover. Finite-index partition handles a mixture of finite and infinite coordinate sets as long as lambda is below all their sizes.

Over a general ring, choosing the last *regular* coefficient does not ensure that later coefficients vanish. They can be zero divisors, so the recursive avoidance conditions depend on coordinates not yet chosen. Choosing the last *nonzero* coefficient instead destroys the at-most-one-root step. Thus neither ordering argument proves the literal arbitrary-ring endpoint. A valid all-ring avoidance lemma must address those dependencies explicitly. No such lemma or counterexample was obtained. The field proof is a routine known subcase, not a creditable resolution.

## Other source-body exclusions

* 331135: Haverkort's Lemma6 proof counts full, side, and hanging vertices, forces two full vertices with three shared neighbors, and derives an impossible hanging-vertex angle. The conclusion explicitly states the exact ten-triangle lower bound and a matching example. The corpus's nine-triangle narrative is stale.
* 331888: the source's Theorem1.6 states the exact formula; Section3 begins with the n=5k-1 identity, then double induction on k,n. Therefore no new bridge beyond the displayed branch identity is needed.
* 331996: max degree-bounded edge subset is not max k-edge-colorable subset. A triangle at k=2 gives3 for the former,2 for the latter. A balanced-degree proof cannot be ported silently.
* 331546: source nu is symmetric-build length; eta is antisymmetric-build length. The record reverses the name. Its rank/full-build comparisons cannot be used without correcting semantics, and that correction is not a discovery.
* 331537: ordinary connected nonbipartite graphs already satisfy lambda_max(L)=rho(L); the source introduction says so. Treating K3 as a 2-uniform counterexample adds no significant mathematics. Higher-order tensors require all complex eigenvalues, not just the variational real H-spectrum.
