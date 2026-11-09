# MathDB 364196: ordinary endpoint and version qualification

Research only; credit 0. No Lean, search over mathematical objects, solver, or children. The full endpoint below is for the ACTUAL original suited rule, 2408.00903v1 Definition 4.1 (decrement the suit of the wrapping card modulo s). It is not a claim that the different printed v2/v3 update has been proved correct. Section 7 explains that distinction.

## 1. Exact game and claim

Let n >= 1 and s >= 1 be integers. A secret is a tuple of n cards, with each rank 1,...,n appearing once and each card having one of the s suits 0,...,s-1. There are N=n! s^n secrets. A legal guess is another such tuple. The only feedback is the subset of positions occupied by exactly the right card, including suit. There is no wrong-suit-at-right-rank feedback and no yellow/absent feedback. A deterministic strategy chooses each guess from the entire preceding sequence of feedback subsets. It need not retain correct positions, avoid a previously excluded card, or ever terminate. Success means actually guessing the secret, not merely identifying it.

For every integer r >= 0 and every such strategy A,

    #{secrets solved by A within r guesses}
      <= sum_{0 <= k < r} D_s(n,k),

where D_s(n,k) is the v1 CircularShift count in Theorem 4.3. Hence v1 CircularShift has probability at least that of A under the uniform law. The bound also holds if A can guess arbitrary words of cards with repeated ranks; this strengthening is not needed. It also holds for randomized strategies whose private randomness is independent of the secret. Fixing the whole random tape gives a deterministic strategy at the finite horizon r, and averaging the deterministic bound proves the assertion. No posterior-uniformity assumption is used.

At r=0 both success probabilities are zero. If n=0 is admitted, use the source convention of one empty secret solved on its first submitted guess; the assertion is immediate. We do not interpret s=0 as a uniform game.

## 2. Feedback histories really give the required bound

Choose a primitive s-th root zeta in C and encode rank a, suit c by a*zeta^c. Codes are distinct: equal codes have equal absolute values, hence equal a, and then equal c modulo s. Let X be the N secret points in C^n. Its s-th power coordinates are 1^s,...,n^s in some order. For d >= 0 let V_d be the restrictions to X of polynomials of degree at most d in each separate variable.

After first success, replace a strategy by the strategy repeating that same successful guess forever. This changes no first-success event and is legitimate because [n] feedback certifies the whole secret. For each feasible length-d feedback history U=(U_1,...,U_d), select a secret x_U producing it. Let g_U^j be the encoded round-j guess following this history and put

    P_U(x) = product_{j=1}^d product_{i notin U_j} (x_i - g_U^j(i)).

Every factor is nonzero at x_U. Each variable occurs at most once per round, so P_U|X belongs to V_d. For distinct U,U', suppose P_U(x_U') != 0. Let j be the first differing feedback round. The earlier feedbacks agree, so the actual adaptive guesses agree through round j. Nonvanishing at x_U' says that its round-j correct set is contained in U_j. Since these sets differ, U'_j is a proper subset of U_j. Thus the sequence of feedback cardinalities for U' precedes that for U lexicographically. Ordering the histories this way yields a triangular evaluation matrix with nonzero diagonal. Equal-cardinality incomparable feedback sets cause zero entries; arbitrary tie-breaking is harmless. Consequently the number of feasible histories is at most dim V_d.

At most one secret solved by time d+1 can have a given length-d history: the guess at d+1 is fixed by that history and must equal any such secret, including earlier successes by the absorbing modification. Therefore

    success_count_A(d+1) <= #feasible_histories_d <= dim V_d.          (H)

This is a complex-linear evaluation-rank argument; no real ordering of card codes or stochastic independence of feedback rounds is assumed.

## 3. The maximum-exponent bridge, including nonzero invariants

Use colored permutations g=(pi_1^{c_1},...,pi_n^{c_n}) with colors 0,...,s-1. Their letter order lists all color s-1 ranks increasingly, then color s-2 ranks increasingly, down to color 0 ranks increasingly. Let Des(g) be descents in this order, d_i the number of descents in positions i,...,n-1, and

    f_i = s*d_i + c_i,       B_g = product_i x_{pi_i}^{f_i}.

Then f_1 >= ... >= f_n >= 0. Indeed at a descent the difference is s+c_i-c_{i+1} > 0; at a non-descent c_i >= c_{i+1}. Equality of consecutive f_i forces equal colors, no descent, and pi_i < pi_{i+1}. Thus the sorted exponent order of B_g is exactly pi, with increasing indices breaking ties. Its maximum exponent is f_1=fdes(g), not total degree fmaj(g).

We prove

    V_D = span{B_g|X : fdes(g) <= D}.                               (F)

Here is a direct straightening proof, independent of homogeneous-quotient dimension arguments. Order all monomials with maximum exponent at most D first by decreasingly sorted exponent vector, lexicographically, and then by their ordinary exponent vector, lexicographically. There are finitely many such monomials. For M=x^a choose pi sorting a decreasingly, breaking equal-exponent ties by increasing variable index, and set c_i = a_{pi_i} mod s. With g, f_i defined above, put

    b_i = (a_{pi_i}-f_i)/s.

The b_i are nonnegative decreasing integers. At the last position this is the integer quotient of a_{pi_n} by s. At a descent, a_{pi_i}-a_{pi_{i+1}} >= s+c_i-c_{i+1}; at a non-descent it is >= c_i-c_{i+1}. These inequalities prove b_i >= b_{i+1}. In particular B_g divides M, and fdes(g) <= max a <= D.

Let S be the monomial symmetric polynomial in y_i=x_i^s indexed by b=(b_1,...,b_n): it is the sum of the DISTINCT monomials obtained by assigning the b_i to the n variables. The product B_g S contains M with coefficient 1. Every other monomial in this product is strictly smaller in our order and has maximum exponent at most max a.

For completeness, the needed rearrangement statement has a precise equality case. For decreasing f and b, any exponent vector f_i+s*b_{rho(i)} is majorized by f_i+s*b_i. For a set of k coordinates, the sum of its f entries is at most the first k f entries and the sum of its assigned b entries is at most the first k b entries; maximizing over k-coordinate sets proves the majorization inequalities. If the sorted exponent partitions agree, their sums of squares agree. Maximizing that sum is equivalent to maximizing sum_i f_i*b_{rho(i)}. An inversion with both f_i>f_j and assigned b_{rho(i)}<b_{rho(j)} would strictly increase that sum upon swapping. Therefore a maximizer assigns the b values in decreasing order between distinct f blocks. It can differ from the aligned assignment only within equal-f blocks (or by exchanging equal b values). Within an equal-f block, pi is increasing. Assigning the largest b to the smallest variable index makes the ordinary exponent vector lexicographically largest. Hence M is the unique maximal monomial in B_g S. The first majorization inequality also gives the required maximum-exponent bound for EVERY other term.

On X, S is the scalar C_b=m_b(1^s,...,n^s), which is a positive real number, not zero. Thus

    M|X = C_b*B_g|X - (B_g S - M)|X.

All terms in the parenthesis lie below M in the finite order and obey the SAME maximum-exponent bound. Induction proves (F). The case b=0 simply says M=B_g and requires no induction. No assumption that this order is multiplicative is used.

This also explicitly handles the top invariant. If b_n>0, then S contains a factor (y_1...y_n)^{b_n}; on X this is (n!)^{s*b_n}. Nothing is discarded or set to zero. Alternatively one can first remove powers of (x_1...x_n)^s: evaluation replaces each by (n!)^s and decreases every exponent by s. Both descriptions terminate. A total-degree-flat deformation alone would not prove (F); the rearrangement bound does.

## 4. Explicit reduction to existing full-ring straightening

Chan–Rhoades, arXiv:1701.06256, Section 5.1, Definitions 5.2–5.5 and Lemmas 5.4–5.6, gives the same bridge with elementary symmetric invariants. For every monomial M, Lemma 5.6 states the POLYNOMIAL-RING identity

    M = e_{mu(M)}(x_1^s,...,x_n^s) B_{g(M)} + Sigma,

where Sigma is a sum of same-total-degree monomials strictly lower in dominance, with the inversion tie-break. Lemma 5.4 says B_{g(M)} divides M. All lower monomials have maximum exponent at most that of M: dominance controls the first part and an equal-partition tie preserves it. Evaluate the invariant factor at (1^s,...,n^s), a scalar, and induct first on total degree and then on the finite same-degree dominance/inversion order. If the invariant factor has positive degree, B_g has strictly smaller total degree; if it has degree zero, M=B_g. This proves (F), including arbitrary powers of e_n, without discarding them. The invariant constants being nonzero does not disrupt either induction.

Bagno–Biagioli's actual 2007 journal body, Section 4 Equation (12) / Theorem 4.3 (pp. 323–324), works initially modulo the top invariant, as the retained notes correctly warned. Section 10 Equation (22) / Lemma 10.2 (pp. 336–337) restores its arbitrary powers. Section 11 Lemma 11.1 / Theorem 11.2 gives the exponent-partition/Carlitz series. Chan–Rhoades makes the full-ring statement particularly explicit. Meyer, Algebraic Combinatorics 3(4) (2020), Section 4.2 Lemma 4.15 / Proposition 4.16, also straightens inside an individual-exponent bound, but its homogeneous generalized quotients are not themselves our nonzero orbit. The displayed evaluation induction is the required reduction.

The direct proof in Section 3 is the colored counterpart of successor2609.01874 Proposition 15, with symmetric polynomials in the s-th powers replacing symmetric polynomials in the variables. This is a complete classical straightening/evaluation adaptation; its classification as routine is based on the actual matching mechanism and explicit reduction, not its length or an open label. No claim of a new algebraic basis is warranted.

## 5. Exact colored Eulerian count, without conflating statistics

The mapping from exponent vectors a to (g,b) in Section 3 is a bijection between all monomials and pairs consisting of a colored permutation g and a decreasing n-tuple b of nonnegative integers. Inverting it sets a_{pi_i}=f_i+s*b_i. The result is decreasing in pi order; equality forces equal f and equal b and hence increasing pi indices, so the original tie-break is recovered. The maximum exponent is fdes(g)+s*b_1.

Writing F_{n,s}(t)=sum_g t^{fdes(g)}, summing monomials by their maximum exponent gives

    (1-t) sum_{j>=0}(j+1)^n t^j = F_{n,s}(t)/(1-t^s)^n.

The factor on the right follows by setting the n successive differences of b to independent nonnegative integers: b_1 is their sum. Consequently

    F_{n,s}(t) = (1-t)(1-t^s)^n sum_{j>=0}(j+1)^n t^j.               (C)

This also follows from Bagno–Biagioli Theorem 11.2, p=1, q=1, with their group color parameter r replaced by our s. Here fdes=s*des+c_1. It is NOT des, a type-B descent number, fmaj, or the per-secret statistic exc(pi)+sum colors. These latter statistics need only be equidistributed in the exact way (C) proves.

Let H_n(t) be the RHS of (C). Since sum(j+1)^n t^j=(t*d/dt+1)sum(j+1)^{n-1}t^j,

    H_n = (1+t+...+t^{s-1}+s*(n-1)*t^s) H_{n-1}
          + t*(1-t^s) H'_{n-1},        H_0=1.

Its coefficients satisfy exactly v1 Theorem 4.3:

    D_s(n,k) = (k+1)D_s(n-1,k) + (sn-k)D_s(n-1,k-s)
               + sum_{l=1}^{s-1}D_s(n-1,k-l).

Therefore F_{n,s}(t)=sum_k D_s(n,k)t^k. The source's v2/v3 generating function for W_s is the same polynomial, regardless of its different per-secret rule. Equation (F) yields

    dim V_d <= #{g:fdes(g)<=d} = sum_{k<=d}D_s(n,k).                 (D)

In fact equality holds. All B_g have maximum exponent <=sn-1. Polynomial interpolation on the sn distinct possible card codes spans all functions on X with coordinate degree <=sn-1. Thus (F) at D=sn-1 spans an N-dimensional function space with exactly N monomials B_g; these form a basis, and all its subfamilies are independent. Equality is extra information, not needed for (H).

## 6. Original v1 CircularShift really attains this bound

Its first guess is the identity with all suits 0. Keep every correct card, rotate all remaining cards right, and decrement the suit modulo s of the one wrapping from the last available position to the first. The source Theorem 4.3 gives its exact finish recurrence just matched in Section 5. Its lift explanation is directly checkable and verifies the algorithm-round correspondence:

Order the sn positions (c,j) lexicographically with c=0,...,s-1. Lift a suited tuple tau to the ordinary permutation

    Phi(tau)(c,j) = (c+color_of_card_at_j mod s, rank_at_j).

Initially Phi(guess) is the ordinary identity. Agreement with Phi(secret) at (c,j) holds exactly when the original card at j is fully correct, independently of c. Therefore the unsolved positions consist of the same list a_1,...,a_l in each layer. Ordinary CircularShift moves a card from a_{j-1} to a_j within each layer, and from the last available slot of layer c-1 to the first of layer c. The latter movement subtracts 1 from its relative suit modulo s. Hence every single original round lifts to one ordinary round, with all solved positions retained and with simultaneous termination. This is not an sn-fold rescaling of the number of guesses.

Ordinary CircularShift terminates after 1+exc(Phi(secret)), as in v1 Theorem 3.4 / Proposition 4.5 / Corollary 4.6. Lemma 4.7 computes each block's contribution: s if its suit is 0 and its rank exceeds the position, 0 if suit is 0 and rank does not exceed the position, and s-c if its suit c is nonzero. The subsequent insertion proof of Theorem 4.3 is read; it has respectively contributions sum_{l=0}^{s-1}D(n-1,k-l), k D(n-1,k), and (sn-k)D(n-1,k-s), giving precisely the displayed recurrence. Thus the actual original strategy has D_s(n,k) secrets finishing at k+1.

Combining this count with (H) and (D), with d=r-1, proves the full claim in Section 1. Dividing by N proves the requested uniform-probability comparison, and the random-tape argument covers randomized strategies. Ties in success probabilities are allowed. No restriction to nonadaptive cyclic strategies has been imposed.

## 7. Later printed rule is a source gate, not silently corrected

v1 Definition 4.1 subtracts one modulo s only on the wrapping card. v2 Definition 4.1 and v3 Definition 4.3 instead print nonmodular color increments using rank-dependent inequalities. The later prose describes incrementing after a card completes its circuit past its starting rank, and its lemma claims the per-secret count 1+exc(sigma)+sum kappa(i). These are not literally the old rule. Moreover, the printed inequalities disagree with the later lemma's proof. The v3 PDF page 8 has been rendered and visually checked; this is not a pdftotext artifact.

A hand calculation exposes the mismatch, without enumeration or solver use. Take n=s=2 and secret [(rank2,suit0),(rank1,suit0)]. The initial guess [(1,0),(2,0)] receives empty feedback. The printed formula produces round 2 [(2,1),(1,0)]: its nonwrap condition 2<2<=1 is false, and its wrap condition 1<=2 is true. The feedback is {2}. With only position 1 active, the next printed wrap test again holds, so the rank2 suit becomes 2, outside the fixed-s game. In contrast, the stated later finish formula requires success in round 2. Even if one extends the color alphabet, the printed nonmodular sequence never returns that rank2 suit to 0. We do not insert a modulo operation or reverse the inequalities without saying so.

This is an uncredited formulation diagnostic, NOT a significant refutation of the intended suited optimality question. It does not defeat the original v1 rule, whose same secret finishes at round 3 and whose overall uniform finish distribution is still optimal by Section 6. It also does not invalidate the filtration proof, which bounds every actual strategy independently of CircularShift.

For a corrected later algorithm, once its source-to-rule correspondence and exact W_s finish counts are established, Sections 1–5 immediately prove its optimality as well. The current report does not designate an unapproved correction as the actual source algorithm. The latest-version literal endpoint remains on SOURCE HOLD, while the original v1 fixed-s endpoint has a complete ordinary proof. No claim about unequal rank-dependent suit counts follows: the wreath-product orbit and constants used here depend on the same s for every rank.

## 8. Qualification and dormant work

The retained maximum-exponent lemma is closed, by a complete full-ring classical reduction and by a direct proof. A pure homogeneous Hilbert series and a total-degree-flat degeneration were insufficient routes; neither is used as a substitute. Conditioning on first feedback and invoking a smaller uniform suited game remains invalid because wrong-suit exclusions change the posterior.

Credit remains 0. The original-rule theorem above uses exactly the successor's history/evaluation argument and known colored straightening with invariant constants retained; no substantially different mechanism or new invariant-theory theorem has been isolated. The journal and later primary bodies make that overlap concrete. Independent adversarial review, novelty adjudication, a strict Lean endpoint, manuscript and extracted replay have NOT occurred. No full qualified novel endpoint survives these gates, so no Lean implementation plan is activated or presented as qualified. No Pi diagnostic or formalization is requested. The next source task, if the root chooses it, is ordinary review of the precise v1 endpoint and of whether any corrected latest rule is actually authorized by the source; it is not a mathematical enumeration task.
