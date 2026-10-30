# T115E109: exact sampling of binary cell-bounded tables

Author proof, conditional only on the stipulated pinned source theorem and ordinary exact algorithms described below. This is not an independent correctness or contribution verdict. The scope is exactly the pre-development `scope.md`; no restrictions on capacities, margins, dimensions or support have been added. No executable implementation of the source FPRAS is claimed.

## 1. Contracts and notation

Let the input and its complete binary length L be as in the frozen statement. A table is an integer matrix X with prescribed nonnegative row and column sums and 0 <= X_ij <= b_ij. Write Omega for this finite set and M for its cardinality.

The only nonclassical input to this proof is **C**, the algorithm of the pinned manuscript *An FPRAS for Cell-Bounded Contingency Tables*, introduction `thm:main`, proved in `algorithm.tex`. On every binary instance and rational relative error eta and failure probability rho, C returns a nonnegative rational estimate of M, within (1 +/- eta)M with probability at least 1-rho. A single polynomial bounds its bit operations on **every** execution in the input length, eta^{-1}, and log(rho^{-1}). It uses fair bits; empty instances return zero. We invoke this contract, not an ideal count oracle or an unimplemented spectral-gap assumption. Its forest, two lifts, transport/trace, evaluator and capped learner are already paid source operations.

Classical antecedents are Jerrum–Valiant–Vazirani (JVV), *Random generation of combinatorial structures from a uniform distribution*, TCS 43 (1986), Theorem 3.3/UGEN, Lemma 6.1, and Theorem 6.3; and Göbel–Liu–Manurangsi–Pappik (GLMP), *Perfect Sampling from Rapidly Mixing Markov Chains*, arXiv:2410.00882v2, Section 3.1, Algorithm 1/Theorem 6 and Section 6.2. The uncapped pinned companion's `prop:law-tabulation` and `thm:exact-sampling` explicitly perform the latter rare-correction operation. We prove the specific counter-output law interface instead of assuming it follows merely from rapid mixing.

Primary links: [JVV](https://www2.stat.duke.edu/~scs/Courses/Stat376/Papers/ConvergeRates/RandomizedAlgs/JerrumValiantVaziraniTCS1986.pdf), [GLMP v2](https://arxiv.org/pdf/2410.00882v2). Exact pinned paths, raw URLs, Git blob IDs and SHA256 values are in `upstream-receipts.json`.

## 2. Exact feasibility and a binary prefix tree

If a dimension is zero, the only possible matrix is the empty matrix; test all given margins for zero and decide accordingly. In positive dimensions, unequal totals are infeasible. Otherwise form a network with source-to-row capacity r_i, row-to-column capacity b_ij and column-to-sink capacity c_j. An integral flow of total sum_i r_i is equivalent to a feasible table. For example, shortest augmenting paths (Edmonds–Karp) use polynomially many augmentations independently of capacity values; residual updates and comparisons involve polynomial-length integers. This gives exact polynomial bit feasibility and, when desired, a feasible witness.

Set ell_ij = ceil(log_2(b_ij+1)) and q = sum ell_ij. Encode each entry in exactly ell_ij bits, with zero bits for a zero cap, in a fixed cell order. Then q = O(L), M <= 2^q, and there is one encoding per table. A prefix of this q-bit string imposes for each cell an integer interval [a_ij,d_ij] contained in [0,b_ij], or is immediately inconsistent. Subtract a_ij from that cell and its incident margins. The residual problem is another cell-bounded table instance; a negative residual margin is infeasible. Its full encoding length is polynomial in L, uniformly over all prefixes. All arithmetic and the construction take polynomial bit time.

Consequently the feasible-prefix tree has depth q, at most 2^{q+1}-1 nodes, exact polynomial-time emptiness tests at each node, and one feasible table at each surviving depth-q leaf. Child sets partition a parent's set. Denote their exact cardinalities by N_v. If q=0, feasibility determines the unique matrix, which we return immediately. Henceforth q>=1 and M>=1.

## 3. Fixed-accuracy estimates with confidence-independent support

Fix eta = 1/[100(q+1)]. For a feasible prefix v, run C on its translated instance with relative error eta and failure probability 1/4. Clip its output to [1,2^q]. This does not spoil a successful relative approximation: the true count lies in that interval. A failed output, including zero, becomes a positive finite rational.

Choose once and for all a computable integer polynomial B(L) dominating the every-execution running time, random-bit count and output-encoding length of these calls for **all** prefixes of inputs of length L. Such a polynomial follows from the fixed program and polynomial bound in C's stipulated contract and the polynomial bound on conditioned input size. Enlarge it to include clipping and to exceed L+q+10. Its coefficients and degree are absolute constants fixed with C, not data-dependent advice. Padding each call by unused fair bits makes its output a deterministic function of precisely B=B(L) bits. Thus each prefix's clipped output distribution is rational, with denominator 2^B and at most 2^B distinct values, each of O(B) bits. This support does not depend on a later confidence request.

For integer k>=1 take the odd integer

    r = 24(k+q+20)+1.

Let H_v be the median of r independent clipped calls at v. A median outside [(1-eta)N_v,(1+eta)N_v] requires at least r/2 failed base calls. If F is their number, independence and the base bound give

    Pr(F >= r/2) <= 3^{-r/2} E[3^F]
                  <= (sqrt(3)/2)^r <= exp(-r/8)
                  <= 2^{-(k+q+20)}.

Here E[3^{1_bad}] <= 3/2 and log(4/3)>1/4. The median is still a member of the same at-most-2^B value set, and costs polynomially many bit operations in L and k on every execution. At leaves we may set H_v=1 deterministically.

## 4. A rejection sampler with exponentially small TV error

One trial does the following, using fresh independent randomness:

1. Draw H_root and save it as Zhat.
2. Traverse the feasible-prefix tree. Test child feasibility exactly. If one child is feasible, take it with probability one. If both are feasible, draw their independent estimates H_0,H_1 and choose child i with probability H_i/(H_0+H_1). Store the product Q of the branch probabilities actually used, starting at Q=1. A child estimate already exposed is not redrawn as that node's estimate; the traversal needs only its children's estimates next.
3. At the leaf x, accept with probability min{1,1/(4 Zhat Q)}. Otherwise discard the trial and restart from the root.

All estimates are positive, so Q>0. Rational Bernoulli draws are exact: for rational a/b in [0,1], use ceil(log_2 b) fair bits to draw an integer below the next power of two, retry if it is at least b, and compare the accepted integer with a. Each attempt succeeds with probability greater than 1/2 (probability one at a power of two). This gives almost-sure termination and expected polynomial bit cost, including for bad estimates. Each trial queries at most 1+2q scalar estimates. All branch rationals, Q, and acceptance rationals have bit length polynomial in L, independently of k, because the scalar values have O(B) bits. The trial has expected cost polynomial in L,k.

For the correctness analysis only, preassign independent H_v to **every** feasible-prefix node. Lazy exposure gives exactly the preceding algorithm. This preassignment is a probability-space construction and is not performed during an ordinary run. Let G be the event that all these estimates meet their relative guarantees. The union bound gives

    Pr(G^c) <= beta := 2^{-k-19}.

Fix a complete estimate assignment in G. At each two-child split, its branch probability divided by the true count ratio lies between (1-eta)/(1+eta) and its reciprocal. At a forced split the ratio is one. Therefore, for every leaf x,

    ((1-eta)/(1+eta))^q / M <= Q(x)
        <= ((1+eta)/(1-eta))^q / M.

Since log((1+eta)/(1-eta)) <= 3eta and 3eta q < 3/100, these bounds imply 1/(2M) <= Q(x) <= 2/M. Also M/2 <= Zhat <= 2M. Thus 4 Zhat Q(x) >= 1, so the acceptance minimum never clips for this assignment, and

    Pr(trial accepts x | estimate assignment) = Q(x)/(4 Zhat Q(x))
                                             = 1/(4 Zhat).

The accepted conditional law is exactly uniform. Its total mass is M/(4 Zhat)>=1/8. Integrating only over G, the trial's accepted subprobability measure has the form

    s_x = a/M + b_x,
    a >= (1-beta)/8,    b_x>=0,    b:=sum_x b_x <= beta.

The b_x include every accepted output from bad assignments, including clipped acceptances; no correctness test for G is used. Total trial success s=a+b is at least 1/16. Independent restarts therefore terminate almost surely, with expected at most 16 trials. Their exact output law is p_k(x)=s_x/s. It is a mixture of the uniform law and a law of total mixture weight b/s<=16 beta. Hence

    TV(p_k, Uniform(Omega)) <= 16 beta <= 2^{-k}.

This argument also establishes expected polynomial bit cost. More explicitly, the expected cost of a sequence of fresh trials is the expected cost of one trial times sum_{j>=0}(1-s)^j: trial j's cost is independent of previous trials' failures. No independence of a trial's own cost and success is needed. All outputs are feasible, on all executions that halt.

## 5. Exact tabulation with only polynomial accuracy dependence

We now give a finite deterministic procedure for computing the entire law p_k. Its bit cost is at most

    2^{a(L)} (k+1)^c                                      (1)

for a fixed computable integer polynomial a and fixed positive integer c. The proof of (1), including its dependence on k, is essential.

First enumerate all prefixes and their feasibility. For each feasible prefix enumerate all 2^B padded tapes of the base clipped counter, simulate it and sort/equate rational outputs exactly. Record values v_1<...<v_t and cumulative counts h_i out of 2^B. This costs singly exponential time in a polynomial in L and is independent of k.

The exact median CDF at v_i is

    F_r(v_i) = sum_{j=(r+1)/2}^r binom(r,j)
                         (h_i/2^B)^j (1-h_i/2^B)^{r-j}.    (2)

Indeed the median is at most v_i exactly when at least (r+1)/2 draws are at most v_i. Subtract successive CDFs to get each median probability. The denominator in (2) is 2^{Br}; numerator and denominator bit lengths are O(Br). Using integer powers, binomial recurrences and schoolbook arithmetic computes these probabilities in 2^{poly(L)}(k+1)^{O(1)} bit operations. Crucially the exponent of k is absolute: enumerating the r-tuples of base outputs would not give this bound and is not our procedure.

Next enumerate one-trial macro histories, consisting of a feasible root-to-leaf path and the scalar median values queried along it. There are at most

    E = 2^{q+(1+2q)B}

such histories, independently of k. For each, multiply the probabilities of its scalar outcomes from (2), its rational branch probabilities, and its terminal acceptance probability. Accumulate the resulting mass in s_x. All rational-coin rejection loops have already been integrated into their exact rational success law; no enumeration of their bit tapes is required. All unused prefix estimates integrate to one; hence we do not enumerate an assignment of values to the full exponential tree.

A history probability has bit length at most poly(L)(k+1): there are at most 1+2q median factors of O(Br) bits, and only polynomially many additional bits for branches and acceptance. Even the deliberately inefficient operation of summing E fractions using products of their denominators has intermediate bit length at most E poly(L)(k+1). Schoolbook arithmetic for at most E such sums still costs 2^{poly(L)}(k+1)^c with an absolute c. The same bound accommodates all prefix tables, their sorting, the r-term sums (2), and enumeration of feasible leaves. It is not a unit-cost arithmetic estimate.

Compute s=sum_x s_x, which is positive by Section 4, and divide to obtain p_k(x)=s_x/s. This division accounts exactly for arbitrarily many independent trials; it is the geometric-series identity. We have thus tabulated the **actual** algorithm, including all bad estimates, all clipped acceptances, and all restarts. Its law is rational but need not be dyadic and need not have polynomial-size denominators. Singly exponential denominator bit lengths suffice here.

For clarity about effective constants in (1), each displayed enumeration bound has exponent polynomial in B(L)+q+L; each arithmetic operation uses integers of length at most 2^{poly(B+q+L)}(k+1)^{O(1)}. There are finitely many loops of explicitly specified polynomial degrees (simulation, sorting by cross-products, repeated integer multiplication, binomial recurrences, and rational summation). Taking the sum of the resulting upper-bound polynomials fixes a computable a and an integer c once and for all. Enlarge them to cover feasible-table enumeration and a rational categorical draw with weights constructed from these probabilities and O(D) additional bits. Then the latter rare-branch expected cost is bounded by

    2^{a(L)} (k+D+1)^c.                                  (3)

This is an effective polynomial majorant derived from the source's fixed every-path bound B, rather than an oracle for an unknown running time. There is no need to optimize or specify numerical source exponents to establish the existential uniform polynomial in the frozen target.

## 6. Rare exact correction

Fix the polynomials from (3), enlarging a(L)>=q+1 and c>=1. Choose the integer

    D = 16(a(L)+c+q+10)^2,     k=2D,     delta=2^{-D}.

These are polynomial functions of L with absolute constants. Section 4 gives p_k(x)<=1/M+delta^2. Also M<=2^q and D>=q, so M delta<=1. Hence

    (1-delta)p_k(x) <= (1-delta)/M + (1-delta)delta^2
                    <= 1/M.

The numbers

    R(x) = [1/M-(1-delta)p_k(x)]/delta

are nonnegative and sum to one. Flip D independent fair bits; enter the correction branch iff every bit is zero. On the complementary event run the Section 4 sampler with parameter 2D. On the correction branch enumerate Omega, compute M and p_k by Section 5, form R exactly, and sample from this rational finite law. For the latter choose a common positive denominator V and integer weights summing to V; draw a uniform integer in [0,V-1] by fair-bit rejection and scan cumulative weights. Its expected bit cost is covered by (3), and it terminates almost surely.

The resulting output law is exactly

    (1-delta)p_k + delta R = Uniform(Omega).

The ordinary branch has polynomial expected bit cost. The correction contribution is at most

    2^{-D+a(L)}(3D+1)^c,

which is bounded by one with the displayed choice of D after harmless enlargement of a. For an explicit inequality put A=a(L)+c+q+10>=12. Then D=16A^2, a<=A, c<=A and log_2(48A^2+1)<=8A for A>=12, so

    a+c log_2(3D+1) <= A+8A^2 < 16A^2 = D.

The branch decision itself costs D bits. Both branches terminate almost surely; all returned matrices are feasible. Initial exact feasibility deals with empty inputs. This proves every quantifier and cost assertion of frozen T115E109.

## 7. Hostile cases and boundaries of the claim

* Failed estimates may be zero or arbitrarily inaccurate within the source's bit bound. Clipping forces positive probabilities. Their entire accepted mass is charged to b, then exactly retained by tabulation; failures are not silently discarded.
* A support with forbidden cells can have disconnected 2-by-2 switch chains. This proof uses no switch-chain connectivity or capped analogue of the uncapped companion's repair map.
* Capacities such as 2^{2^t} contribute 2^t bits to the actual input. Complexity is polynomial in complete L, never in the numerical total capacity. The prefix depth is q, not sum b_ij.
* Rejection of the uncapped companion's uniform outputs can have exponentially small acceptance. That procedure is not used.
* Simple child count-ratio sampling at fixed relative error does not attain arbitrarily small TV error. The terminal Q-dependent rejection is indispensable to the good-assignment uniform sublaw.
* Conditioning merely on the estimates seen along a random path would risk bias. The proof conditions on a preassigned full independent tree, whose union failure bound is affordable through O(k+q) median repetition; the implementation still exposes only polynomially many nodes.
* Exhaustively enumerating all confidence-amplification random tapes costs 2^{Theta(B r)} and would defeat the rare-branch accounting. Equation (2) and enumeration of scalar outcomes, rather than repetitions, are the specific repair.
* The common branch has expected, not every-path, polynomial cost because exact rational coins and trial restarts are unbounded. This exactly matches the frozen target. No bounded-time dyadic approximation claim is substituted.
* The exhaustive branch is an explicit computation, not a supplied counting or sampling oracle. It is astronomically impractical. The theorem asserts uniform expected polynomial bit complexity, not practical performance.

The novelty of this deduction has not been established. It combines established rejection, median amplification and residual correction. The only potential contribution requiring assessment is the confidence-independent scalar-support tabulation interface and its use to bypass a capped high-accuracy Markov-chain construction. Correctness of the assembled proof and contribution eligibility require separate parent review; neither follows from artifact integrity or finite controls.
