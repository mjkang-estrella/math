# I323 — independent analytic checks

2026-10-13. Complete-theorem proof verdict: **PASS unchanged**. The frozen candidate and internal bridge were checked independently, without assuming the bridge as an axiom. This file expands the review's derivations; none of the following checks is a numerical scan.

## 1. Gates, normalization, histories and decoding

The stipulated transform supplies an unnormalized success operator. In its actual source proof, the phase register is unprepared and success is its all-zero outcome; controlled-shift scratch is cleared. Thus on success there is no residual environment indexed by the old data x. The proof uses a phase register with at least two bits, shifts and additions modulo Q, and one H per data bit. No step requires the original parameter choice b=16n. The candidate uses log_2 Q=10+2ceil(log_2 q)>=14, so that interface is valid.

Preparation uses two log_2 Q-bit uniform registers and reversible modular powering. Each input pair has amplitude 1/Q. Each successful transform adds a factor 1/sqrt(Q), yielding 1/Q² after both; probability therefore has prefactor 1/Q^4. The group-value register is intentionally left entangled. Every other arithmetic scratch register is cleared before interference, and x,y have no history copies until their interference is complete. The phase flags are measured or computed as tested events, without renormalization.

For a genuine bin k=k_q(j), |kq/Q-j|<=q/(2Q)<1/2. Rounding recovers j uniquely. Range checking 0<=j<q and testing the exact forward bin equality reject all other k; adjacent bin centers differ by Q/q>1. For odd q the jQ/q half-tie cannot occur, since q is coprime to Q, although the declared floor rule would still fix a tie. The same argument holds for l. Since g has order q, the verifier accepts precisely a'=a among 0<=a'<q. With j!=0 it follows that j'=aj mod q. Conversely those two bin outputs and both phase successes pass the decoder and verifier. Hence p_j really is the specified one-output-pair probability.

## 2. Fourier coefficients and error classes

Let T(t)=max(1-4|t|,0), supported on [-1/4,1/4], and periodize it. The polygonal interpolant is the sum over r=0,1,2,3 of (-i)^r T(t-r/4). With the negative-exponential expansion convention, its m-th coefficient uses the integral against exp(+2pi i m t). The translate sum is sum_r exp(2pi i(m-1)r/4), equal to 4 exactly for m=1 mod 4 and zero otherwise. The kernel coefficient is (1/4)(sin(pi m/4)/(pi m/4))². Their product is 8/(pi²m²) on the supported class. At m=0 the translate sum vanishes. In particular, m=-3,-7,... belong to the expansion and have positive coefficients; reversing the sign convention would change the supported residue class.

The coefficients have an absolutely summable 1/m² bound. The series converges uniformly to the continuous interpolant, and evaluation at t=0 gives sum c_m=1. Finite summation over x may therefore be interchanged with the series. Substituting k=tQ/q+eta gives the written D_Q argument (m-1)t/q+m eta/Q exactly.

For the main term, if eta!=0,

    |D_Q(eta/Q)|=|sin(pi eta)|/|sin(pi eta/Q)|
                       >=2|eta|/(pi|eta|/Q)=2Q/pi.

At eta=0 it equals Q. Thus its coefficient-weighted magnitude is at least 16Q/pi³>Q/2. This strict elementary constant comparison is valid independently of q.

For m!=1, the following sets cover all supported integers:

- A: all aliases m=1+4qz, z!=0;
- N: nonaliases with |m|<=M=Q/(2q);
- T: all supported m with |m|>M.

A and T can overlap. Applying a positive upper bound twice to an overlapping term is safe for the triangle-inequality error estimate. The main term lies in none of them because M>=2. Primality and t!=0 imply q divides (m-1)t precisely when q divides m-1. Combining with m=1 mod 4 and odd q gives the displayed alias progression, including its negative terms. For z!=0,

    |1+4qz|>=4q|z|-1>=3q|z|,
    sum_A c_m <= (8/pi²)/(9q²) * sum_(z!=0)1/z²
                 =8/(27q²)<=8/243<1/24.

The alias contribution is at most Q times that sum. For N the unperturbed argument has distance at least 1/q from the integers. The perturbation has magnitude at most 1/(4q); the distance function is Lipschitz, so the resulting distance is at least 3/(4q). The geometric-sum bound |D_Q(v)|<=1/|sin(pi v)| and |sin(pi v)|>=2dist(v,Z) give 2q/3. Sum_N c_m<=1.

For T let N_0=floor(M). Since M>=2, N_0>=M/2. Ignoring the residue restriction and using 8/pi²<1 gives

    sum_T c_m <=2 sum_(n>N_0)1/n²<=2/N_0<=4/M.

This includes both signs and works for noninteger M. The tail contribution is at most 4Q/M=8q. Consequently

    |S|>=Q/2-Q/24-26q/3
        >=11Q/24-9q>=10Q/24=5Q/12>Q/3.

The last comparison follows from Q>=216q. Here B>=q and Q=1024B², so the comparison and M>=2 hold uniformly, including q=3. eta=0 does not break any denominator estimate or the class coverage. There is no need to sum this infinite Fourier series algorithmically: it is solely a convergence and lower-bound argument.

## 3. Character projection

Distinct z modulo q give distinct computational basis states |g^z>. Hence chi_j has norm one; pairwise character inner products are the elementary q-term geometric sums, zero for different j. For the actual output vector v_(k,l), taking the bra chi_j conjugates its negative character phase to exp(+2pi i jz/q). Because the group exponent is x+ay modulo q, its overlap becomes

    <chi_j|v_(k,l)>
      =(Q² sqrt(q))^(-1)
        [sum_x g_0(kx/Q) exp(2pi i jx/q)]
        [sum_y g_0(ly/Q) exp(2pi i (aj mod q)y/q)].

Both sums factor because x,y are independently ranged and the character is multiplicative on addition. Choosing the accepted k,l makes both frequencies nonzero: h!=1 implies a!=0 and q is prime. Cauchy–Schwarz gives

    p_j=||v_(k,l)||²>=|<chi_j|v_(k,l)>|²>=1/(81q).

No character state is part of the implemented circuit, and no measurement of the group register is needed for this inequality.

## 4. Nine-variable count and dimension thirteen

Squaring the vector norm yields a sum over four inputs. Inner products of group states impose equality of their exponents modulo q, exactly the stated linear constraint with a unique integer z. For canonical 1<=a<=q-1,

    |x+ay-x'-ay'|<=(1+a)(Q-1)<=q(Q-1),

so |z|<=Q-1 whenever the equality holds. Allowing [-Q,Q] is harmless. z is the only potentially negative counted variable.

In each of the 256 choices of the four sigma residues, use coordinates

    x,y,x',y', n_x,n_y,n_x',n_y', z.

The original four have integer bounds [0,Q-1]. For a phase with coefficient c in [0,Q-1], quarter index beta=floor(4cv/Q) decomposes uniquely as beta=4n+sigma with 0<=sigma<4. Its integer characterization is exactly

    Q(4n+sigma)<=4cv<=Q(4n+sigma+1)-1.

The -1 is on the integer numerator comparison; it does not approximate a real floor. Since n=floor(cv/Q) and cv< Q², 0<=n<Q, so the written upper bound n<=Q never truncates the sum. Every original tuple has exactly one cell in the residue partition. Each feasible tuple has exactly one n for each factor and one z.

The interpolation parameter u=4cv/Q-4n-sigma lies in [0,1). Periodicity removes 4n from the phase power, yielding (-i)^sigma(1+(-i-1)u). Conjugated factors have conjugated coefficients. Each factor is affine in the original coordinate and its n; c is a supplied integer coefficient, so it adds no counted variable. Their product has total degree at most four in eight nonnegative coordinates. Multiplying by Q^4 clears its Gaussian-rational denominators. No weight depends on z.

For a monomial product v_i^(d_i), sum d_i<=4. The integer identity

    v^d=sum_(s=0)^d Stirling2(d,s) s! binom(v,s)

holds for v>=0 (the constant case uses binom(v,0)=1). A product of binomial factors is the number of independent strictly increasing tuples for each coordinate. Their integer inequalities are 0<=t_1, t_r+1<=t_(r+1), t_s<=v-1. Empty tuples have multiplicity one; infeasible tuples when v<s correctly contribute zero. Their total coordinate count is sum s_i<=sum d_i<=4. Thus each unweighted count lies in dimension 9+sum s_i<=13 and remains bounded. Signed real and imaginary coefficients are applied to the resulting integers outside the counts.

There are a bounded number of degree-four monomials in eight variables and a bounded number of Stirling expansion terms, multiplied by only 256 residue choices. The dimensions and number of constraints are constants. The cited external counting interface was checked on the actual primary Theorem 4.4 and Algorithm 5.2, not a summary. It applies to rational polytopes, including equalities encoded as two inequalities. This yields a deterministic polynomial bit-time algorithm for each supplied q,j,a, with no q-sized table or Fourier-frequency summation.

The polynomial's denominator divides Q^4; the probability prefactor adds Q^4. Swapping primed/unprimed variables conjugates the weight and changes z to -z, preserving the domain, so the imaginary sum vanishes. Nonnegativity follows independently from its squared-norm derivation. The probability has a representation N_j/Q^8 with 0<=N_j<=Q^8. For intermediate output-length checks, all nine original coordinates lie in boxes with O(log Q) bit endpoints, and the four lifted coordinates do too. A count has O(log Q) bits since dimension is fixed. Expanded coefficients and the bounded number of signed arithmetic operations have O(log Q+log q) bit operands up to constant factors; the counting algorithm's internal resources have their own fixed polynomial bound. Its ordinary rational arithmetic is not a random coin. Since Q is a power of two, final probability denominators are dyadic with exponent at most 8log_2 Q.

## 5. Retentions, multiplicity and repeated preparation

Because B>=q,

    tau=1/(256B)<=1/(256q)<1/(162q)<=p_j/2.

Let r=2tau/p_j. It lies in (0,1]. The floor C_j rounds r downward to a dyadic grid of mesh 2^(-J), so 0<=C_j<=1 and

    e_j=(p_j/2)(r-C_j),  0<=e_j<p_j 2^(-J-1).

The ordinary/guess branch choice has probability 1/2. Each guessed pair has probability 2^(-2b) within its branch; multiplying by its retention 2^(2b+1)e_j gives unconditional mass e_j. This retention is nonnegative and less than p_j 2^(2b-J)<=1/16. Both e_j and the scaled retention are dyadic; only a scaled exact integer floor, not a sampled nondyadic ratio, is involved in C_j.

For the actual h!=1, exactly one exponent a in [0,q) verifies. The valid labels are precisely j=1,...,q-1. Thus there are q-1 verified pairs and one canonical logarithm, and their total mass is (q-1)tau without enumerating them. As odd q lies strictly above B/2 and is integral, q-1>=B/2. This establishes the stated P_0>=1/512, including the smallest orders, without using the weaker bound B<2q alone.

Rejected ordinary outputs or bad guesses need no p_j evaluation. The specified sequence requires verification before the retention computation; guard that computation on the passing bit and use a positive dummy denominator elsewhere. All canonical verified pairs satisfy the proven lower bound. Reversible guarded evaluation and fixed clocks give bounded arithmetic on every history. No membership oracle or witness is available before it is found or uniformly guessed.

Run 1024 copies with fresh quantum registers and coins, retaining each history. Conditioning on an earlier measured history fixes only classical parameters; untouched old work factors from each fresh trial operation. Independent failure probability is therefore (1-P_0)^1024. Since (1-1/512)^512<=1/2, this is at most 1/4. Taking the first successful result uses the completed retention flag, not mere exponent verification without its retention. Every such result is the same a; the first-choice index and labels remain histories. P is an initially known dyadic. Its denominator exponent is at most 1024(b+8), polynomial in input length despite exponentially large Q and q.

## 6. Independent check of the parent compiler and amplification

For the generic bridge take its known polynomial bound q(n)>=1. With R=2q(n), fresh repeated copies give P=1-(1-p)^R. For q(n)>1,

    1-1/q(n)<=1/(1+1/q(n)),
    (1+1/q(n))^q(n)>=2,

so failure is at most 1/4. q(n)=1 gives p=P=1. If p has polynomial denominator exponent, so does P, because R is polynomial. Witness-dependent evaluation is performed only after verification. The guess branch can also compute P using its unique valid y; uniqueness ensures it agrees with the ordinary branch.

For a unique canonical L-bit output and J=L+2, let r=1/(2P). Then r<=2/3 and the dyadic floor C obeys 0<=C<=1. The residual is

    e=1/4-PC/2=(P/2)(r-C),
    0<=e<P 2^(-J-1).

A valid guessed witness has unconditional mass 2^(-L-1), and its retention 2^(L+1)e is less than P/4<=1/4. Ordinary mass PC/2 plus guessed mass e is exactly 1/4. The verifier's uniqueness, not any prior knowledge of y, makes both successful outputs agree. Invalid guesses reject with bounded dummy arithmetic. These are the bridge's existing hypotheses and implementation, not added ones. For the candidate after its 1024 copies, P is already known; choose the canonical b-bit exponent with range and powering verification and apply exactly this construction. No reapplication of the bridge's initial repetition stage is necessary.

Write psi=V|0>, Pi for the final success projector, and G=Pi psi with ||G||²=1/4. The success sign gives psi-2G. Its inner product with psi is 1/2; hence

    (2|psi><psi|-I)(psi-2G)=2G.

The resulting vector has norm one and exclusively correct output support. The reflection is V(2|0><0|-I)V^(-1) on all workspace and histories, with classical input held fixed. The source implements the middle multi-control sign and its inverse exactly; a possible global sign is immaterial. There is no need to erase history separately before amplification. Discarding history before this inverse would be invalid, but neither draft does so.

## 7. Uniform worst-case circuit and full-order extension

All bit lengths determining the prime core satisfy log Q=10+2ceil(log q)=O(log p). The counting theorem has fixed maximum dimension 13, so its exponent in the polynomial clock is constant. Each classical algorithm has a single uniform reversible implementation; classical labels are runtime inputs, not compiled advice. Primitive gate addresses can be selected by the retained controller on polynomial workspace. Additional controls use a reversibly computed conjunction, a singly controlled primitive, then conjunction cleanup. Inverting a controlled primitive is the controlled inverse, already available. The complete inverse reverses every gate and retains all prior work until that point.

Read-only inputs of fixed length can control the preparation and its inverse, giving a single uniform circuit per input length. Every branch is clocked and has polynomial space; run-dependent b and zero/default branches are managed by polynomial controller overhead. The constant 1024 repetitions and the one amplification step preserve polynomial gates and qubits. The model permits histories rather than requiring intermediate reset or postselection. Arbitrary polynomial-time classical rational computations remain Boolean networks over NOT/CNOT/Toffoli.

For full order initialize m=p-1 and strip a factor ell whenever g^(m/ell)=1. With true r=ord(g) dividing m, the test is equivalent to r dividing m/ell, so this preserves r|m and terminates with every prime valuation of m equal to that of r. The successful divisions number at most log_2(p-1); at most one failing test per distinct prime is needed after its stripping, so total tests remain O(log p). Exact factorization has deterministic canonical classical output with certainty, so copying it and retaining its quantum history supplies fixed subsequent parameters.

For a full prime-power factor ell^e of m, g_ell=g^(m/ell^e) has order ell^e, h_ell=g_ell^a, and gamma has order ell. At stage k write a-x_k=ell^k(d_k+ell u), with d_k in [0,ell). Then

    (h_ell g_ell^(-x_k))^(ell^(e-1-k))
       =g_ell^(ell^(e-1)d_k+ell^e u)=gamma^d_k.

Thus the promised prime-order core applies, including its h=1 branch for zero digits. Updating x_(k+1) gives the induction invariant modulo ell^(k+1). At stage e, x_e is the canonical residue a mod ell^e. CRT on the coprime full prime powers returns the unique a in [0,m). The sum of the e values is at most log_2 m; all powers, inverses and CRT arithmetic have polynomial-length binary operands. The cases ell=2, g=1 and h=1 are explicit and exact. For p=2 the only nonzero base is g=1, so the algorithm returns before factoring p-1=1.

Later calls use fresh zero workspace with old histories untouched. On classical promised inputs their previous successful outputs are deterministic, so they cannot carry an uncertain classical parameter to the next call. Copy-and-uncompute is also available because a probability-one canonical classical output factors from its garbage. Either described implementation preserves exactness with polynomial total histories. The optional invalid-promise checks are compatible with prime-field subgroup membership h^m=1 and do not enlarge the claimed promised-input theorem.

## 8. Status and limits

Every assertion used in Sections 1–7 has been checked as written. No repair, weakened theorem, computed rotation, expected-time retry, dense-matrix implementation or hidden exponential sum is needed. The analytical Fourier projection is not an executable subroutine. The internal compiler's witness-computable law is independently justified, not stipulated. Source truth is accepted only for the pinned corpus; classical fixed-dimensional counting is separately supported by the primary reference.

The original attribution and novelty limits remain. The review gives no earlier-proof or contribution verdict, no new accepted finding, and no priority claim. Workflow failures and source-reading boundaries are recorded separately in reading-and-failures.md.
