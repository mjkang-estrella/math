# I324 — independent operation and correctness analysis

2026-10-13. Contribution verdict: **SUBSTANTIAL within documented comparison coverage**. This analysis separately checks the new deductions needed for the contribution claim. The pinned OpenAI source is accepted as true; the parent compiler is not accepted as an axiom. These analytic checks were performed before reading the newly authorized finalized I323 proof evidence.

## 1. Concrete source interface and trial

The actual source Lemma transform tests the return of its ancillary phase register. On that outcome the unnormalized entry is Q^(-1/2) g_0(kx/Q), with the phase scratch cleared. Its proof uses bitwise Hadamards and reversible controlled shifts; its operational construction works for any power-of-two Q with at least two bits. The original contextual choice Q=B^16 is not necessary to that circuit. The candidate's 10+2b-bit registers meet that condition. Multi-controls are conjunction computations followed by source singly controlled gates. None of this introduces a QFT of order q.

The initial two-register amplitude is 1/Q. Two flagged transform entries multiply it by 1/Q, giving the group-register vector with prefactor Q^(-2), hence Q^(-4) in its squared norm. Clearing arithmetic scratch before interference is essential. The group-value register remains entangled; no x or y history is copied before interference. Later measured outputs and their classical arithmetic may be copied into orthogonal history.

The q-bin rule recovers j because |kq/Q-j| <= q/(2Q) < 1/2, and the forward equality rejects other outputs. Both labels have explicit range checks. For a nonzero j the modular inverse exists. Verification over canonical exponents [0,q) forces a'=a, so the passing event for j is precisely the pair of selected outputs and both phase flags. h=1 is handled before this argument; otherwise a and aj mod q are nonzero.

## 2. Fourier lower bound, independently derived

Represent the interpolant as four translates of the periodized triangle T(t)=max(1-4|t|,0), with translate weights (-i)^r. For the negative-exponential Fourier convention, the translate sum is four when m=1 mod 4 and zero otherwise. The triangle coefficient is (1/4)(sin(pi m/4)/(pi m/4))^2. Hence the supported coefficient is 8/(pi^2 m^2), including negative m; m=0 vanishes. Absolute summability permits substitution into the finite x-sum. Evaluating at t=0 gives sum c_m=1.

Writing k=tQ/q+eta gives exactly the candidate's argument (m-1)t/q+m eta/Q in D_Q. For m=1 the geometric-sum formula and |eta|<=1/2 give magnitude at least 2Q/pi, including eta=0 by continuity. Multiplication by c_1 gives 16Q/pi^3>Q/2.

For other m, aliases satisfy m=1+4qz with z nonzero. The bound |1+4qz|>=3q|z| implies total alias coefficient at most 8/(27q^2)<1/24, valid even at q=3. Their geometric sums have magnitude at most Q. For nonaliases |m|<=M=Q/(2q), the unperturbed distance to an integer is at least 1/q; the perturbation is at most 1/(4q). Thus the distance is at least 3/(4q), giving |D_Q|<=2q/3. For the remaining tail, floor(M)>=M/2 and the two-sided integral comparison yields sum c_m <=4/M. Its contribution is at most 8q. Counting a large alias in both estimates only increases the error bound.

Consequently |S| >= Q/2-Q/24-26q/3 >= Q/2-Q/24-9q >=5Q/12>Q/3, since Q>=216q. Q=1024B^2 satisfies that inequality and M>=2. All estimates are analytic, not a numerical scan or an implemented infinite sum.

The q computational states |g^z> are distinct. The normalized character vector therefore has norm one. Conjugating its negative character phase produces the positive exponential that factors the overlap into S(k,j)S(l,aj mod q)/(Q^2 sqrt(q)). Projection onto this unit vector bounds the actual squared norm below by 1/(81q). The character is an analytical test vector only; it is never prepared or measured by the circuit.

## 3. The paid collision-count operation

The group-state inner product is one exactly when x+ay-x'-ay'=qz for a unique integer z. Since 1+a<=q, the absolute numerator is at most q(Q-1); the written z box [-Q,Q] includes every term. Here a is supplied numerical data on a verified branch. There is no variable-variable product in this constraint.

For each original coordinate v and phase coefficient c, the floor beta=floor(4cv/Q) decomposes uniquely as 4n+sigma. Fixing the four sigma values gives 256 cases. The inequalities Q(4n+sigma)<=4cv<=Q(4n+sigma+1)-1 encode the integer floor exactly. n=floor(cv/Q) is nonnegative and less than Q. Every original tuple enters exactly one case and has exactly one choice of each n and z.

The phase on a cell is (-i)^sigma [1+(-i-1)(4cv/Q-4n-sigma)]. Its conjugate uses conjugate coefficients. Four affine factors give degree at most four in the eight nonnegative coordinates, denominator dividing Q^4, and no dependence of the weight on the potentially negative z. The overall Q^(-4) probability prefactor gives denominator dividing Q^8. Exchange of primed and unprimed coordinates conjugates the sum and sends z to -z, so the result is real; nonnegativity independently follows from the squared-norm derivation.

Expand into the bounded number of monomials of degree at most four. The identity v^d=sum_s S(d,s)s! binom(v,s) converts each monomial to a bounded linear combination of products of binomial factors. A factor binom(v,s) counts tuples 0<=t_1<...<t_s<v. Strict inequalities become integer linear inequalities, and the empty tuple handles s=0. At most four added coordinates suffice, giving dimension at most thirteen. Coefficients can be signed or complex; they multiply the returned counts outside the oracle. All boxes, constraints and coefficients have O(log Q+log q) bit lengths.

The actual [counting theorem and algorithm](https://library.slmath.org/books/Book38/files/barvinok.pdf) were read, including their local explanation of extracting the count from a short rational generating function. The input dimension is fixed before the instance. The algorithm is deterministic polynomial bit time in the polytope encoding, not polynomial in Q or its volume. Lower-dimensional rational polytopes are allowed; the equality causes no input-dependent dimension.

An independent way to avoid any full-dimensionality concern is to solve the equality for x, whose coefficient is one, and replace z by w-Q with 0<=w<=2Q. The eight remaining coordinates are nonnegative. Substitute the resulting linear expression for x into every inequality and the weight. This is a bijection on the counted integer tuples and leaves weight degree at most four. The same lift then uses at most twelve coordinates. This checks that the equality does not hide a lattice-index or dimensional complication; no change to the candidate is needed.

A fixed-dimensional count in the displayed boxes has O(log Q) output bits, since the number of coordinates is constant. Intermediate coefficients and the bounded signed combinations also have polynomial bit lengths. A probability numerator may be represented as an integer over Q^8. No general claim that all source-gate circuit probabilities are dyadic is used: dyadicity follows for this particular flagged event from its Gaussian-rational formula.

This operation differs from computing the probability of a generic quantum circuit. It exploits the known logarithm to turn equality of group outputs into one linear congruence. Without that witness the constraint is not available in this classical form. It also differs from treating q-1 labels as a polynomial-size list: each call is on the label actually produced or guessed.

## 4. Completion, clocks and the independent compiler check

tau=1/(256B)<=1/(256q)<1/(162q)<=p_j/2. Hence r_j=2tau/p_j is at most one. C_j is its downward dyadic rounding at mesh 2^(-J), and e_j=(p_j/2)(r_j-C_j) satisfies 0<=e_j<p_j 2^(-J-1). The guessed-pair retention 2^(2b+1)e_j is less than p_j 2^(2b-J)<=1/16. Every sampled threshold is a polynomial-bit dyadic; the ratio is evaluated by integer division only to compute a floor.

An ordinary passing pair contributes p_j C_j/2. A uniform guessed pair has unconditional probability 2^(-2b-1); multiplying its threshold gives e_j. The sum is tau for each nonzero label. Exactly one exponent verifies but exactly q-1 labels accompany it. Summing analytically gives P_0=(q-1)tau, with no label enumeration. Since odd prime q is strictly greater than B/2, q-1>=B/2 and P_0>=1/512.

Fresh registers and untouched old work justify independence of the fixed 1024 copies. P=1-(1-P_0)^1024>=3/4 is an initially known polynomial-bit dyadic. Selection of the first success concerns the completed retention flag. Merely choosing the first verified exponent before its filter would change the law; that is not the described algorithm.

The parent compiler is valid under its explicit extra hypotheses. Its R=2q(n) independent trials give P>=3/4, using (1-1/q)^q<=1/2; q=1 is immediate. P can be evaluated from the unique verified witness with polynomial dyadic representation. With J=L+2, downward rounding of 1/(2P) yields C, and e=1/4-PC/2 satisfies 0<=e<P2^(-J-1). The valid guessed-witness contribution is exactly e and its retention is less than P/4. Thus total success is exactly 1/4, even when P becomes computable only after a witness is found or guessed. Uniqueness makes successful branches agree. In the candidate P is already known, so only this quarter-success step is needed after its stated repetition.

All divisions are guarded by prior verification; rejected labels use dummy arithmetic and reject. A uniform fixed polynomial clock bounds classical counting and arithmetic on every branch. The source retained-record construction implements those controllers reversibly without enumerating histories. Inputs select gates at runtime through the source finite control mechanisms; they do not select new gate angles.

For psi=V|0> and G=Pi psi with ||G||^2=1/4, the two sign reflections map psi-2G to 2G. This has norm one and only canonical correct output. V and its inverse include every work/history register. The all-zero reflection is compiled from Boolean tests and S^2, holding classical input fixed. Histories need not be erased before the inverse. This is a single exact amplification step with a fixed worst-case bound.

## 5. All input orders and the contribution boundary

Exact factoring of p-1 supplies the order-stripping tests. Starting from p-1, division by ell when g^(m/ell)=1 preserves ord(g)|m and removes precisely excess prime valuations. There are O(log p) divisions and at most one terminal failed test per prime. For g=1 return immediately; p=2 therefore never requires factoring 1.

For ell^e||m, g_ell has order ell^e and gamma has order ell. If a-x_k=ell^k(d_k+ell u), the stated digit right side is g_ell^(ell^(e-1)d_k+ell^e u)=gamma^d_k. The prime-order core returns the next digit exactly, including zero digits and ell=2. After e steps CRT returns the unique exponent in [0,m). The total number of digit calls is at most log_2 m, and every binary arithmetic operand has polynomial length. Deterministic canonical classical outputs can be copied while old quantum work remains untouched; fresh work for later calls preserves both certainty and a polynomial total history bound.

These facts show that the complete result satisfies its advertised operation contract, rather than only a prime-order or expected-time variant. They do not establish historical priority. The nonroutine conjunction of a useful uniform DLog mass and its witness-computable exact collision count is what changes the guarantee under the specified basis. The generic compiler, classical counting, source per-label completion, amplification, and digit/CRT consequence are not separate substantial discoveries. Search/read limits are recorded in the two companion provenance notes.
