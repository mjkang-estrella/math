# I337 — fixed-gate hidden subspaces of bounded codimension

2026-10-13. **Unreviewed parent proposal.** This is not accepted and has not received a contribution verdict. It extends the selected-frequency construction beyond prime-field logarithms to a standard black-box hidden-subgroup input. A reviewer must decide whether that is a substantial new contribution or a technical extension of R021; no separate count is presumed.

## Proposed theorem

Fix an integer r>=1. Input an odd prime q, an ambient dimension d>=r, and the standard reversible XOR oracle O_f for f:F_q^d->{0,1}^m, with promise

    f(x)=f(y) iff x-y belongs to H,
    dim H=d-r.

There should be an exact quantum oracle algorithm returning the unique reduced-row-echelon basis of H, with polynomial worst-case gates, qubits, oracle calls and uniform classical generation in d+log q+m. The polynomial degree and constants may depend on fixed r. Gates other than the explicitly charged oracle are the same one fixed finite set as R021. Controlled oracle use can instead be implemented by the usual query/copy/unquery construction. The conclusion is relative to an oracle; it does not assert efficient evaluation of an arbitrary f. For an efficiently given oracle circuit its charged implementation can be substituted. No exact QFT, input-dependent rotation, postselection or unbounded retry is allowed. Codimension r is a promise, not estimated for free. q=2 can be handled by constant-sized 2^r coefficient searches and the same basis selection argument below.

## Core: vector logarithms in a promised quotient basis

Suppose v1,...,vr have independent images modulo H and w is in their quotient span. Then the coefficient vector a in F_q^r satisfying w=sum a_i v_i mod H is unique and is verified by one test f(w-sum a_i v_i)=f(0). Prepare r+1 dyadic exponent registers with x1,...,xr,y in [0,Q), Q=1024*2^(2b), b=ceil(log2 q), and query

    f(sum x_i v_i+yw).

Clear arithmetic scratch before interference and apply the stipulated flagged polygonal transform to all r+1 exponent registers. For s in F_q^r select the output bins corresponding to (s,s dot a). A normalized character of the q^r distinct quotient labels factors the projection into r+1 copies of the R021 sum S(k,t). For t!=0 its modulus exceeds Q/3, and for t=0 it equals Q exactly. Therefore the actual selected event has probability

    p_s >= 9^(-(r+1)) q^(-r).

Take r fresh copies. A label is an invertible r by r matrix B whose rows are the sampled s vectors; the final-coordinate labels give B a. Decode a, then verify it. For each fixed B in GL_r(F_q), the correct event has probability

    p_B=product_rows p_s >= 9^(-r(r+1)) q^(-r²).

The selected event probability is exactly computable from q,s,a in polynomial bit time for fixed r. In its squared norm, two exponent tuples collide precisely when

    x_i-x_i'+a_i(y-y')=q z_i,  i=1,...,r.

These are linear constraints when a is supplied after verification. Bounds |z_i|<=Q suffice. There are 2(r+1) exponent coordinates, r congruence coordinates and 2(r+1) phase-floor coordinates, totaling 5r+4. The Gaussian-rational weight has degree 2(r+1); the same binomial lift as R021 adds at most that many coordinates. Thus a bounded number of rational-polytope counts in dimension at most 7r+6 evaluates p_s. The denominator divides Q^(4(r+1)), and p_B is also a polynomial-bit dyadic. This is fixed-dimensional counting; no claim for r growing with the input is made.

Choose a fixed integer C_r with 2^(-C_r)<=1/(2*9^(r(r+1))), and tau=2^(-b r²-C_r). Then tau<=p_B/2. Equalize the mass at each verified B to tau using R021's two-mode dyadic correction. A guessed pair (B,a) has r²+r field entries, so use rounding precision J=b(r²+r)+4. For e_B=tau-p_B C_B/2, the guessed retention 2^(b(r²+r)+1)e_B is below 1/16. The resulting total probability is exactly |GL_r(F_q)|tau, an initially computable dyadic bounded below by 2^(-r²-C_r-r). A fixed number depending only on r of repetitions raises success above 3/4. The unique-output quarter-success compiler then returns a with certainty.

All these circuits have polynomial clocks even when the quotient-basis/span promise is false: branch arithmetic uses explicit ranges and valid positive dummy values; computed p_B refers to the hypothetical linear quotient with the tested a and remains an evaluable nonnegative dyadic. Exactness is asserted only under the core promise. Invalid outer bases need no success guarantee.

## Removing the supplied quotient basis for arbitrary ambient dimension

Choose r coordinate indices from r independent ceil(log2 d)-bit strings. Reject out-of-range or non-increasing tuples. For each proposed coordinate basis I, run the bounded core circuit for every standard basis vector e_j, obtaining candidate quotient coefficients. Verify all relations with f. If all pass, these r images span the promised r-dimensional quotient, so they are independent. The relations produce H and its unique RREF basis. If I is not a quotient basis, at least one e_j lies outside its span, and no coefficient can pass its membership test. Thus an invalid I never passes final verification, regardless of behavior of the bounded core circuits off promise. At least one coordinate subset is a quotient basis.

The exact outer success probability is N_H/2^(r ceil(log2 d)), where N_H is the number of coordinate r-subsets forming a quotient basis. Given a valid RREF description of H, compute its annihilator and enumerate at most d^r subsets; ordinary rank tests determine N_H in polynomial time for fixed r. This is witness-computable, inverse-polynomial and dyadic. The verifier for H requires canonical RREF form of rank d-r and membership of every row in the hidden kernel; the rank promise makes the accepted output unique. The same quarter-success compiler therefore exactifies the outer procedure in polynomial worst-case time. Its verifier may make charged classical oracle queries.

## Remaining audit obligations

The above construction must be checked as an oracle circuit, including every normalization, canonical output encoding, good/bad-basis case, dyadic precision, actual selected event and fixed-r resource bound. In particular, the negative case is rejected by final relation checks, not by an exact decision promise secretly added to the core. All references to R021 are to already audited algebraic operations, but the multidimensional construction is a new deduction and must be independently proved. Compare exact finite-Abelian HSP work and its finite-basis/QFT-oracle distinction before claiming contribution or priority. A straight extension verdict is possible and would mean no acceptance increment.
