# I338 — independent full-scope operation analysis

2026-10-13. Contribution verdict: **TECHNICAL relative to R021**. These are analytic checks and an explicit reduction to the accepted operational construction. They are not a formal certificate or a separate independent full proof verdict. No numerical scan is used. The stipulated pinned OpenAI theorems are accepted as true; the new deductions below are checked independently.

## 1. Dependency contract and limitations of an opaque DLog reduction

R021 supplies the flagged polygonal operator A_Q(k,x)=Q^(-1/2)g_0(kx/Q), its scalar selected-frequency bound, the floor-cell/weighted-count representation, per-label dyadic completion, and the unique-output compiler with a witness-computable dyadic success law. Its external classical input counts integer points in a rational polytope in every fixed dimension. The fixed gate set and retained-record machinery are read directly in the pinned Sections 2, 3 and 6. The I323 proof and I324 contribution records explain why the scalar probability evaluator and lower bound were paid together.

The modular theorem alone does not furnish a map from arbitrary coset labels to powers modulo a convenient prime. Such a map could require knowing H and cannot be supplied for free. Nor can arbitrary label encodings be multiplied without a supplied operation oracle. The reduction here reuses the accepted circuit construction at its actual equality-of-output-state interface, and explicitly extends its constant-dimensional classical count. It does not assume an unproved embedding or exact QFT implementation.

Fix r>=1 once for the circuit family. Let b=ceil(log2 q) and Q=2^(10+2b). The ambient oracle input is a canonical d-tuple of b-bit field residues. Standard arithmetic on d coordinates costs polynomially many Boolean gates in d and b. Its size db and the output size O(d^2 b) are polynomial in d+b+m. The oracle's action on invalid encodings need not be known because the query input is always reduced modulo q.

For prescribed v_1,...,v_r,w, compute u=sum x_i v_i+yw modulo q, query O_f with zero label target and uncompute u's arithmetic scratch. The exponent registers and f(u) remain; no pre-interference exponent copy remains. Each preparation uses one charged query. Every inverse query is charged. A controlled XOR query at an arbitrary label target t uses a fresh label register: query f(u) into it, controlled-XOR it into t, and query again to clear it. This costs two calls and does not require controlled access as an extra oracle primitive. Membership testing can query f(u) and f(0) separately; either charge both or charge the initial computation of a reusable f(0). Guarded classical controllers and all reflections use the same gates as R021.

## 2. Constant-dimensional vector trial

Assume only for this section that v_i+H form a quotient basis. The quotient coordinate map z->Vz+H is bijective onto F_q^d/H, whose labels are therefore q^r distinct computational basis states. For the unique a with w=Va mod H, the post-transform label vector at output k=(k_1,...,k_r,k_y), on all successful phase flags, is

    v_k = Q^(-(r+1)) sum_(x_1,...,x_r,y<Q)
              [product_i g_0(k_i x_i/Q)] g_0(k_y y/Q)
              |f(V(x+a y))>.

There are r+1 uniform registers, initial amplitude Q^(-(r+1)/2), and r+1 flagged entries adding the same factor again. Thus the prefactor is Q^(-(r+1)), not a normalized transform on a forced successful branch.

For analysis only define

    chi_s = q^(-r/2) sum_(z in F_q^r)
                exp(-2 pi i s dot z/q) |f(Vz)>.

Its norm is one because all the labels are distinct. Its bra gives the positive character exponent. With k_i=k_q(s_i) and k_y=k_q(s dot a), where k_q(t)=floor(tQ/q+1/2), the overlap is

    <chi_s,v_k> = [Q^(r+1) q^(r/2)]^(-1)
                   [product_i S(k_q(s_i),s_i)]
                   S(k_q(s dot a),s dot a).

No chi_s is prepared or measured, and no q^r labels are enumerated. R021's uniform scalar bound applies to each nonzero frequency. At t=0, k_q(0)=0 and S(0,0)=Q since g_0(0)=1. Consequently

    p_s=||v_k||^2 >= 9^(-(r+1)) q^(-r).

Zeros in s, in a or in s dot a do not cause a gap. Bin decoding uses rounding of kq/Q and a forward equality/range test; error is at most q/(2Q)<1/2, so the mapping is injective. Take r fresh trials. Require their r decoded first-coordinate rows to form B in GL_r(F_q), let ell be their last-coordinate labels, set a'=B^(-1)ell and test f(w-Va')=f(0). On the promise the verifier forces a'=a, hence ell=Ba. For a fixed B its verified ordinary event is precisely the product of the r chosen bin/flag events. Fresh trial registers and untouched prior work give

    p_B=product_rows p_s >= 9^(-r(r+1))q^(-r^2).

This is a fixed-size tensor and linear-system extension of the scalar event. It is not r independent scalar logarithm calls: the shared y in each trial couples the quotient coordinates. The next section addresses that coupling explicitly.

## 3. Actual squared norm and exact counting

For supplied numerical a and selected output k, the exact raw event law is

    p_s = Q^(-2(r+1)) sum_(colliding tuples)
              product_(r+1 phases) g_0(c v/Q)
              product_(r+1 primed phases) conjugate(g_0(c v'/Q)),

where all 2(r+1) exponent variables range from 0 to Q-1. Collision means exactly

    x_i-x_i'+a_i(y-y')=q z_i, i=1,...,r.

For canonical 0<=a_i<q the absolute left side is at most (1+a_i)(Q-1)<=q(Q-1), so |z_i|<=Q suffices. The a_i are input coefficients to this classical count, not counted unknowns. A common y creates several linear constraints on the same variables, which the rational-polytope interface already permits.

For each of the 2(r+1) phases use beta_v=floor(4cv/Q)=4n_v+sigma_v. Fix the sigma_v in {0,1,2,3} and impose

    Q(4n_v+sigma_v) <= 4c v <= Q(4n_v+sigma_v+1)-1,
    0<=n_v<=Q.

The -1 gives the exact integer floor partition, including zero c. Its phase is the same affine Gaussian rational as R021:

    (-i)^sigma_v [1+(-i-1)(4cv/Q-4n_v-sigma_v)].

There are 2(r+1) exponent variables, r congruence variables and 2(r+1) floor variables: 5r+4 in total. The weight has degree at most 2(r+1), has denominator dividing Q^(2(r+1)), and contains no negative z_i. Expand its bounded number of monomials, then use R021's identity

    v^h = sum_(t=0)^h Stirling2(h,t) t! binom(v,t)

on each nonnegative weighted coordinate. A binomial factor counts increasing integer tuples 0<=u_1<...<u_t<v. All additional constraints are linear, and at most 2(r+1) new variables suffice. Thus dimension at most 7r+6 handles every count. For r=1 these are exactly the nine/thirteen-coordinate bounds of R021. The number of phase cells, monomials and lifted counts depends on fixed r alone.

All coefficients, bounds and supplied phase bins have O_r(log q) bits. The weighted sum and its fixed-dimensional counting calls have polynomial bit resources for fixed r. Imaginary parts cancel by exchanging primed/unprimed tuples and negating z. Nonnegativity follows from the squared-norm derivation. The phase denominators together with the norm prefactor give denominator dividing Q^(4(r+1)), hence an exact polynomial-bit dyadic. p_B is the product of r such values, still polynomial-bit. No enumeration of q frequencies, q^r labels, exponent ranges of length Q or oracle outputs is performed.

Lower-dimensional equalities can also be eliminated by solving for each x_i, whose coefficient is one. Shift z_i to z_i+Q to make all remaining coordinates nonnegative; substitute the resulting affine x_i expression into the bounds and weight. This is a bijection of integer tuples and leaves the degree fixed. It supplies an alternative count interface if one wants to remove affine equalities before calling a counter. No new counting theorem is needed.

## 4. Completion of the core and behavior off promise

Write k=r(r+1) and choose a fixed C_r satisfying 2^(-C_r)<=1/(2*9^k). Put tau=2^(-b r^2-C_r). Since 2^b>=q,

    tau <= 9^(-k)q^(-r^2)/2 <= p_B/2.

Let W=b(r^2+r), J=W+4. For valid B,a use the same completion arithmetic as R021:

    C_B=2^(-J)floor(2^J * 2tau/p_B),
    e_B=tau-p_B C_B/2.

Then 0<=C_B<=1 and 0<=e_B<p_B 2^(-J-1). Choose ordinary versus guessing mode with a fair bit. In ordinary mode require the verified B,a and retain with C_B. In guessing mode choose W fair bits, reject invalid encodings or singular B, verify a and retain with 2^(W+1)e_B. This last threshold is less than p_B/16<=1/16. The mass of a particular guess in the entire preparation is 2^(-W-1), so the residual contribution is exactly e_B. Each B therefore has mass tau.

There is one a and exactly

    |GL_r(F_q)| = product_(i=0)^(r-1)(q^r-q^i)
                = q^(r^2) product_(j=1)^r(1-q^(-j))

valid B labels. Their total p_0=|GL_r(F_q)|tau is initially computable without enumerating matrices. Each last factor is at least 1/2 and q/2^b>=1/2, so

    p_0 >= 2^(-r^2-C_r-r).

This bound is a positive constant for fixed r. Take K=2^(r^2+C_r+r+1) fresh copies, a fixed constant depending only on r. Then P=1-(1-p_0)^K>=3/4 by the same elementary repeat bound as the accepted compiler. P is a dyadic with polynomial denominator length. Encode a in rb bits and use the accepted quarter-success construction. The two masses PC/2 and residual e total exactly 1/4, and the retained unitary plus one ordinary reflection iteration returns a with certainty on the core promise.

The promise is not silently strengthened to include an exact decision oracle for valid I. Every range check, count, floor and arithmetic computation has an explicit polynomial clock on arbitrary v_i,w. For a canonical guessed a and invertible B, the computed probability can always be taken from the hypothetical injectively labeled quotient F_q^r with relation w=Va; this gives a nonnegative dyadic, a positive lower bound and safe thresholds on every arithmetic branch. Reject malformed B/a before a division or use fixed positive dummy values. Off promise the actual collision law may differ, the verifier may accept multiple coefficients, and quarter success need not hold. The implemented preparation and its reflections nevertheless remain valid bounded unitary circuits. They may output arbitrary candidates. The outer proof below does not require any further guarantee.

## 5. Removal of the unknown quotient basis

Let h=ceil(log2 d) and D=2^(rh). Guess r independent h-bit coordinate indices, using indices 0,...,d-1, and accept only strictly increasing in-range tuples. Every size-r subset has exactly one preimage of mass 1/D. For a subset I let V consist of those coordinate columns. For every j in 0,...,d-1 run the total bounded core on w=e_j and obtain an rb-bit coefficient vector, with a defined candidate default on any internal failure. Check every relation

    u_j=e_j-Va_j,    f(u_j)=f(0).

When I is a quotient basis, each core call is promised and certain. Prior work is retained; a certain classical a_j factors from its garbage, so later calls have fixed classical parameters and fresh work. All checks pass with probability one.

When I is not a quotient basis, its quotient span has dimension <r. The coordinate images e_j+H span the whole r-dimensional quotient, so at least one is outside this smaller span. For that j, every a_j gives u_j outside H. Its relation check fails for every possible core output and history. Thus no invalid I passes, even though the core is unrestricted off promise. Rejecting merely on its own success bit would not have sufficed; the final relation checks are essential.

On a passing tuple all u_j are in H, and all coordinate images lie in the span of V. As V has r columns and the quotient dimension is r, their quotient images must be independent. For j in I, a_j is the corresponding unit vector and u_j=0. For j outside I, the non-I coordinates of u_j form the standard coordinate vectors. These d-r vectors are independent, belong to H and therefore span H. Elimination returns its unique RREF. The verifier for an arbitrary guessed RREF string checks canonical field encoding, exact RREF form, rank d-r, and row membership in H with charged queries. A (d-r)-dimensional subspace contained in H equals H, so the accepted canonical string is unique.

Consequently the raw outer passing probability is EXACTLY

    p(H)=N_H/D,

where N_H counts coordinate subsets forming a quotient basis. It is not a product of uncertain core success probabilities, since the core has already been made certain on every valid subset, and no invalid subset passes.

Given the valid RREF string, compute any full-rank r by d annihilator matrix A with ker A=H. Its quotient map identifies e_j+H with column j of A. A subset I is a quotient basis iff det A_I!=0. Changing the chosen annihilator basis multiplies every submatrix on the left by an invertible matrix, so this predicate and N_H are invariant. Enumerate at most binom(d,r)<=d^r subsets and count their ordinary field rank tests. This takes deterministic polynomial bit time for fixed r. The count has O_r(log d) bits; at least one basis exists because A has rank r. Thus

    p(H)>=1/D,    D<= (2d)^r.

This is precisely the accepted compiler's extra hypothesis: exact dyadic probability computed only from a unique valid witness. It is not a probability computation for a general circuit.

For a concrete polynomial bound use R=2D independent outer runs. Then P(H)=1-(1-p(H))^R>=3/4. Its denominator exponent is at most Rrh, polynomial in d for fixed r. A fixed padded RREF encoding uses L=(d-r)db bits, with the zero-row case d=r having its unique empty encoding. Put J_*=L+2 and compute, only on valid witnesses,

    C=2^(-J_*)floor(2^(J_*)/(2P(H))),
    e=1/4-P(H)C/2.

The ordinary half-mode has mass P(H)C/2. The guessing half-mode samples an L-bit RREF candidate, verifies it and retains the unique valid guess with 2^(L+1)e, contributing e. Rounding bounds this retention below P(H)/4. Both successful modes compute identical N_H from the identical valid witness. The mass is exactly 1/4 even though H was unknown before preparation. Retain all histories and apply the source sign/reflection construction including every query in the unitary and its inverse. The resulting vector has only correct canonical output support. No postselection or unbounded repetition occurs.

For d=r the relation construction produces H=0, and N_H=1; the same formulas are valid. d=1,r=1 uses zero index bits and one valid tuple. For q=2, the core enumerates at most 2^r coefficient strings, tests relations and returns the first passing candidate with bounded Boolean logic. On a genuine basis there is exactly one; on an invalid basis the same outside-span relation rejects. The outer count and compiler are unchanged.

## 6. Contribution and proof boundaries

The construction above accounts for arbitrary unknown H and ambient d without letting counting dimension grow. Its entire non-oracle gate alphabet is unchanged, every oracle implementation is charged, and all repetition counts are fixed worst-case functions. Gate/qubit/classical generation and query resources are bounded by (d+b+m)^(c_r) for some constant c_r. The large constants from fixed r are permitted; no practical efficiency estimate is asserted.

The coupling obstruction in the vector core is exactly r linear collision equations with a known verified coefficient vector. The selected estimate is a product of the paid scalar estimate, and the classical probability evaluator uses the same weight lift with a fixed larger dimension. The outer obstruction of an unknown basis is handled by polynomial coordinate guessing and a witness-computable matroid basis count, directly feeding the paid compiler. These are explicit technical extensions. They do not construct a general exact QFT, solve variable-r counting, or invent a new state-conversion operation.

The primary literature comparisons are bounded by the ledger. They exclude a direct duplicate implementation under the stated finite gate set in the inspected algorithms, but do not establish worldwide priority. This conclusion rests on a positive operation-level relationship to R021 rather than absence of search results. No decisive flaw was found in these checked mathematical steps. Full independent proof review, if separately commissioned, remains a distinct gate.
