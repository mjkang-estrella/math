# H031 — Independent review of the adjacent-rotation trial

2026-10-08. **Independent review recommendations only. All new H031 deductions
remain UNACCEPTED pending coordinator disposition. Verified COMPLETE classical
factoring complexity improvement: NONE.**

**Disposition:** accept the scoped algebraic core and the conservative per-trial
bound, with the explicit proof and access completions below; revise the claim
of a completely specified sampler and the wording of its relation to prior art;
reject this submission as a new complete factoring improvement. Close only this
submitted realization as a proposed improvement. Neither zero useful mass nor
an impossibility theorem for adjacent rotations has been proved.

The report's conditional probability is correct for an exact, uncapped execution:

    Pr(proper split | fixed valid retained data t)
       = 2^(-c_t-1) if chi_t is nontrivial, and 0 otherwise.

This includes nonsquare root failures. Its validity does not establish favorable
c_t or chi_t. The complete-trial formula also survives. Its per-trial bit-cost
majorant can be justified as O(B^3 poly(n)) = L_N[1/3,3+o(1)], including the
large field products and both exact root calls. It is not a successful expected
factoring bound without division by the actual success probability.

## 1. Scope, evidence, and provenance

I read all 553 lines of the frozen H031-submitted-draft.md, the complete original
brief, the historical organizing intake and construction intake, the project
instructions and current STATE, H027's disposition and prior-art note, and all
866 lines of the accepted corrected H028 report with its disposition. These
inputs supply accounting and reconstruction dependencies, not a useful-yield
law for H031. STATE was frozen at review intake, not represented as the earlier
STATE seen by the proposer.

Independent document checks reproduced the reported counts: 12/12 delivery
entries, 8/8 source records, and 11/11 owned-artifact records match. Of the
12 original input entries, 11 match; only the legitimately mutable STATE differs.
The submitted snapshot and original report have identical SHA-256
`d5a3b605756de25926bb34be6bb82bf2144a8de4b4aeae04b5623b1fa37abffb`.
The construction intake has SHA-256
`86fbd089b905c18a0a84232542fb6c21eb26d7da2a787d0730379198cb2d3b00`.
These checks establish document identity, not mathematical correctness.

Frozen inputs, copied primary archives, fresh LLL source retrieval, actual reading
scope and final artifact seals are recorded in
[review provenance](H031-review-provenance.json),
[retrieval record](H031-review-retrieval.json), and
[delivery seals](H031-review-delivery.sha256).

I did not read H030's draft, review, sources or task registry, and did not poll it.
References to its ownership in required STATE/brief documents were unavoidable
context only. I ran no candidate, finite mathematical experiment, sweep, numerical
replay, benchmark, implementation, test suite or Lean command. All executed
processing was source retrieval, document reading/copying, PDF rendering, and
provenance hashing/checking. Only the authorized H031 review paths were written.

## 2. Decisions on the major claims

1. **ACCEPT: N-only parameters, finite exceptional branch, monic polynomials,
   height bounds and coupling identities.** Their proofs are in §3. The promise
   is distinct Blum semiprimes; no all-composite theorem is supported.
2. **ACCEPT: paid finite relation stream, good-prime labels, separate field
   blocks, cap and uniform parity-kernel sampling.** Duplicates and underfilled
   quotas are legitimate retained data, not rank or supply guarantees (§4).
3. **ACCEPT with proof completion: actual-square subspace, derivative-localized
   reduction, packet normalization, root-sign invariance and character law.**
   Arbitrary field fractions must not be reduced modulo N. Section 5 supplies
   the required localization and a denominator-cleared overlap identity.
4. **ACCEPT with a specification clarification: conditional and full-trial
   success identities.** Both are exact for any fixed deterministic completion
   of the setup order. The text needs that order to identify one literal A_N;
   §6 gives an admissible completion and covers every failure class.
5. **ACCEPT with expanded accounting: O(B^3 poly(n)) pathwise trial work.**
   Section 7 identifies Lenstra's variables and checks prime construction,
   finite fields, lifting, LLL, output widths, verification and sequential access.
   The full field input is not polynomial-size in n alone.
6. **ACCEPT: iid expected-work quotient E[T_trial]/sigma_N when sigma_N>0.**
   Correlation of cost and success within a trial is allowed. No positive
   uniform bound for sigma_N is supplied (§8).
7. **REVISE: description as a fully specified implementation and as a
   specialization of the existing conjecture.** It is a finite algorithmic
   construction after routine deterministic conventions; it is not implemented
   or formally refined. The character issue is the same kind of issue as LV's,
   but neither their conjecture nor sampler theorem transfers to this retained
   prefix. Section 9 states the precise prior-art relationship.
8. **REJECT: any promotion to a new complete factoring improvement, preserved
   leading constant, or useful-mass theorem. ACCEPT the proposed narrow closure.**
   This rejection concerns what has been demonstrated, not what these rotations
   could ever achieve. Missing proof is not a lower bound.

## 3. Input law and algebraic setup

Write n=bitlength(N), k=ceil(log_2 n), and use exactly the integer definitions of
d,e,E=B=2^e,Q=2^(2k),m in the submission. Then n^2<=Q<4n^2 and the t menu costs
exactly 2k unbiased bits. Computing these integers by comparisons, binary search
and exact powers uses polynomially many operations on polynomial-bit integers.
There is no scan of all Q candidates inside a trial.

For large n, d=(n/k)^(1/3)+O(1), since rounding to an odd integer loses less than
two. Consequently log m grows as (log N)/d, whereas log d=O(log n), and m/d tends
to infinity. The inputs satisfying m<2d form a finite set. Trial division through
floor(sqrt(N)) is a genuine, fully paid terminating branch there; on the promised
domain it returns a proper divisor. Finite exceptional costs can be absorbed in
an asymptotic upper bound by enlarging a fixed constant. This argument would
not authorize such trial division as a fallback on every failed large input.

On m>=2d,

    m^d <= N < (m+1)^d <= m^d exp(d/m) <= m^d exp(1/2) < 2m^d.

Thus the quotient floor(N/m^d) is exactly 1, and ordinary repeated base-m
division gives the stated digits 0<=c_j<m. The leading term is monic of degree d.
For rotation index j=t or t+1, j<=Q; the changed coefficients are c_0-jm and
c_1+j. The advertised H=(Q+1)m+Q bounds them, the remaining digits, and 1.
All polynomial input coefficient widths are polynomial in n.

Exact rational polynomial factorization is an appropriate terminating primitive
here. The monic integer inputs are primitive; their irreducible monic factors
lie in Z[X]. LLL (1982), Algorithm 3.5/Theorem 3.6, includes repeated factors
and gives polynomial bit work in degree and logarithmic coefficient norm. With
d and log H polynomial in n, the entire setup factorization is poly(n).
Factor heights are polynomial-bit, so all h(m) evaluations and gcd checks are
also poly(n). Reducibility alone is not a split certificate: every returned gcd
must satisfy 1<gcd<N. The no-split reducible case is correctly a failure.
[Primary paper scan, §3](https://www.math.ucdavis.edu/~deloera/MISC/LA-BIBLIO/trunk/Lovasz/LovaszLenstraLenstrafactor.pdf).

For accepted irreducible f_i, characteristic zero gives Delta_i!=0 and
f_i'(alpha_i)!=0. Resultants/subresultants compute Delta_i with polynomial
bit work, with log|Delta_i|=O(d log(d+1)+d log(H+1)). Direct Horner evaluation
of D_i=f_i'(m) has polynomial width as well. The tests distinguish a unit,
a proper divisor, and gcd=N. Nothing calls for factoring Delta_i, constructing
a maximal order, or solving a class/unit-group problem.

For the coupling, the monicity and f_2-f_1=X-m imply

    Res(f_1,f_2) = product_{f_1(alpha)=0} (alpha-m)
                 = (-1)^d f_1(m) = -N,
    f_2'(m)-f_1'(m) = 1.

The sign is correct because d is odd. In K_2,
f_1(alpha_2)=m-alpha_2!=0: an irreducible degree-d>=3 polynomial cannot have
alpha_2=m in Q. Therefore mapping the named generator alpha_1 to alpha_2 does
not respect f_1=0. This says nothing about other possible field isomorphisms.
The resultant gives N itself up to sign. The derivative identity alone is not
a factorization; the actual derivative gcd tests can of course split N and are
already charged as successful branches.

## 4. Stream, local labels, and linear algebra

For every enumerated positive primitive pair, r=a+bm>0 and
u_i=a+b alpha_i!=0. Otherwise alpha_i would be rational. The norm calculation is

    G_i = product_sigma(a+b sigma(alpha_i)) = (-b)^d f_i(-a/b).

Subtracting the two expressions gives

    G_2-G_1 = (-b)^d(-a/b-m) = b^(d-1)(a+bm).

The bounds r<=(m+1)E and |G_i|<=(d+1)H E^d follow term by term from the
homogenized polynomial. Signs of norms can be retained without extra matrix
constraints, because actual field squarehood is subsequently decided exactly.
It would be incorrect to use even valuations of |G_i| as the squarehood test.

On reaching the base/stream branch, all base primes are units modulo N: a prime
base entry cannot equal the composite N, and a nonunit entry gives a proper gcd.
Rows with gcd(r,N)=N are discarded; proper gcds are successes; only units enter
retained data. Full trial division, including full valuations, is finite and
exact. The finite box is traversed even after either cap is filled, except that
an actual early split terminates the trial. Counts and cost never presume that
a cap is attained.

Here is why (i,ell,-a/b mod ell) is the correct label. If ell|b, primitivity
implies ell does not divide a, whereas G_i is congruent to a^d modulo ell. Thus
ell cannot divide both b and G_i. Every prime ideal over ell dividing u_i forces
alpha_i=-a/b in its residue field. Because ell does not divide Delta_i, the
index of Z[alpha_i] in the maximal order is prime to ell and f_i mod ell is
squarefree. There is precisely one such degree-one prime, with ramification
index and residue degree 1. The norm valuation is therefore its ideal valuation.
There are at most d possible roots per ell per field, hence at most d s labels
in each field. Labels in different fields remain distinct even when their
printed prime and residue coordinates agree.

This proves the restricted good-prime assertion; it does not supply a general
bad-prime valuation routine. The rejection gcd(|G_i|,|Delta_i|)!=1 avoids that
routine and can lose an unquantified amount of supply. All remaining ideals
in a selected product have their valuations represented; the integral elements
have no negative ideal valuations to hide. This matches the local-order
qualification in Stevenhagen §§5–7 and the accepted H028 reconstruction.
[Primary chapter](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/04psh.pdf).

The block matrix really imposes P_1 v_1=P_2 v_2 and A_i v_i=0. Its kernel
maps onto W_1 intersect W_2: for any common image choose one preimage in each
L_i=ker A_i. The fiber kernel is exactly the product of the two stated kernels.
This is a finite linear-algebra identity, not a claim about dimensions or roots.
The RREF/free-coordinate map is a bijection from F_2^(dim V_t) onto V_t.
Independent fair free bits therefore sample exactly uniformly, including zero.
No random relation law or random parity law is being assumed.

Every coordinate refers to an original retained row occurrence. Equal values
or parity columns may create dependencies with no useful character value;
retaining these occurrences does not alter the correctness proof. Intersections
below refer to coordinate occurrences, not to deduplicated algebraic values.

## 5. Reduction, normalization, and the character: independent proof

### 5.1 The ring on which reduction is defined

For one accepted field set A=Z[alpha], delta=f'(alpha), D=f'(m). The polynomial
relation f(m)=N gives a ring map phi_0:A->Z/NZ. Since gcd(D,N)=1, it extends
uniquely to

    phi: A[delta^(-1)] -> Z/NZ,
    phi(h/delta^j)=h(m) D^(-j).

There is no map asserted on all of K. In particular, nonzero in K does not
mean that a denominator is invertible modulo N.

If w^2=U with U in A, then w is integral over A and hence integral over Z.
The derivative multiplier delta O_K subset A implies h=delta w lies in A.
One proof uses the trace-dual identity A^vee=delta^(-1)A: an algebraic integer
has integral traces against A, so lies in A^vee. Thus w belongs to the displayed
localization, and its reduction is exactly the submitted h(m)/D. Applying phi
to w^2=U yields x^2=r modulo N. Since r is a unit, x is automatically a unit.
The explicit congruence and gcd checks should consequently pass for any genuine
root on this branch; they are verification, not an extra probabilistic filter.

Lenstra's common scalar denominator for root output, discussed below, need NOT
be invertible modulo N. First multiply by delta in the exact field and cancel
the rational denominators to obtain integral h coefficients; only then evaluate
h(m)/D. Do not invert the discriminant or arbitrary output denominators mod N.
This is a proof completion for §§4–5 of the submission, not a changed algorithm.

### 5.2 Positive rational normalization and ordinary reconstruction

Write r_i=product_j b_j^(a_ij)>0. All b_j are units. Let v_j be the common
rational parity, c_i=product_j b_j^floor(a_ij/2), and R_v=product_j b_j^v_j.
In integers r_i=c_i^2 R_v, and after reduction z_i=x_i/c_i satisfies z_i^2=R_v.
Thus rho=z_1/z_2 is a unit root of 1.

For N=pq with distinct p,q=3 mod 4, CRT identifies the four roots of 1 with
(+,+),(-,-),(+,-),(-,+). The Jacobi symbol J is +1 on the first two and -1
on the mixed roots. Accordingly J(z_1)!=J(z_2) is equivalent to J(rho)=-1,
which is equivalent to 1<gcd(rho-1,N)<N. The test of only rho-1 suffices on
this promised domain. Outside it, this Jacobi equivalence is not established.

The positive integer root of r_1 r_2 is

    Y=product_j b_j^((a_1j+a_2j)/2)=c_1 c_2 R_v.

Then

    x_1 x_2/Y = z_1 z_2/R_v = z_1/z_2  (mod N),

because z_2^2=R_v and all denominators are units. This proves literal equality
of the two reconstructed ratios, not merely equality of their Jacobi symbols.
Negative norm metadata has no bearing on positivity of r_i. Replacing negative
r_i by |r_i| in a different stream would invalidate this proof without signed
matching data and a separate argument.

### 5.3 Actual-square subspace and overlap cancellation

The map from row-coordinate vectors to K_i^*/K_i^{*2} taking a subset to the
class of its product is a homomorphism. Multiplying a repeated coordinate twice
contributes u_i^2. Thus S_t is the kernel of the two square-class maps restricted
to V_t, and is a subspace containing zero. The root routines decide membership
only for the sampled vector; no basis, dimension or oracle for S_t is provided.

Take v,w in S_t, let s=v+w, and let C_i be the product of field-i row factors
whose coordinates occur in both v and w. Write r_Ci for the product of those
rows' positive rational r-values. In K_i,

    U_i(v) U_i(w)=C_i^2 U_i(s).

Choose any actual roots q_i(v),q_i(w),q_i(s). A field of characteristic zero has
only the two roots +/-q of a nonzero square. Hence for some epsilon_i in {+1,-1},

    q_i(s) C_i = epsilon_i q_i(v) q_i(w).

This is an equality in Z[alpha_i][delta_i^(-1)]. It involves no inverse of C_i
there. Equivalently, writing h_i(v)=delta_i q_i(v), one has the equality entirely
in the power-basis order Z[alpha_i]

    delta_i C_i h_i(s) = epsilon_i h_i(v) h_i(w).

Reducing this equality is legitimate. Since r_Ci is a product of retained
r-values, it is a unit mod N, and division AFTER reduction gives

    x_i(s) = epsilon_i x_i(v) x_i(w) / r_Ci  (mod N).

This supplies the missing justification for reduction of the field-fraction
expression in the submitted abbreviated proof.

The positive global roots satisfy an exact integer identity

    Y(s) r_C1 r_C2 = Y(v) Y(w).

It follows that rho(s)=epsilon_1 epsilon_2 rho(v)rho(w) modulo N. Because
J(-1)=1 for these semiprimes, chi_t(s)=chi_t(v)chi_t(w). Root-sign changes
multiply rho by at most -1 and cannot change chi_t. At zero, each field root
is +/-1 and Y=1, giving chi_t(0)=1. Thus this is a well-defined character on
S_t independent of all field-root sign conventions.

A common unit mask a also leaves (a z_1)/(a z_2)=rho unchanged. Neither that
mask nor independent choices between the two field-root signs can turn a
trivial productive character into a nontrivial one.

A nontrivial character has a kernel of index 2; its -1 fiber is the other
coset, not a linear subspace containing zero. Therefore exactly |S_t|/2 vectors
in S_t give a proper split. Uniform sampling of V_t has probability
|S_t|/|V_t|=2^(-c_t) of reaching an actual square, yielding the claimed formula.
If chi_t is trivial, no vector in S_t yields a proper split. A nonsquare never
gets a valid packet or a success credit under the specified exact routine.

## 6. The complete trial and a small specification repair

A literal sampler should fix otherwise routine order conventions. For example:
construct/factor both polynomials first; order their monic irreducible factors
by degree then coefficient tuple; inspect reducible-factor gcds in field order;
return the first proper gcd; if any polynomial is reducible and none gave a
proper gcd, fail. With both fields irreducible, compute/check derivatives in
field order. Then use increasing base primes, the stated lexicographic pair
order, field order for processing, deterministic exact algebra routines, and
leftmost pivots. Root sign may be fixed arbitrarily because §5 proves invariance.
This completion respects the attempted work and costs in the submission.

The prose currently leaves a choice between failing immediately at the first
unproductive reducible field and checking the other already attempted field's
reducible factors. These can define different early-success sets. Thus I request
a local specification clarification, not a change to the displayed identity:
define A_N and G_N using the chosen actual execution order. The identity below
holds under either fixed policy. No unperformed gcd gets a success credit.

With such a convention let A_N be t values on which a preprocessing or stream
gcd actually returns a proper split. Let G_N be the disjoint set reaching the
matrix stage with both valid fields and maps. All other t values fail. Then

    sigma_N = |A_N|/Q
              + (1/(2Q)) sum_{t in G_N} 2^(-c_t)
                                      1_{chi_t nontrivial}.

The partition is exhaustive on the nonexceptional branch because t is uniform,
retained data are deterministic given t, and the only remaining random choice
is the uniform kernel vector. Exact uncapped root routines terminate both on
squares and nonsquares. Their verified map checks cannot exclude a true square
under the proven hypotheses. Any capped or fallible replacement needs another
success event and a different analysis.

The following boundary cases remain explicitly inside this law:

- Early proper gcds from reducible-factor evaluations, derivatives, base primes,
  or rational r-values belong to A_N and stop the actual execution.
- Reducibles without a split and noninvertible maps with gcd=N fail; failed
  pairs never receive the conditional matrix probability with weight one.
- Bad-prime norm rejection, primitive-pair rejection, rational nonsmoothness,
  norm nonsmoothness and late cap discards change the retained data. They
  cannot be replaced by hypothetical rows or unpriced attempts.
- Underfilled or empty retained lists still define the literal matrix. A kernel
  is never the empty set: it contains zero. With dimension zero it is {0},
  S_t={0}, chi_t is trivial, and success probability is zero.
- Empty field products equal 1. One field alone can give a productive dependency;
  that success is counted, but establishes no advantage from coupling.
- Duplicate occurrences stay in V_t and in its uniform denominator. No distinct
  packet, rank, or nontrivial-character premise is inferred from their count.
- Nonsquare on either side is failure, including an early stop after the first
  unsuccessful call. Successful extraction followed by rho=+/-1 is also failure.
- On the finite trial-division branch the success probability is 1 and its
  actual work is charged separately. The 1/Q formula is for the other branch.

## 7. Full bit-work audit

### 7.1 Scalar widths, input mass, and explicit access

Let w_0 bound the binary widths of an individual r or G_i. The already proved
bounds give

    w_0=O(log(d+1)+log(H+1)+d log(E+1))=poly(n).

Each row has at most poly(n) prime-support entries, since every nonzero integer
of w_0 bits has at most w_0 prime factors with multiplicity. Full valuations
have polynomial-bit representations. The cap bounds R=R_1+R_2 by O(dB),
D_mat by O(dB), and the sparse input nonzero count by R poly(n), independently
of any yield or rank law. Identifiers have O(log R+log E+log B+log Q)=poly(n)
bits. The free-bit budget is 2k+dim V_t<=2k+R, fully charged; it is not being
claimed polynomial in n.

The following access realization supports the submitted majorant on a fixed
multitape bit machine, without a free large indexed-memory operation.

- **Base:** emit multiples j^2,j(j+1),... through B for each 2<=j<=sqrt(B).
  There are O(B log B) records. Every composite appears because it has a divisor
  at most its square root. External merge sorting, duplicate removal and a
  sequential complement scan produce exactly the primes through B using
  B poly(n) bit work and storage, since log B=poly(n). Each base gcd is paid.
- **Full stream:** retain the sorted prime list on a tape. Each attempted pair
  costs primitive/unit tests plus at most one rational and two norm scans;
  resetting the prime head costs O(B poly(n)) as well. Full division to extract
  valuations uses only polynomial work per scalar/prime pair. Norm evaluations,
  bad-prime tests, rejected statuses and late-cap admissible rows are all paid.
  This yields O(E^2 B poly(n)) even when R=0. Early successful termination only
  lowers work. Storing all discarded rows is unnecessary; writing/reading their
  processed bits is still included.
- **Labels and dense matrix:** sort retained support entries by label, assign
  labels, sort entries back by matrix position, and fill zero runs sequentially.
  This costs O((R+D_mat+1)^2 poly(n)). Include an additive 1 for empty data rather
  than interpreting a zero dimension as zero control cost.
- **Elimination:** scan to choose a pivot, copy its row to a work tape, and scan
  all rows to eliminate that pivot. Resets and row exchanges cost O(D_mat R)
  bits per pivot up to polynomial identifier factors. There are at most
  min(D_mat,R) pivots. Storing equations, free/pivot coordinates and the original
  relation order suffices for sampling and lifting. Back substitution and a
  merge with the selected-row flags fit O((D_mat R+R+1) poly(n)). Matrix storage
  is O((D_mat R+1) poly(n)).

### 7.2 Exact field products really have growing coefficient widths

For a reduced product A(X)=sum_{j<d} A_j X^j with max|A_j|=M, multiply by a+bX
and reduce the single X^d term using f_i. The new coefficient in position j is

    a A_j + b A_(j-1) - b A_(d-1) f_(i,j),

with A_(-1)=0. Its magnitude is at most E(H+2)M. Starting from 1 proves the
submitted bound, with harmless rounding/sign-bit additions:

    h_i := ceil(log_2(2+max|coeff(U_i)|))
           = O(1+ell_i log(E(H+2))) = O((R_i+1) poly(n)).

This is an upper bound, not an assertion that every subset attains that height.
The element degree remains below d, while coefficient length can be on the
R_i scale. Sequential multiplication of all selected factors fits
O((R_i+1)^3 poly(n)) with schoolbook arithmetic (indeed it can be bounded more
sharply). Access to its polynomially many coefficients adds polynomial factors
or a scan of O(h_i poly(n)) bits, not another R-sized matrix factor.

### 7.3 Lenstra 1983: exact substitutions and what is included

I inspected the primary CWI PDF's actual page images for printed pp. 251–254,
including Algorithms 4.1/4.4, Proposition 4.3 and Theorem 4.5, as well as the
preceding definitions and lattice argument in the extracted text.
[Primary PDF](https://ir.cwi.nl/pub/2541/2541D.pdf).
The following are my substitutions into that theorem, not a new field-factoring
algorithm. To avoid the paper's collisions with H031 notation, use:

    paper F          = H031 f_i (defining monic irreducible polynomial),
    paper delta F    = d (field degree),
    paper f          = T^2-U_i (polynomial to factor),
    paper n          = nu=2 (NOT bitlength(N)),
    paper d          = b_den=1 (input coefficient denominator),
    paper D          = D_L=b_den*|disc(F)| (NOT f_i'(m)),
    paper f_max      = max(1,max|coeff(U_i)|),
    paper |F|        = Euclidean coefficient norm <= sqrt(d+1) H.

U_i!=0 makes T^2-U_i squarefree in characteristic zero. A linear factor exists
exactly when U_i is a field square; otherwise the degree-two factor is
irreducible. There are only two possible roots, and at most two field calls
in the full trial. Empty products cause no difficulty.

The displayed Theorem 4.5 bounds, in these renamed variables, are

    arithmetic operations:
      O(nu^6 d^6 + nu^5 d^6 log(d|F|)
                   + nu^5 d^5 log(b_den f_max)),
    operand bit length:
      O(nu^3 d^3 + nu^2 d^3 log(d|F|)
                   + nu^2 d^2 log(b_den f_max)).

Use 1+log of the displayed magnitudes at small values. With nu=2, b_den=1,
and log(d|F|)=poly(n), both bounds are O((h_i+1)poly(n)). Schoolbook integer
arithmetic therefore yields O((h_i+1)^3 poly(n)) bit work, hence
O((R_i+1)^3 poly(n)). A generic statement that field factorization is polynomial
would not suffice to determine this exponent; the actual linear dependence
in both displayed logarithmic-height bounds is essential.

Here are the setup and output obligations behind that substitution.

- **Denominators:** Algorithm 4.4 chooses D_L=|disc(F)| rather than finding the
  largest square divisor of the discriminant. It therefore does not need
  integer factorization of the discriminant. Its logarithm is poly(n), and all
  monic factors lie in D_L^(-1)Z[alpha][T].
- **Prime choice:** in this application Res(T^2-U_i,2T)=-4U_i!=0. The prime
  selected in Algorithm 4.4 must avoid D_L disc(F) and must not annihilate
  all coefficients of this resultant. Page 254 bounds its numerical size by
  O(log b_den+nu d log(d|F|)+nu log nu+nu log(b_den f_max)), thus
  O((h_i+1)poly(n)). It is not necessarily polynomial in the bitlength of N.
  No integer factoring oracle is required: enumerate/test primes until this
  condition holds. An external sieve as above and sequential coefficient
  remainders fit the cubic majorant. Even elementary trial primality checks
  throughout this bounded interval fit that majorant. The relevant prime size
  must not be mistaken for its logarithm. Here log(h_i+2)=poly(n), because
  h_i=O((R_i+1)poly(n)) and R_i=O(dB); auxiliary index widths therefore also
  fit the stated polynomial factors.
- **Finite fields:** factor F modulo the selected prime and choose a factor H
  on which the resultant remains nonzero. The prime does not divide disc(F),
  so the required factors are simple. The auxiliary field has p_aux^(deg H)
  elements and deg H<=d. Page 253 explicitly uses the modified Berlekamp
  algorithm whose dependence is polynomial in p_aux and deg H, not enumeration
  of all field elements. Theorem 4.5 includes this preprocessing. Its output
  arrays have polynomially many field coordinates, so sequential coefficient
  access does not introduce a p_aux^d loop.
- **Lifting and LLL:** Algorithm 4.1 chooses a finite precision using its (4.2),
  Hensel-lifts H and the chosen finite-field factor, and applies Proposition 2.7
  to the lattices of §3.5. At nu=2 the nontrivial lattice dimension is at most
  d+1. Taking logs in (4.2) gives precision-bit length O((h_i+1)poly(n)); it
  is not a search over unbounded candidate roots. Proposition 4.3 includes
  both lifts and the discriminant work. No suitable inert prime is assumed.
- **Output widths:** page 254 bounds logarithmic factor height by
  O(d log(d|F|)+nu+log f_max). Together with log D_L=poly(n), a returned root
  has polynomially many rational power-basis coordinates of
  O((h_i+1)poly(n)) numerator/denominator width. Coefficient height alone would
  not have bounded the denominators without D_L.
- **Access:** the high-width lattice and polynomial arrays have poly(n) entries.
  A full sequential scan for each arithmetic access costs at most
  O((h_i+1)poly(n)); this is absorbed by the allowed schoolbook work per
  operation. Large auxiliary prime lists can be generated and scanned on
  separate tapes. Thus the arithmetic theorem does not require an uncharged
  random access to an exponentially long root table.

The degree-two input has no repeated-factor complication; a terminating exact
irreducibility answer gives the nonsquare failure. There is no root-completion
probability silently set to one by a heuristic, numerical precision cap, or
chosen-prime oracle.

### 7.4 Final verification, exponents, and complete majorant

Using the returned coordinates, multiply by f_i'(alpha_i), check integrality,
and verify both w_i^2=U_i and h_i^2=f_i'(alpha_i)^2 U_i by exact polynomial
arithmetic. All degrees are poly(n), all widths O((R_i+1)poly(n)); these
operations fit the same cubic majorant. Reduction uses n-bit modular arithmetic
and the already justified inverse of D_i, never an unchecked scalar denominator.

The full positive rational factorization is stored by summing row exponents.
An exponent sum is at most R_i w_0, so its bit length is O(log(R_i+1)+log(w_0+1)).
Sorting/merging sparse lists or scanning all s coordinates per selected row is
paid and fits the majorant. Forming c_i, Y modulo N, and packet verifications
uses polynomial-bit exponents and n-bit residues. Modular inverses, Jacobi
symbols, proper gcd tests, divisibility tests and final output are included.
On the promised domain an optional deterministic primality check of the two
returned factors is polynomial work; no arbitrary-composite recursive theorem
is obtained from the promise.

Summing the pathwise costs gives, with constants adjusted for empty cases,

    T_trial <= poly(n) [1+E^2 B+(dB+1)^3]
             = O(B^3 poly(n)).

The two root calls contribute a sum of two cubes bounded by O((R+2)^3 poly(n));
there is no uncharged root extraction for a packet basis. Cold setup is repeated
and charged. A safe total space bound is O(B^3 poly(n)) bits; matrix memory
alone may be O(B^2 poly(n)).

For logarithmic conversion set L=ln N. Since

    n = L/ln 2 + O(1),
    k = ln n/ln 2 + O(1),
    e = (n k^2)^(1/3)+O(1),

we have

    ln B = (ln 2)e = (1+o(1)) L^(1/3)(ln L)^(2/3),
    d = (1+o(1))(L/ln L)^(1/3).

Fixed powers of n and d are exp(o(L^(1/3)(ln L)^(2/3))). Therefore the
majorant is L_N[1/3,3+o(1)], not a different constant caused by base-two logs.
This is an upper bound on the time of every trial, not an equality for every
execution and not a lower bound on alternative implementations.

## 8. Restarts and the absent success theorem

For iid cold trials let T_j be each trial's actual cost and S_j its success
indicator. With tau the first success and sigma_N>0, nonnegative summation gives

    E[sum_{j<=tau} T_j]
      = sum_{j>=1} E[T_j 1_{S_1=...=S_(j-1)=0}]
      = E[T_trial] sum_{j>=1}(1-sigma_N)^(j-1)
      = E[T_trial]/sigma_N.

T_j need not be independent of S_j; independence from previous trials suffices.
The pathwise bound ensures finite E[T_trial]. If sigma_N=0 there is no successful
restart run. Adaptive field retention, altered caps, biased dependency choices,
or shared preprocessing require another strategy-valid probability/cost proof.

The unresolved quantity is the actual weighted useful mass, including A_N.
There is no proof here that it is positive on every promised input, let alone
at least n^(-C). If that stronger bound were later proved, this ledger would
support constant at most 3 for this implementation on the promised family.
It would not preserve either cited square-congruence constant 1.92299 or
1.90188. Conversely, the conservative constant 3 is not evidence that a faster
implementation of these rotations is impossible. No matched complete factoring
improvement is demonstrated.

## 9. Primary-source gate and sampled-law mismatch

**Coppersmith:** the primary paper is *Modifications to the Number Field Sieve*,
Journal of Cryptology 6 (1993), 169–180, DOI 10.1007/BF00198464. Page 174
explicitly uses base-m polynomials plus i(X-m). Page 175/Figure 1 has shared
rational columns and separate field ideal/character blocks. Page 176 takes
individual field roots, multiplies their modular images, and uses the rational
square over the entire selected triple set. Page 177 charges the roots over
participating fields. Page 170 marks the smoothness substitution as heuristic.
The H031 normalization is an exact rewriting of that global reconstruction;
neither its parity match nor its common root supplies novelty.
[Primary PDF](https://link.springer.com/content/pdf/10.1007/BF00198464.pdf).

**Lee–Venkatesan:** in arXiv:1805.08873v1, Theorem 2.1 is a square-congruence
result. Theorem 2.3's fruitful Blum-semiprime conclusion assumes Conjecture 7.82.
Section 7 already constructs the sign-independent productive Jacobi character;
the conjecture asserts its independence from imposed characters/parities.
Remark 7.83's ambient character count is not a law for the generated character.
Remark 7.85 discusses multiple fields. Definition 4.28 uses independently uniform
coefficient perturbations across a full polynomial family. Its argument therefore
cannot simply be assigned to this one-parameter adjacent pair.
[Primary text](https://arxiv.org/html/1805.08873v1).

The following differences are independently material, rather than cosmetic.
H031 fixes m, varies only one small rotation coefficient with t and t+1 coupled,
uses only positive (a,b), rejects every bad-prime norm row, retains only the
first prescribed number in each field, and samples the ideal-parity kernel
without additional character columns. Its actual-square subset must absorb
the missing squarehood constraints. LV's proof of Theorem 2.3 invokes its
smooth generator set and its own collection/character procedure. Even
nontriviality on a larger smooth semigroup would not imply nontriviality on
H031's retained prefix. No inclusion plus distribution argument, quantitative
transfer, or truncation-preservation lemma is supplied.

Therefore replace any reading of “specialized conjecture” as formal equivalence
or automatic applicability with: **the same productive-character obstruction
arises for a different, separately unanalysed sampling law.** H031 additionally
owes a bound for landing in actual squares. The inspected primary passages do
not support a claim that Coppersmith omitted global rational parity; his displayed
reconstruction states it explicitly. The terse multi-field wording in LV is
not evidence of a new missing parity mechanism.

The v1 text has local sign/wording inconsistencies in its short proof (including
an inequality printed in the wrong direction for the desired character value).
The mathematical criterion used in this review is re-derived in §5 and is
chi=-1, with a -1 coset of size half the square space. I do not treat those
local typographical issues as a new gap or as a proof of H031's required law.

The source check was targeted. It did not re-prove all analytic results in LV,
the entire field-factorization literature, or an exhaustive novelty claim.

## 10. Required repairs and complete outstanding objections

The following local repairs make the scope reviewable without changing the
submitted equations or claimed leading trial constant. The original submitted
bytes and all prior accepted files must remain preserved.

1. **Reduction proof:** insert the localization phi:A[delta^(-1)]->Z/NZ and
   the cleared equality delta C h(v+w)=+/-h(v)h(w) from §5. Explicitly prohibit
   modular inversion of arbitrary field-output denominators, including disc(F).
2. **Literal sampler:** fix setup/gcd failure order and deterministic routine
   conventions as in §6, then define A_N from that execution. Do not claim
   a unique early-success set before resolving the order ambiguity.
3. **Root/access ledger:** supply the variable dictionary, both displayed
   Lenstra bounds, numerical auxiliary-prime bound, output denominator bound,
   and sequential access completion from §7. Keep O((R_i+1)poly(n)) coefficient
   widths, two uncapped calls and exact checks; use an upper-bound sign for work.
4. **Prior-art wording:** say that the productive-character issue is analogous
   under a different sampled law, not that the LV conjecture or proof transfers
   to the capped row space. Preserve the global rational parity comparison.
5. **Status and closure:** retain UNACCEPTED until coordinator disposition;
   retain verified improvement NONE. Describe a finite on-paper construction
   with a justified upper ledger, not a tested implementation or formal proof
   of complete factoring complexity.

The full unresolved mathematical list for a positive improvement is:

- A uniform lower bound on actual complete-trial success, or another sufficient
  strategy-valid success/work theorem, is absent. The early-gcd term is included
  but has no such bound either.
- No favorable mass of valid, serviceable adjacent pairs is proved after
  irreducibility/map validation. No independence or nonisomorphism result can
  replace this missing arithmetic statement.
- No adequate retained supply/rank statement is proved for this exact stream,
  including positive-pair restriction, all smoothness tests, bad-prime rejection,
  deterministic prefix caps, duplicate occurrences and empty/underfilled lists.
  Expected raw relation counts would not by themselves resolve this.
- No uniform small codimension c_t=O(log n), or adequate weighted replacement
  for it, is proved on enough actual retained spaces. Ideal parity alone does
  not resolve unit/class obstructions or provide roots.
- No nontriviality of chi_t on enough actual S_t is proved, nor independence
  adequate for the weighted law. Global root-sign choices and common masks
  cannot create this mass. General character counting is not a substitute.
- No theorem transfers LV's distribution, character constraints, collection
  guarantees or fruitful-output claim to this sampler and its truncated spaces.
- No paid replacement lowering this construction's complete cost to a matched
  improved constant is supplied. Improved matrix/root primitives would need a
  new ledger and would still leave the useful-mass obligation.
- No all-composite correctness/success theorem or all-input complete factoring
  reduction is supplied. A split completes the promised semiprime only.
- No implementation or machine refinement has been checked. That is a distinct
  evidence limit; building one now would not prove the missing useful-mass law.

The local proof/accounting repairs are provided here for adoption; the positive
probability and improved-complexity obligations remain unresolved. No additional
experiment or replacement question is selected. The selected realization fails
to meet the constructive brief's improvement threshold, which is sufficient
for this narrow disposition without asserting that its actual sigma_N is zero.

**Best supported outcome:** an independently checked finite construction after
routine specification completion, its failure-inclusive character identity, and
its conservative L_N[1/3,3+o(1)] per-trial majorant. **Verified COMPLETE factoring
complexity improvement remains NONE.**
