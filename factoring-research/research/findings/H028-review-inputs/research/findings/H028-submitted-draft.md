# H028 — Polynomial sharing, paid norm streams, and compatible square maps

2026-10-08. **Constructive analytic report; new deductions below await
independent review. Verified full factoring complexity improvement: NONE.**

**Disposition proposed to the coordinator: close these two concrete routes as
new complexity mechanisms. Selected new survivor: NONE.** The first route
constructs and sieves a field-index arithmetic progression, but it neither
removes the charged norm population nor changes the bottlenecks of the known
multiple-field model. The second constructs genuinely common integer columns
with an explicit square map, but reduces to classical quadratic congruences
with larger norms. Identical local root labels alone do not supply that map.
Neither conclusion is a lower bound on arbitrary multiple-field methods.

No research experiment, benchmark, sweep, solver implementation, package,
Lean change, delegation,
commit, publication or scheduler was used. Writes are this file and adjacent
`H028-sharing-*` source/provenance artifacts only. H027 was neither read nor
duplicated. The coordinator's acceptance of H026 overrides the historical live
review language in the read checkpoint; no H026 task was polled or launched.

## 1. Evidence and inherited scope

Read the project AGENTS, README, SPECIFICATION, RESEARCH_LOOP, RESEARCH_TEAM
and STATE; the complete H028 brief and W001 baseline/relation ledgers; the H016
processing report/disposition; the H022 corrected report, complete independent
review and disposition; and the H023 report, intake comparison and disposition.

Primary-source access was to the underlying documents, not just abstracts:

- **Coppersmith (1993), §§3–4, printed pp. 174–180**, and §2 for the original
  matrix and square roots. The PDF and extracted text are archived. The images
  of printed pp. 175 and 177–178 were inspected for the matrix layout and to
  resolve damaged OCR of constants and inequalities.
  [Original paper](https://link.springer.com/content/pdf/10.1007/BF00198464.pdf),
  [local PDF](H028-sharing-source-coppersmith1993.pdf).
- **Lee–Venkatesan, v1, Remarks 2.7 and 4.31**, with the statements separating
  square congruences from useful factoring. The actual HTML, including its
  mathematical markup, is archived. [Primary text](https://arxiv.org/html/1805.08873v1),
  [local HTML](H028-sharing-source-lee-venkatesan2018.html).
- **Stevenhagen, §§6–10**, for the distinction between ideal parity, element
  squares, order denominators, characters and square-root extraction.
  [Primary chapter](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/04psh.pdf),
  [local PDF](H028-sharing-source-stevenhagen2008.pdf).
- **Kleinjung, §6.7**, especially the sieve over the index in `f1+i*f2` on
  printed pp. 11–13. Polynomial rotation and its small-prime root sieve are
  established methods. [Primary chapter](https://www.joppebos.com/montgomery/book_ch6.pdf),
  [local PDF](H028-sharing-source-kleinjung-ch6.pdf).
- **Pomerance, Smooth numbers and the quadratic sieve**, the quadratic
  congruences and sieving discussion, and printed p. 80 on multiple polynomials.
  [Primary chapter](https://math.dartmouth.edu/~carlp/PDF/qs08.pdf),
  [local PDF](H028-sharing-source-pomerance2008.pdf).

This is a targeted prior-art check, not an exhaustive novelty search. The
derivations and proposed constructions below are explicitly separated from
what the sources assert. Source hashes and the consulted local-input hashes
are in [the provenance manifest](H028-sharing-provenance.json).

Three inherited limits matter throughout:

1. [H016](H016-disposition.md) charges aggregate integer input and output bits.
   Its `(B+S) poly(n)` corollary needs polynomial scalar and identifier widths.
   Its ideal handling is restricted to good primes; discarding bad-prime rows
   has unquantified supply loss. It makes neither `K*M` values nor changed-field
   preprocessing free.
2. [H022](H022-disposition.md) has fixed-field uniform geometry, actual height,
   strategy-valid expected-yield and mesh assumptions. Its infimum
   `c^3=32(1+gamma)/9` is **not** a many-field obstruction. None of the exclusions
   below is inferred from H022.
3. [H023](H023-disposition.md) supplies real geometry exceptions. Its translated,
   skewed, degree-halved and binomial comparisons remain special-form models,
   not an all-input supply of advantageous fields. Its `16/3`, `40/9` and
   `32(s+1)/(9s)` cubes cannot be assigned to arbitrary N or to every field here.

## 2. Reconstructing the known cold multiple-field model

### 2.1 Parameters, actual construction and norms

Put

    t=log N, D=t^(1/3)(log t)^(2/3), V=t^(2/3)(log t)^(1/3),
    L[c]=exp((c+o(1))D), d=(delta+o(1))(t/log t)^(1/3),
    E=L[epsilon], B_R=L[beta], B_A=L[gamma], beta>=gamma>0.

Here `gamma` is the algebraic smoothness-bound parameter, **not** H022's
coefficient-height parameter. All limiting constants in this section are fixed.

Take a base-m polynomial `f_0` of degree d with `f_0(m)=N` and coefficients
bounded by m, with `log m=(1/delta+o(1))V`. For the asymptotic usual degree
scale, `m=floor(N^(1/d))` gives leading digit one eventually: `m/d` tends to
infinity, and `(m+1)^d<2m^d`. Finite exceptions are handled explicitly rather
than granted monicity. Choosing a nearby multiple of N or using the standard
nonmonic formulation is also possible, with its corresponding costs.

Coppersmith's §3 construction is already

    f_i(X)=f_0(X)+i(X-m), 0<=i<K.                         (2.1)

All these polynomials have the same degree and the same modular root, and
indeed `f_i(m)=N`. Writing them costs `K poly(n,log K)` bits/work in this
scale, where `n=bitlength(N)`. Their coefficient maximum obeys

    A_i <= (K+1)m+K,
    log max_i A_i <= log m+log(K+2)+O(1).                (2.2)

For i>=2 the changed constant coefficient has absolute value at least
`(i-1)m`, so the multiplicity really increases heights; it is not a supply of
smaller-height fields. With `K=L[kappa]`, that increase is on the D scale and
is lower order on V. Each actual discriminant has polynomial bit length
`O(d log d+d log A_i)` and is separately computable.

Polynomial generation is not an irreducibility or independence oracle.
Validate candidates; count the Q attempted polynomials, discarded reducibles,
failed character/denominator choices and restarts. Rational polynomial
factorization/irreducibility testing has a polynomial-bit implementation;
any factor of N actually obtained during a failure is checked as a separate
successful branch. It is not guaranteed that every reducible f splits N.
Using `Q=L[kappa+o(1)]` to obtain K serviceable fields is part of the known
heuristic baseline, not a new all-input assertion about (2.1).

Normalize primitive pairs, for example `b>0, |a|<=E, b<=E`, to avoid the
obvious common scaling/sign duplications. Set

    r(a,b)=a-mb,
    F_i(a,b)=b^d f_i(a/b)
            =F_0(a,b)+i b^(d-1)(a-mb).                 (2.3)

The rational side is common. Its V-scale logarithm is `1/delta`; a uniform
algebraic upper envelope is `(1/delta+epsilon*delta)V+o(V)`. In particular

    |F_i(a,b)| <= (d+1) max_i A_i E^d.                 (2.4)

Substituting these size envelopes as smoothness probabilities is a heuristic
for the actual polynomial values. It is not an unconditional yield theorem,
nor does a norm upper bound prove a corresponding upper probability bound.

### 2.2 Selection, multiplicity, separate columns and processing charges

First sieve the `E^2` primitive pairs for `B_R`-smooth r. In the size model put

    tau_R=1/(3 delta beta),
    tau_A=(epsilon delta+1/delta)/(3 gamma),
    M=L[mu], mu=2 epsilon-tau_R.                        (2.5)

M is the Stage-1 population, not the initial box. Every one of the K fields
then receives those M pairs. There are **K*M algebraic norm objects**, including
every failed second test. The expected Stage-2 count per field is modeled by
`L[mu-tau_A]`. Dependence between fields is not erased by writing these symbols.
The original paper tests these irregularly spaced survivors individually
using ECM, with per-integer overhead on the `L_N[1/6]` scale (printed p. 175),
below the leading D scale. The H016 implementation below is an alternative
paid processor; it is not silently attributed to the 1993 algorithm.

Let `B_R'` be the rational prime/sign column count and `B_A'` the per-field
ideal/character count. Coppersmith balances

    K approximately B_R'/B_A', kappa=beta-gamma,
    D_mat approximately B_R'+K B_A'=L[beta].            (2.6)

A good prime ideal column has label **(field i, prime p, root rho)**. The
integers p on the rational side are common columns; the same printed `(p,rho)`
in different fields is not a common ideal. There are at most `d*pi(B_A)` good
degree-one labels per field, plus separately handled exceptions and character
columns. Thus the unfiltered algebraic base has scale `K*B_A`, not `B_A`.
For general K the ambient dimension parameter is

    q=max(beta,kappa+gamma), D_mat=L[q].                 (2.7)

Before optimizing, the following are the available implementation charges
under the stated degree/width hypotheses:

- Generating Q polynomials and computing discriminants costs `Q poly(n)`;
  a full field/character/bad-prime preparation procedure is not supplied by
  merely writing their coefficients.
- Rational-prime construction costs `B_R poly(n)`. Preparing root tables
  separately for K fields costs expected `K B_A poly(n)` using finite-field
  factorization. The elementary deterministic scan over all residues costs
  `K B_A^2 poly(n)`. Table storage is `K B_A poly(n)` bits, with paid sorting
  or indexed access. No scan of the entire table per relation is assumed.
- One can instead label a **retained good-prime linear element** directly:
  if p divides its norm, primitivity and monicity imply p does not divide b;
  `rho=a/b mod p` is the unique relevant root. When p does not divide
  `disc(f_i)`, its ideal valuation is the recovered integer p-valuation.
  Label `i` remains indispensable. This costs polynomial work per support
  entry and does not presume free global root tables.
- H016 integer processing gives
  `(B_R+B_A+M+K M) poly(n)` for the explicit streams here. All norms,
  full valuations, identifiers and retained metadata are paid. Prime/field
  table construction, if used, is additional. H016 does not remove `K M`.
- Rejecting `gcd(F_i,disc(f_i))!=1` is cheap and exact but can lose supply.
  Keeping those rows requires a paid local-order/valuation treatment.
  There is no free discriminant factorization or maximal-order computation.

At the balanced parameters, sufficient collection in the displayed model is

    2 epsilon - 1/(3 delta beta)
       - (epsilon delta+1/delta)/(3 gamma) >= gamma.    (2.8)

Strict/slightly enlarged quotas absorb constants, characters and surplus
rows. The original layout uses about `2 B_A'` rows per field, and hence about
`2 B_R'` rows and columns in all. More rows than columns ensures a parity
dependency; it does not ensure a useful square root or a proper split.

Rows have polynomially many nonzeros because integer norm widths are
polynomial in n. With `R=L[q]` retained rows and sparse data `W=R poly(n)`,
the usual paid sparse-linear-algebra model costs `D_mat W=L[2q] poly(n)`.
Filtering must retain its lifting records; elimination fill, duplicate rows,
extra collected rows, failed Krylov runs and memory traffic are charged.
Arbitrary rank or a favorable filtered core is not assumed free.

### 2.3 What a dependency actually reconstructs

For a selected set S of triples let S_i be its field-i subset and put

    U_i = product_(i,a,b in S_i) (a-b alpha_i),
    Y^2 = product_(i,a,b in S) (a-bm).                  (2.9)

The common rational columns, including sign, construct the integer square
on the right from full prime exponents. The **separate** ideal and character
blocks must allow actual roots `z_i^2=U_i` in each field. Even ideal valuations
alone do not imply this: ideal classes and units are still present. With K
fields the character failure allowance must be small enough for their union;
an extra `O(log K)` characters per field suffices only under the relevant
character sampling/spanning hypotheses. Constructing those characters is paid.

Order denominators have an explicit standard remedy in the monic case. If
`z_i` is integral but not in `Z[alpha_i]`, then

    h_i=f_i'(alpha_i) z_i belongs to Z[alpha_i].

Verify `h_i^2=f_i'(alpha_i)^2 U_i` in the field. Set `d_i=f_i'(m)`.
If `gcd(d_i,N)=1`, evaluate

    x_i=h_i(m)/d_i mod N,
    X=product_i x_i mod N.                              (2.10)

Then `x_i^2=product_(S_i) r mod N` and `X^2=Y^2 mod N`. A gcd of d_i with
N strictly between 1 and N is already a verified split; gcd N is a failed
invertibility case, **not** automatically a proper factor. Denominators,
verification and such failures are part of the algorithm. This is the
standard order-multiplier construction, not a new shared square-root oracle.

Finally test `gcd(X-Y,N)` and `gcd(X+Y,N)`, also handling any nonunit X or Y
by paid gcd checks. For odd N with at least two distinct prime factors and
unit Y, a *uniform* square-root sign pattern would give a proper split with
probability at least 1/2. These relation procedures have not been proved
to produce that distribution. Write their actual productive-trial probability
as sigma_N, and charge complete failed attempts/restarts through
`E[T_trial]/sigma_N` for independent identically distributed restarted trials.
An `L[1/3]` comparison needs `sigma_N^(-1)=L[o(1)]` at minimum. No such new
bound is proved here. Uniform splitting bounds, primality tests and recursive
splitting would be needed to pass from one split to COMPLETE factorization;
the polynomial number of recursion nodes would then preserve the L constant.

### 2.4 Exact constant and a symbolic derivation

The reconstructed cold per-trial cost envelope, with the baseline completion
assumptions and balanced K, is

    c >= max(2 epsilon, 2 beta,
             beta-gamma+2 epsilon-tau_R, beta+gamma).  (2.11)

The third term charges **all** K*M second-stage values. The last allows
`K B_A^2` square-root work, as well as the conservative deterministic root
table option. At about `B_A` rows per field, fast root work can do better;
the weaker allowance already fits. Changed degrees, heights or unbalanced
relation populations require recharging `sum_i T_root(i,R_i)`, not importing
this expression unchanged. Character/local-order costs and successful field
selection are among the conventional completion hypotheses.

Here is an independent algebraic reconstruction of the optimization, not a
claim to improve it. Even discard the last two terms in (2.11). If the
remaining envelope is at most `2x`, then `epsilon<=x` and `beta<=x`.
Any feasible (2.8) has `delta<6 gamma`: otherwise its coefficient of epsilon
is nonpositive and the other terms are strictly adverse. Therefore increasing
epsilon to x improves (2.8); increasing beta to x also improves it. A necessary
condition is consequently

    3 gamma(2x-gamma) >= x delta+(1+gamma/x)/delta
                      >= 2 sqrt(x+gamma).              (2.12)

Put `z=gamma/x`, where `0<z<=1`. Squaring positive quantities gives

    x^3 >= 4(1+z)/[9 z^2 (2-z)^2].                    (2.13)

The logarithmic derivative of the expression on the right has the sign of
`3z^2+2z-4`; its unique zero in (0,1] is

    z_*=(sqrt(13)-1)/3.

It decreases before this zero and increases afterwards; it diverges at zero.
Substitution, with equality in the positive AM–GM step of (2.12), yields

    beta=epsilon=x=((46+13 sqrt(13))/108)^(1/3),
    gamma=x (sqrt(13)-1)/3,
    delta=x (4 sqrt(13)-10)/3,
    kappa=x-gamma,
    c_C=2x, c_C^3=(92+26 sqrt(13))/27.                 (2.14)

These are precisely the printed p. 177 values and the constant in
[Lee–Venkatesan Remark 4.31](https://arxiv.org/html/1805.08873v1#S4).
The latter uses `beta'` for our gamma, `sigma` for epsilon and `eta` for
kappa; its height parameter `kappa` is instead `delta^(-1)+o(1)`.
It states a randomized **square-congruence** result, not an unconditional
general complete-factoring theorem. Its separate useful-factoring statement
has the Blum-semiprime/character-decorrelation qualification.

Useful exact equalities at (2.14) are

    tau_R=2 kappa, tau_A=gamma, mu=2 gamma,
    log(K M)/D = beta+gamma < 2 beta=c_C.              (2.15)

Numerically the printed values give beta about .95094, gamma about .82591,
kappa about .12503, delta about 1.40175 and c_C about 1.90188. The norm-test
and conservative square-root exponents are about 1.77685; both are strictly
below the sieve and matrix exponent. This gap is central to Card A.

**Scope of (2.12)–(2.15).** This is optimization of (2.8), the balanced
common-rational/disjoint-algebraic-column architecture and the retained sieve
and matrix charges. It is not a lower bound on actual factoring, on a better
smoothness sampler, on smaller actual norms or on compressed column spaces.
In particular a field-index selector that changes the justified yield law
has changed the model and must be analyzed separately.

### 2.5 The factory has a different accounting boundary

For §4, let

    b_f=((5+2 sqrt(6))/18)^(1/3),
    beta=gamma=b_f, epsilon=b_f sqrt(6)/2,
    delta=b_f(3 sqrt(6)-6).

The permanent rational table costs `L[2 epsilon]`, approximately
`L[2.0068]`, to build; its storage and subsequent per-N cost have exponent
`2 b_f`, approximately 1.6386. Here K=1 at leading scale. If Q_f inputs use
one genuinely applicable table, the averaged cost is schematically

    L[2 epsilon]/Q_f + L[2 b_f],                       (2.16)

plus storage/access and failed-input costs. On a cold single input the
precomputation is charged, so this is not a 1.6386 cold bound. These constants
are not mixed into either card's cold comparison.

## 3. Card A — Sieve exact norm progressions in the field index

**Proposed saving.** Replace repeated general polynomial evaluation and
individual smoothness tests by a contiguous index sieve, while retaining
different algebraic fields. This is a concrete attempt to share *algebraic*
norm processing. The common rational stage alone is already Coppersmith's.

### 3.1 Input-only construction and an exact processor

Use the explicitly generated, validated family (2.1), with the actual height
bound (2.2); there is no low-height oracle. For each paid Stage-1 pair j compute

    U_j=F_0(a_j,b_j), V_j=b_j^(d-1)(a_j-mb_j),
    F_i(a_j,b_j)=U_j+i V_j.                             (3.1)

Two integer computations per pair initialize the progression. Updating an
entry by addition instead of reevaluating a degree-d polynomial is a valid
polynomial-factor saving. It still takes K updates/status objects for that
pair. Distinct i give distinct integers because V_j is nonzero. Values from
different pairs may coincide and require charged deduplication; identical
integer norms in different fields do not identify their ideal vectors.

An exact small-factor sieve along i works as follows. For each p<=B_A:

- If p does not divide V_j, solve
  `i=-U_j/V_j mod p` and visit that progression in `[0,K)`.
- If p divides V_j but not U_j, no entry is divisible by p.
- If p divides both, every entry is divisible by p. Extract full valuations
  at the actual integers, or use the corresponding prime-power progressions.

Initialize the K residual integers, divide at every hit until indivisible,
and accept only residual absolute value one. This supplies exact prime
exponents, not merely approximate logarithmic sieve scores. Zeros are excluded.
Negative values retain their signs. The degeneracies above are mandatory.

For one pair there are `O(B_A)` prime setup operations and at most
`sum_(p<=B_A,p not dividing V_j)(K/p+1)` first hits. Primes dividing V_j
contribute at most polynomially many full-array passes because V_j has
polynomial bit length. Full valuation extraction and exact arithmetic add
polynomial factors in n. Consequently the conservative whole processor costs

    (M B_A+M K) poly(n),                               (3.2)

in addition to field/character preparation, matrix work and reconstruction.
Streaming one pair at a time uses a K-sized norm array plus the base and
retained relation storage. It does not use constant storage for K outputs.

By contrast, simply expanding (3.1) and invoking the accepted H016 batch
construction costs

    (B_A+M K) poly(n),                                 (3.3)

before ideal processing. Neither has an output-sensitive certificate for
discarding an entire interval of nonsmooth values without visiting them.
Building product trees of the K terms still has aggregate K-input bit mass.
No sublinear explicit-list claim follows from the two-number description
`(U_j,V_j)`.

The index-divisibility congruence is also the elementary operation underlying
Kleinjung's existing root sieve over rotations. Here it is used to process
complete values for fixed pairs, rather than to score polynomials; that change
of loop order is not, by itself, a new asymptotic smoothness primitive.

### 3.2 Preprocessing and matrix costs before any optimization

All field-specific discriminants, bad-prime decisions, good ideal labels,
characters and square roots from §2 remain. The index sieve can avoid
precomputing every root of every f_i, but on accepted entries it must still
record `(i,p,a/b mod p)` and the correct valuation. The matrix has common
rational columns and K algebraic blocks, hence (2.7), not a single algebraic
base. Shared modular arithmetic does not identify ideals.

The conditional full exponent of the H016-backed explicit stream, with
ordinary balanced completion, is exactly (2.11), supplemented by any larger
actual selection, local-order or character-preparation exponent. The direct
index sieve additionally has the term `mu+gamma` from (3.2).

At the known optimum,

    mu=2 gamma,
    mu+kappa=beta+gamma < c_C,
    mu+gamma=3 gamma > c_C.                            (3.4)

The last inequality follows from `3 gamma/beta=sqrt(13)-1>2`.
Thus the literal prime scan for every Stage-1 pair is worse at those
parameters. H016 removes that avoidable scan, but only recovers the known
subdominant `K*M` charge. It does not change the matrix or initial sieve.

### 3.3 Decisive symbolic comparison and disposition

Equations (2.12)–(2.14) already optimized the **more optimistic** model in
which all second-stage processing and roots were free. Its infimum is still
c_C. Therefore any implementation change confined to the evaluation/smoothness
cost of the same norm streams, with (2.8), the common rational scan and the
same matrix dimension retained, cannot certify a smaller leading constant
through that model. This restricted deduction is proposed for independent
review; it is not an accepted theorem about all multi-field algorithms.

Generalizing to `f_i=f_0+i*g`, `g(m)=0 mod N`, does not automatically change
this result's hypotheses favorably. For `deg g<d`,

    H(f_i)<=H(f_0)+K H(g),
    F_i=F_0+i b^d g(a/b).                              (3.5)

The second term is an integer after degree-d homogenization. One must price
constructing g, its actual coefficient height, changed norm geometry,
irreducibility failures and all K*M values. If g is a multiple of `X-m`, this
is the established rotation framework. A common modular root alone asserts
neither smaller actual norms nor an improved smoothness law. If `deg g>=d`,
leading coefficients/degrees and their local/denominator issues also change.

**Disposition: no new survivor.** The recurrence is useful explicit structure,
but its priced implementation does not escape the baseline. A future change
would need a justified supply or matrix change as well, or a different initial
search method. The conclusion does not exclude such changes. No finite
benchmark can refute or establish the algebraic optimization above, so none is
proposed or run for this card.

## 4. Card B — A common target for algebraic data, with a square map

**Proposed saving.** Replace K independent ideal blocks by columns of one
target ring, while making a dependency produce a verifiable congruence of
squares. This attacks matrix enlargement, independently of Card A's processing
recurrence. A local root-table coincidence is insufficient; the target needs
an actual element-level square map.

### 4.1 Sufficient compatibility data, and why simple merging fails

One exact sufficient interface is the following. For each row j, construct
an element `v_j` of a common order A, a rational integer `r_j`, a known unit
`c_j mod N`, and an order homomorphism `psi:A->Z/NZ`, such that

    psi(v_j)=r_j c_j^2 mod N.                          (4.1)

All representations, valuations and square-class tests in A are paid. If
the selected rows yield both

    product_j v_j=w^2 in A, product_j r_j=y^2 in Z,

then

    x=psi(w)/(product_j c_j) mod N
    satisfies x^2=y^2 mod N.                           (4.2)

This is an elementary sufficient square-map lemma, proposed for independent
checking, not a supplied method for constructing its inputs. Denominators in
w require the same care as §2.3. Proper splitting and nonredundant rows remain
additional requirements. Taking `v_j=r_j` and `c_j=1` can supply only the
obvious repeated rational construction with a directly chosen root `w=y`;
that tautological implementation gives `x=y` and no split.

Mapping an element to its norm in a common subfield preserves multiplicative
squares, but generally does **not** meet (4.1) for its chosen modular image.
For example, if `f_i=X^2+s_i X+t_i` and `f_i(m)=0 mod N`, then

    Norm(a-b alpha_i)=a^2+s_i ab+t_i b^2
      =(a-bm)(a+b(s_i+m))+b^2 f_i(m).                 (4.3)

The missing ratio is `a+b(s_i+m) mod N`, not a known square. Claiming its
square root as free would add precisely the sort of modular-square-root
oracle forbidden in this task. Relative norms in towers have the analogous
compatibility obligation; no general impossibility is claimed for them.

Here is an entirely symbolic counterexample to deleting field labels merely
because local root labels and integer norms match. Take

    N=55, m=4,
    f_0=X^2-X+43, f_1=X^2+2364X+43.

Then `f_0(4)=55`, `f_1(4)=55*173`, and both reduce modulo 43 to `X(X-1)`.
Both are irreducible over Q: the first discriminant is -171; the second is
`2364^2-172`, strictly between `2363^2` and `2364^2`, since
`2*2364-1>172`. Both derivatives at m are congruent to 7 modulo 55, a unit;
the standard derivative check does not discard this example. At the good
prime 43, use the root-zero ideal in each field and the row `(a,b)=(0,1)`.
Each element `-alpha_i` has norm 43 and an odd valuation at **its own**
root-zero ideal. The common rational value is -4, so the two rational rows
multiply to 16; the two integer norms multiply to `43^2`. Nevertheless neither
individual field element is a square, since the norm of a field square is a
rational square and 43 is not one. Merging just these ideal columns would
erase exactly that obstruction. Separate square-class/character information
must still prevent treating this as two available field roots.

This hand-derived example is an algebraic witness, not a finite research run
or evidence about relation density. It does not assert that every compressed
matrix is unsound: a valid compression must supply a lifting map such as
(4.1)–(4.2), or another explicitly proved replacement.

### 4.2 Two precise ways local tables can be shared, and their costs

**Identical reductions.** Let `P=product_(p<=B_A) p` and construct

    f_i=f_0+i P(X-m).                                 (4.4)

The common root is preserved and all f_i have the same reduction at every
base prime. This really reuses the mod-p polynomial/root *tables*. It does
not reuse the ideals themselves or their prime-power valuations; beyond
mod p the polynomials may differ.

The price is explicit. The primorial has logarithm `theta(B_A)~B_A`.
For a nontrivial i, the changed coefficient has that bit scale; this is much
larger than V when `B_A=L[gamma]`. More generally, two distinct integer
polynomials congruent coefficientwise modulo P cannot both have height below
P/2: a nonzero coefficient difference is a multiple of P. The all-primes
table-identification construction therefore leaves the old height regime.

For (4.4), and nonzero primitive pairs from §2, `|b^(d-1)(a-mb)|>=1`.
The old F_0 is at most `exp(O(V))`, whereas P has logarithm of order B_A.
For i>=1, eventually

    |F_i| >= P-|F_0| >= P/2.                          (4.5)

Thus these actual norms, not just an upper bound, have bit length at least
order B_A. Explicitly processing K*M such norms costs at least their total
bit mass, and H016's polynomial-width corollary no longer applies. Storing
the changed polynomials costs `K B_A poly(n)` bits; an explicit norm stream
has scale `K M B_A` bits. Rejecting all changed fields avoids that cost only
by losing the intended family. Congruence modulo a much smaller primorial
can avoid this penalty, but shares tables only for that smaller core and
still supplies no element square map. This is a rejection of this concrete
table construction, not a bound on every form of preprocessing reuse.

**Actual common fields.** A field homomorphism into a common field is
injective; between number fields of equal degree it is an isomorphism.
Such maps can correctly transport ideals, characters and elements, provided
they are explicitly constructed and commute with reduction modulo N. The
result is then a collection of elements in one field; the K representations
themselves are not K supplies of new independent relations. An enlarged or
different element region could still be useful, but needs its own norm and
enumeration accounting.

For a concrete elementary example, `f_i(X)=f_0(X-iN)` still has root m
modulo N and root `alpha_i=alpha_0+iN` in the same field. Its elements are
`a-b alpha_i=(a-iNb)-b alpha_0`, so the relation map is an exact relabeling of
an enlarged old pair region. For monic degree d, the coefficient of
`X^(d-1)` is `c_(d-1)-d iN`; even that coefficient can be N-sized. In the
ordinary `a,b=exp(O(D))` region with b>=1, nonzero i changes the old first
coordinate by at least order N. Small old norms are not provided for free.
Using translation by i instead would move the modular root to `m+i`, and
therefore change the supposedly shared rational values. Neither version is
an uncharged common-root, small-norm source.

### 4.3 An explicit compatible construction: norm descent to integers

Rather than assume the missing map exists, it can be forced in degree two.
After the ordinary primality/even-input/perfect-power preprocessing, generate
K distinct primes `ell_i` coprime to N. The first K+n primes suffice to find
K such primes or a proper gcd, since N has at most n distinct prime divisors.
Sieve/gcd construction costs `(K+n) poly(n,log(K+n))`; it is not advice.

Set

    f_i(X)=X^2+ell_i N, m=0, alpha_i^2=-ell_i N.        (4.6)

Every polynomial is monic irreducible over Q, since it has no rational root.
They define distinct imaginary quadratic fields: equality of two such fields
would require `ell_i/ell_j` to be a rational square, impossible for distinct
primes. The common modular root and degree are explicit; actual coefficient
height is exactly `ell_i N`. No hidden factor of N is used.

Enumerate pairs `1<=a<=A, 1<=b<=H, gcd(a,b)=1` and every field. With M the
raw pair count, generate all K*M integers

    q_(i,a,b)=Norm(a-b alpha_i)=a^2+ell_i N b^2,
    q_(i,a,b)=a^2 mod N.                               (4.7)

The second identity is the required computable square map. Here the common
target is Z and the known modular root is a; there is no requirement to make
`a-b alpha_i` a square in its own field. This is why integer prime columns
are legitimate in this construction, whereas they were illegitimate in the
preceding example. It is a changed relation equation, not the deletion of
unwanted ideal coordinates from the original NFS equation.

In fact `f_i'(0)=0`, so importing the ordinary NFS derivative-denominator
pipeline at this root would fail its invertibility check. It is not being
silently used: identity (4.7) supplies the modular square directly, and the
integer reconstruction below proves correctness independently of that pipeline.

Factor smooth q's over one **integer** base B, retaining full exponents.
A parity dependency gives

    Y=product_(p<=B) p^((sum_j v_p(q_j))/2) mod N,
    X=product_j a_j mod N,
    X^2=product_j q_j=Y^2 mod N.                        (4.8)

This construction genuinely has one column set, regardless of K, and an
executable root map for every returned dependency. Gcd verification is the
same as §2.3. Every selection/gcd failure is paid. Irreducibility needs no
search here; no field root tables, ideal class groups, algebraic characters
or algebraic roots are needed because (4.7) replaced those obligations.

Different triples need not give different integers or independent parity
rows. Keep exact tuple/known-root provenance; sort to detect identical
`(q,a mod N)` relations. If the same q has two different modular roots, test
their gcd difference/sum explicitly rather than calling the pair new rank.
Repeated identical relation equations supply the tautological square, not
new evidence for useful yield. After these filters, denote the number of
distinct admitted relations by R. No lower bound on R or on productive
dependencies has been assumed. Nonprimitive candidates and rejected
duplicates are still part of K*M paid attempts.

For polynomial `n,log A,log H,log K,log B` widths, complete integer processing
costs `(B+K M) poly(n,log A,log H,log K,log B)`. The matrix has at most
`pi(B)` columns and R polynomial-weight rows; its actual dimension/nonzeros
determine the sparse-linear-algebra charge. Reconstructing (4.8) costs
`R poly(n,log B,log R)` given the full valuations. Storage includes batch
scratch, retained rows and dependency lifting. No count of fields replaces
the norm-object charge.

### 4.4 Its decisive size comparison and prior art

The norm bounds are exact:

    N <= q_(i,a,b) <= A^2+ell_max N H^2.               (4.9)

For `log A,log H,log K=o(log N)`, these are N-scale norms, not the
`exp(O(V))` norms that motivate general NFS. In particular, at NFS-sized
`K*M=L[u]` and `B=L[b]`, the ordinary size-based smoothness substitution for
N-sized integers predicts

    log(probability) = -(2/(3b)+o(1)) V,               (4.10)

which cannot supply `L[b]` relations from `L[u]` explicit attempts for fixed
u,b>0. This is a conditional model comparison, not a proved upper bound on
the smoothness of this structured sequence.

At the more natural `L_N[1/2]` scale let `B=L_N[1/2,b]` and total scanned
attempts be `L_N[1/2,u]`. Subexponential A,H,K keep the leading norm
logarithm equal to t. The same smoothness model and common-base obligation
give

    u>=b+1/(2b), c>=max(u,2b).                         (4.11)

Their infimum is `sqrt(2)`, at `b=1/sqrt(2)`, already on a worse L exponent
than NFS. This is just a particularly simple congruent-square relation
construction with positive quadratic norms, not a new factoring bound.
If a larger a-range changes the norm's t-scale coefficient to eta>=1, the
term becomes `eta/(2b)` and the relaxation does not improve.

Trying `X^2-ell_i N` instead, with reducibles explicitly handled, changes
the norm to `a^2-ell_i N b^2`. Its small values come from the familiar
cancellation near square roots; `ell=1,b=1` is the ordinary quadratic-sieve
polynomial. These relations have an integer square map for the same classical
reason. Pomerance's primary treatment supplies the quadratic-sieve baseline
`L_N[1/2,1]` and explicitly discusses multiple-polynomial variants. Calling
the multipliers “fields with shared columns” would not create a new mechanism.

**Disposition: no new survivor.** The common-column square-map obligation is
solvable in the explicit family (4.6), and its reconstruction is exact; its
norm-size/yield model loses and its relation architecture is classical.
Sharing just local labels is unsound for the original fieldwise-root method;
transporting genuinely isomorphic fields is legitimate but does not grant
additional useful elements at the old heights. Other norm/tower/square-class
maps remain possible, but no input-only family with the needed norm sizes,
nonredundant supply and cheaper complete cost is supplied in this round.

## 5. The decision inequality a changed construction would have to pass

The two cards use different exact square maps, so their intermediate row
counts cannot be compared without their respective final reconstruction.
For a prospective genuine many-field change, use the following ledger.
It specifies a falsifier, not a claim that its favorable parameters exist.

Let Q be all attempted fields, K the retained fields, M_i the paid pair count
in field i, U the aggregate bits of all actual norm inputs, and R the number
of nonredundant retained relations with lifting records. Let D_mat,W be
the actual matrix dimension scale and nonzero count. Let P_map include any
common-ring maps, changes of basis, inverse maps and their verification. Pay

    T_trial = P_family(Q)+P_base+P_char+P_bad+P_map
            + T_rational+T_norms(U)+T_ideal
            + T_dedup/filter(R)+T_LA(D_mat,W)
            + T_lift+sum_i T_root(i)+T_gcd.             (5.1)

Rational-side tests may be shared only when their integer values really are
the same. Common *factor-base prime generation* does not make the K ideal
bases common. For explicit norm streams with polynomial widths, the default
term is `sum_i M_i poly(n)`, equal to K*M in the balanced construction. Any
replacement must specify an exact algorithm, its preprocessing and output
format, and prove the smaller complete bound; compact input notation alone
does not change (5.1). Large bit widths require the U charge instead.

For illustration, keep (2.3)'s sizes, one rational box, K=L[kappa], and a
uniform justified rate `L[-tau_A-ell]` of distinct admissible algebraic
relations on the Stage-1 stream. Here ell>=0 is an explicitly assumed loss
for duplicates, bad-prime exclusions or other filters; a different or biased
yield law must be substituted if proved. If the certified replacement matrix
has `D_mat=L[q]`, retain the conventional quota `R>=L[q]` as a modeled
collection obligation, not a universal lower bound on the number of rows
needed for a dependency. A necessary inequality for that modeled quota is

    kappa+2 epsilon-tau_R-tau_A-ell >= q.              (5.2)

For the original separate bases, `q=max(beta,kappa+gamma)`. A valid shared
structure may reduce q only with a square map and paid reconstruction. A
method relying on only a subset of fields must use its actual participating
counts, not credit every polynomial as useful.

If field/preparation/filter/root exponents are respectively p and r after
taking their maxima, explicit norms have polynomial width, retained row
weight is polynomial, and the actual proper-trial probability has reciprocal
`L[s]`, the conventional sufficient-cost *envelope* would be

    c_full = max(p, 2 epsilon,
                 kappa+2 epsilon-tau_R, 2q, r)+s.     (5.3)

Here (5.2) alone is only a necessary expected-supply inequality under the
declared law. To turn (5.3) into a factoring upper bound requires enough
usable output with appropriate stopping/restart control, paid square maps
and a proved or explicitly matched heuristic productive-split probability.
Neither independent ideal valuations nor useful square-root signs are
inferred from a raw success count. For a differing matrix algorithm replace
`2q` by its actual paid bound, including fill and lifting.

This exposes three distinct ways a promising formula can fail:

1. A norm selector moves `K*M` work into table building, whose exponent then
   enters p, or produces larger operands, whose aggregate bits enter U.
2. A purported matrix compression drops field labels without an element-level
   square map; then it has no valid q for (5.2)–(5.3).
3. A field or pair selector has an attractive unconditional average, but its
   actual adaptive/post-filter supply or sigma_N is unknown. Its claimed
   c_full is conditional, even if every arithmetic operation is correct.

Card A changes none of (5.2)'s favorable parameters and cannot lower the
restricted infimum even after its second-stage charge is erased. Card B
correctly changes the reconstruction and q, but changes norm scale from V to
t and thereby leaves this `L_N[1/3]` model. Neither satisfies a new cold
`c_full<c_C` comparison. No unlimited low-norm-field, all-smooth-output, rank,
hidden-factor or algebraic-root primitive has been introduced.

## 6. Handoff and next action

**Best supported result of this round:** a primary-text reconstruction of
the known multiple-field constant and factory boundary, an explicit paid
field-index processor, a scoped symbolic explanation of why removing that
processor's cost cannot change the same model's optimum, and an explicit
common-column construction whose exact square map reveals its classical
quadratic-congruence scope. New project deductions are not accepted until
independent review.

**Two cards assessed; zero new survivors selected.** No separately authorized
finite experiment is needed for either closure. In particular, a smoothness
sweep would not establish the missing all-input/adaptive law or make these
identities novel. There are no seeds, budgets or unreported trials because
no computational research protocol was executed or proposed as a survivor.

The precise next action is independent symbolic review of:

- the restricted optimization (2.12)–(2.15), including the `delta<6 gamma`
  monotonicity step and the fact that the discarded terms are subdominant;
- the field-index processor's complete K*M and M*B_A accounting;
- the square map (2.9)–(2.10), its derivative/invertibility qualification,
  and the distinction between fields' ideals and common rational primes;
- (4.1)–(4.8), the field-label witness, the primorial height/input-bit penalty,
  and the precise limited scope of the positive-norm model (4.10)–(4.11).

If accepted, these findings close only these concrete mechanisms under their
stated models. Reopening requires an explicit materially changed family,
yield law, norm-processing primitive or square map with its full cost; it
does not require enlarging a parameter grid for the present constructions.
The coordinator owns that decision, independent-review launch, hypothesis
registry, checkpoint and synthesis. This child has made none of those edits.

**Verified full factoring complexity improvement remains NONE.**
