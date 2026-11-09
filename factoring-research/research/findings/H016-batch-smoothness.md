# H016 — Paid batch smoothness and the boundary with ideal processing

Date: 2026-10-08. **Constructive mathematical analysis; new applications and
cost claims here await independent review. Verified factoring complexity
improvement: NONE.**

The integer-processing obligation has a known constructive solution. For S
signed integer pairs of at most w bits per entry, prime-base construction,
smoothness recognition, and sparse **full prime exponent vectors**, including
all unsuccessful inputs, cost `(B+S) poly(n)` when
`w, log(B+2), log(S+2) = poly(n)`. The arithmetic is quasi-linear in aggregate
bits with explicit logarithmic overhead below. It is not trial division by
the entire base separately for every candidate. It does use fast multiplication
on aggregate-sized integers; schoolbook multiplication at those nodes would
not establish the bound.

This does not identify the resultant's integer exponents with ideal exponents.
For monic irreducible f and primitive quadratic g, this report also constructs
and costs the actual ideal labels and valuations at primes not dividing
`disc(f)`. No integral basis or discriminant factorization is needed for that
restricted construction. It can reject every row whose norm meets the
discriminant, at charged cost and with **unquantified loss of useful supply**.
Retaining those exceptional rows needs additional local-order work not supplied
here. Character evaluation is costed separately from producing a sufficient
set of characters or finding an algebraic square root.

Accordingly, H014's `s+b` integer trial-division envelope can be replaced by
`max(s,b)`. Its stronger-cutoff **conditional** total envelope is again
`max(s,2b)=1.89` at its stated witness, provided all the remaining population,
algebraic and completion hypotheses hold. This is neither a new NFS bound nor
a finding about H017's population question.

## 1. Scope, evidence and primary-source check

Read in full: AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, research/STATE.md, research/hypotheses/H016.md,
W001-relations.md (including its shared accounting and Card C),
H008-disposition.md, H013-disposition.md, and
[H014-resultant-enumerator.md](H014-resultant-enumerator.md).
The checkpoint is `research/STATE.md`; there is no project-root `STATE` file.
H014 remains provisional under its separate review. Neither its enumerator
nor H017's supply task is duplicated here.

The two requested Bernstein primary papers were successfully retrieved from
the author's server by Python's standard-library HTTP client after browser
`open` calls returned HTTP 502. This is actual full-paper access, not reliance
on an indexed abstract:

- [How to find smooth parts of integers, 2004-05-10](https://cr.yp.to/factorization/smoothparts-20040510.pdf):
  inspected the full seven-page paper, especially Algorithm 2.1 and Theorems
  2.2–2.3 on pp. 3–4. The latter gives
  `O(b_total (log b_total)^2 log log b_total)` for smooth parts.
- [How to find small factors of integers, 2002-09-23, retypeset 2022-03-27](https://cr.yp.to/papers/sf-20020923-retypeset20220327.pdf),
  reached through the author's [sf index entry](https://cr.yp.to/papers.html#sf):
  inspected §§4–7, including the product/remainder algorithms and Theorem 7.2.
  Algorithm 7.1 recursively partitions the integer multiset, discarding primes
  not dividing each subproduct. It returns each input's distinct prime support;
  multiplicities still need extraction. Its input-bit bound has one more
  logarithmic factor than the smooth-parts bound. In its notation, if
  `j=ceil(log2 #inputs)`, `k=ceil(log2 #primes)`, integer-bit mass is U,
  prime-bit mass is P, and multiplication costs `t*mu(t)` with nondecreasing
  mu, Theorem 7.2 gives
  `O((U*(1+j^2+j*k)+P*(1+k))*mu(O(U+P+1)))`.
  Substituting `mu(t)=O(log(t+2) log log(t+4))` yields the cubic-log bound
  for prime support, including a multiset of repeated inputs.

The indexed primary text displayed the cutoff in Algorithm 2.1 incorrectly
as `2^e >= x`. The PDF and its proof instead say **`2^(2^e) >= x`**. The
[retained page image](H016-batch-source-smoothparts-p3.png) was inspected to
resolve this material transcription error. In the construction below we use
the sufficient safe choice `2^e >= bitlength(x)`, requiring only
`O(log bitlength(x))` squarings.

The retained PDFs/text and hashes are in
[H016-batch-provenance.json](H016-batch-provenance.json). No novelty is claimed
for these algorithms, product/remainder trees, gcd, or coprime splitting.
Sections 2–5 give an explicit construction and its own cost argument, including
an exponent-recovery variant, rather than extending the abstract's claim by
assertion. No fast multiplication library or new executable was implemented;
no finite experiment, density test, or benchmark was run. Therefore there is
no unregistered validation run or trial-division reference cost to hide.

## 2. Precise integer interface and costs

There are S records with scalar entries `u_i=g_i(m)` and
`v_i=Res(f,g_i)`; the integer lemma itself works for arbitrary signed entries.
Let `ell(x)=bitlength(x)` for positive x. Set

    P_B = { primes p <= B },        K = #P_B,
    P = sum_{p in P_B} ell(p),
    U = sum_{all entries |x|>=2} ell(|x|),
    b_total = 2 + P + U + 2S,
    L = max(1, log2(b_total+2)),
    L2 = max(1, log2 log2(b_total+4)).

Let I also count the bits of candidate coefficients/provenance and any other
input payload, beyond the scalar values. Their reading, copying and retained
output are charged. In H014 these are polynomial bits per record. The labels
`(row number, side)` cost `O(log(S+2))` bits each, not constant space.

The construction below has arithmetic cost

    O(b_total L^3 L2),                                      (1)

plus prime enumeration. A deliberately conservative bound including sorting,
record identifiers, explicit tree traversal and bit data movement is

    O(B log^3(B+2) + b_total L^4 L2
      + (I+1) log^2(I+b_total+2)).                           (2)

The fourth power is a sufficient allowance for bookkeeping, not a claim of
optimality. The useful distinction is logarithmic rather than multiplicative
B overhead. The integers in product trees have up to `O(b_total)` bits, not
w bits; scratch inside multiplication/division is charged at that width.
Use, for example, the established multiplication bound
`M(t)=O(t log(t+2) log log(t+4))`, fast division `O(M(t))`, and fast gcd
`O(M(t) log(t+2))`. Bernstein's checked cost proofs use these kinds of bounds.
No unbounded-integer unit-cost model is used.

For a direct full-batch implementation, storing trees, fragments, tags and
sorting scratch has the conservative allowance
`O(b_total L^2 + I + output_bits)` bits, in addition to the temporary sieve
scratch specified below. The output is sparse:
`(row, side, sign, status, smooth part, residual cofactor, [(p,e),...])`.
An S-by-K dense matrix would have a different, potentially S*K, output cost
and is not required. Relation matrices are also initially sparse.

### Base construction is paid

A standard Eratosthenes sieve constructs P_B in `B poly(log(B+2))` bit work;
the primes are not input advice. A simple entirely sequential alternative
suffices if random array access is a concern: generate all multiples
`k*j <= B`, `2 <= k <= floor(sqrt(B))`, `j >= k`; sort the resulting
`O(B log(B+2))` composite marks and scan the complement in `[2,B]`.
Every composite has such a mark, and no prime does. Binary generation and
merge sorting give the `O(B log^3(B+2))` allowance in (2), with
`O(B log^2(B+2))` bits of scratch. Duplicate marks are paid for.
No prime-number asymptotic is needed: `P <= B log2(B+1)` is sufficient.

If B<2, the base is empty; each nonzero absolute value has smooth part 1.
S=0 is an empty stream and needs no prime construction unless another stage
requests the base. These cases do not invoke a modulo-zero operation or an
empty-tree routine with undefined behavior.

### Signs, zero, units and repetitions

- Store the sign of every nonzero x and run the positive-integer routine on
  `|x|`. Negative values can be smooth in this convention; the rational sign
  becomes a parity column. The sign of a norm is not the full list of real
  embedding signs of the algebraic element.
- For x=0, emit `ZERO / not an admissible multiplicative relation`. There is
  no finite largest B-smooth divisor of zero. Do not put zero in a product
  tree. The zero-resultant and zero-rational cases remain charged failures.
- For x=1 or -1, emit smooth part 1, residual 1, and the empty exponent list,
  preserving the sign. An algebraic norm of ±1 identifies a unit, not a square.
- Every occurrence has its own row label. Identical numbers, identical pairs,
  and repeated g's may all be processed; their bits and output count enter U,
  I and S. Repeated moduli cause no difficulty in remainder trees because
  this algorithm does not use CRT inverses between those moduli. Optional
  deduplication is an additional charged sort, not an assumed supply gain.

## 3. Smoothness recognition for every input

For all nontrivial positive values x in the batch:

1. Construct the balanced product tree of P_B and its root
   `Z=product_{p<=B} p`.
2. Construct a balanced tree of the x's. Reduce Z at its root modulo the root
   product, and recursively reduce each remainder modulo both child products.
   At a leaf this gives `r_x=Z mod x`. Unbalanced operand widths are handled
   by fast division at their actual bit sizes.
3. Choose `e=ceil(log2 ell(x))`, set `y=r_x`, and perform e modular squarings
   modulo x. Thus `y=Z^(2^e) mod x`, without materializing `Z^(2^e)`.
4. Set `s_x=gcd(x,y)` and `c_x=x/s_x`. Report smooth iff `c_x=1`.

For any prime q not in the base, `v_q(Z)=0`; for a base prime p,
`v_p(Z)=1` and `v_p(x)<ell(x)<=2^e`. Consequently

    gcd(x, Z^(2^e)) = product_{p<=B} p^(v_p(x)).             (3)

This proves both exact smooth-part extraction and recognition, with all
multiplicities. A leaf can have remainder zero; gcd(x,0)=x is correct.
No assumption about how often x is smooth, or about independence of the two
sides, occurs in this proof.

At each balanced tree level the total bit size of products is `O(P+U+S)`;
tree depth is logarithmic. Summing multiplication/division by using the
nondecreasing `M(t)/t` envelope gives `O(b_total L^2 L2)` for product and
remainder trees. At each x, modular powering and gcd cost at most
`O(ell(x) log^2(ell(x)+2) log log(ell(x)+4))`. Summing has the same bound.
This agrees with the checked smooth-parts theorem. There is no multiplication
of a B-bit prime product separately with each original input.

The two scalar streams may be concatenated or processed in paired batches.
Testing the second side only after first-side success is optional; the bound
already pays both sides of every record, including both-side failures.

## 4. Constructive full exponent vectors, not merely smooth parts

The following balanced prime-partition routine is a convenient explicit
variant of known batch smooth-part/coprime splitting. It avoids assuming that
a gcd has already labeled its prime powers. It can factor **every smooth
part**, even of rejected inputs. Factoring only fully smooth retained rows
is an optional saving and is unnecessary for the stated upper bound.

Build a balanced binary tree of the ordered distinct primes. At a node with
prime subset Q, carry the list of tagged integers `z_i>1` known to be Q-smooth.
At the root these are the nontrivial s_x from (3).

    split(Q, tagged z):
        if list empty: return
        if Q has one prime p:
            for each tagged z: recover e from z=p^e; emit (tag,p,e)
            return
        divide Q into its consecutive halves Q_left,Q_right
        run Section 3 on every z with prime base Q_left
        call the returned smooth part l; set r=z/l by exact division
        pass tagged l>1 to the left child and tagged r>1 to the right
        recurse on the two children

Correctness follows by unique integer prime factorization: l contains exactly
the prime powers with primes in Q_left, and r exactly those in Q_right.
They are coprime and their product is z. Eventually every nontrivial fragment
is a pure power of its leaf prime. Exponents from a single tag are not merged
with another occurrence's exponents.

The crucial size invariant is stronger than counting successful rows. At each
prime-tree depth, the product of all fragments descended from one original
smooth part is that part. Every retained fragment is >=2, so

    sum_fragment ell(fragment)
      <= 2 sum_fragment log2(fragment)
      <= 2 sum_original log2(s_x) <= 2U.                    (4)

Thus fragment count is also at most U. The prime groups at that depth are
disjoint and their total prime-bit mass is P. Calls to the smooth-part routine
on disjoint groups therefore cost at most
`O((P+U+S)L^2 L2)` per depth, not K or B times this amount. There are at most
`ceil(log2(max(2,K)))` depths. Even rebuilding product/remainder trees in each
call fits (1). Empty children stop immediately; building/storing the original
prime partition is also charged.

For a leaf `z=p^e`, recover e without e divisions by p: construct the powers
`p, p^2, p^4, ...` by squaring up to the first exceeding z (at most twice
ell(z) bits). Scan back down. When the current power divides the current
remainder, divide it out and add its exponent to a binary counter. The final
remainder is 1; the accumulated counter is e. There are `O(log ell(z))`
operations at widths `O(ell(z))`, so this stage costs
`O(M(ell(z)) log(ell(z)+2))`. The sum of leaf bit lengths is O(U) by (4).
Reconstructing each smooth part from its emitted powers and checking
`x=s_x*c_x` likewise fits the quasi-linear allowance. Full exponents, not
just odd exponents, can therefore be retained for later reconstruction.

The total number of `(tag,p,e)` records is at most U. Prime and exponent bit
lengths sum to O(U): `log p <= e log p` and `log(e+1)<=e` for e>=1.
Including O(L)-bit identifiers gives O(U L) output bits. Tree group identifiers,
explicit lengths, and sequential or sorted routing fit the looser (2).
At worst a full hierarchy has O(L) levels of O(b_total L) tagged data.
Levelwise streams and merge sorting avoid any assumption of free access to
an S-by-B array. Reading and writing these data is included in (2).

This also explains the distinction in the primary sources: the smooth-parts
bound is not automatically a bound for already labeled exponent vectors.
An additional logarithmic-depth refinement, or the small-factors algorithm
followed by charged multiplicity extraction, is needed. No favorable fraction
of smooth inputs is required for the construction above.

## 5. Streaming, storage and the poly(n) qualification

A single batch is enough for the mathematical bound, but H014 need not retain
all S values in RAM. Let `C=max(2,P,w)` and group nontrivial scalar inputs into
batches of total input bits between C and `C+2w`, except the last. Unit/zero
statuses are handled as encountered. There are at most `1+U/C` nonempty
batches. Even if the P-bit prime tree is rebuilt for each batch, its total
bit charge is `O(U+P+w)`; it is **not** paid once per scalar. Each batch's
arithmetic uses `O(C)`-bit nodes and
`C poly(log(C+2),log(S+2))` working bits, with the
more conservative tagged-tree allowance above. Keep the two sides' statuses
until the pair is classified, which costs the current batch's record space.

H014 thus admits `B poly(n)` working memory for this stage, including a
base-sized buffer, when w and log B are polynomial in n. A stream of statuses
or retained evidence still costs `S poly(n)` disk/output bits if requested.
Retaining R accepted relation records costs `R poly(n)` bits, separately from
batch scratch. If every input's complete vector is kept, that output must
also be paid. A claim of tiny constant memory would be false. A batch much
smaller than the prime-base bit mass can repeatedly pay for the base; the
chosen batch size prevents that hidden factor.

Since `P<=B log(B+1)` and `U<=2S w`, (2) implies `(B+S) poly(n)` when

    w, d, log(A+2), log(H+2), log(B+2), log(S+2) = poly(n),  (5)

and candidate payloads have polynomial width. In H014, `S<=H(2H+1)^2`,
so its log S promise follows from its log H promise. Arbitrarily many repeated
inputs in a general externally supplied stream require the separate log S
qualification for record identifiers, sorting and retained provenance.
Without (5), retain the explicit aggregate/logarithmic bound; do not silently
rename it `(B+S) poly(n)`. B and S themselves remain subexponential-sized
quantities, not polynomial in n.

## 6. Why integer norm parity is insufficient

For the ideal stage assume **monic irreducible** f of degree d>=3, an algebraic
integer alpha with f(alpha)=0, and `K_f=Q(alpha)`. Do not apply field arguments
to an arbitrary reducible f output by ordinary base expansion. Field selection
and verification are a separately charged prerequisite. Put
`Delta=disc(f)!=0`; compute it by the resultant of f and f', in polynomial
bit work. Its bit length is polynomial in d and coefficient width.

For any nonzero g(alpha),

    v_p(|Res(f,g)|) = sum_{P|p} residue_degree(P) * v_P(g(alpha)). (6)

In particular even v_p of the integer resultant need not imply even ideal
valuations. A concrete algebraic illustration, requiring no numerical
experiment, is

    f=X^3+2X^2+X+5=(X+2)(X^2+1)+3,
    g=X^2+1.

The rational-root test makes f irreducible (the only possible integer roots
are ±1,±5, and none is a root). Its discriminant is -655, coprime to 3.
Modulo 3, f is `(X-1)(X^2+1)` and `X^2+1` is irreducible. The resultant is
9 by the displayed identity. The degree-two prime `(3,alpha^2+1)` has ideal
valuation 1 in g(alpha); its norm is 9. Thus a single odd ideal valuation is
invisible in the even integer exponent 2. These f coefficients are even
compatible with ordinary base 10 expansion, f(10)=1215; the example is about
parity information, not a useful relation population or a factoring result.

The background distinction and the subsequent square-class/root obligations
are described in [Stevenhagen, The number field sieve, §§3–10](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/04psh.pdf).
The construction next explicitly supplies the missing good-prime labels and
valuations; it does not assert that (6) can be inverted from the norm alone.

## 7. Costed good-prime ideal assignment for a primitive quadratic

Call p good when `p does not divide Delta`. This sufficient criterion excludes
all ramified and index primes; it may exclude more than necessary. At good p,
the order `Z[alpha]` is already maximal locally and f mod p is square-free.
Its monic irreducible factors h label distinct maximal-order prime ideals

    P_(p,h) = (p,h(alpha)) O_K,  Norm(P_(p,h))=p^deg(h).

This is the good-prime case of
[Dedekind–Kummer, Sutherland, Theorem 2.1 and following discussion](https://math.mit.edu/~drew/ArithmeticEquivalenceLectureNotes.pdf).
The formula is usable without computing O_K or an integral basis globally.

Process only primitive g after the already charged gcd(a,b,c) test. Then
g mod p is nonzero for every p, although its degree can drop. For each prime
p in the recovered support of the resultant, do the following:

1. Test `Delta mod p`. If zero, mark this row exceptional; use the rejection
   policy in §8 unless a separately paid handler is supplied.
2. Compute `h_all=gcd(f mod p, g mod p)` as a monic polynomial. At good p
   it is square-free, has degree <=2, and is nonconstant because p divides
   the resultant. A constant gcd in this situation is a consistency failure.
3. Factor this degree-at-most-two polynomial over F_p. A linear factor labels
   a degree-one ideal. An irreducible quadratic labels one degree-two ideal.
   A split quadratic labels **two separate** degree-one ideals. With primitive
   quadratic g, higher residue degrees cannot divide g(alpha): an irreducible
   factor of f dividing nonzero g mod p has degree at most 2.

This handles primes dividing a: use the actual reduced degree, not a formula
requiring a inverse. If g mod p has a repeated root, gcd with square-free f
still gives that root once; the ideal's valuation is computed next rather
than inferred from the multiplicity of the root of g mod p.

### Splitting costs and randomness

Irreducibility of a square-free quadratic h is tested by
`gcd(h,X^p-X)` with modular powering. If split and p odd, choose a uniform
linear polynomial z modulo h. Compute `gcd(h,z)` first; a proper factor
finishes. For a unit z, try `gcd(h,z^((p-1)/2)-1)`. CRT makes the two nonzero
components independent; their quadratic signs differ with probability 1/2.
Counting also the nonunit choices gives a constant success probability per
attempt (uniformly in odd p). Repeat only unsuccessful choices, and verify
the returned factors by multiplication. For p=2, test its two elements.

This is the degree-two instance of finite-field randomized splitting; see
[Sutherland, finite-field algorithms, §§3.11–3.12](https://math.mit.edu/classes/18.783/2022/LectureNotes3.pdf).
Each attempt has polynomial bit cost in log p; the expected number of
attempts is bounded by a constant, and uniform sampling's rejected bit strings
are also paid. This is **Las Vegas expected time**, not deterministic
worst-case polynomial time. All unsuccessful splitting attempts count.

There is a simple deterministic alternative relevant to the 1.89 envelope:
once per base prime, evaluate f at every r in F_p and store all its roots.
This costs at most `sum_{p<=B} p * poly(d,log B,log A)`, hence
`B^2 poly(n)` total, with at most d stored roots per p. Each subsequent h_all
can be split by testing this stored list; if a degree-two h_all has no root
there, it is irreducible. This adds B^2 preprocessing, **not S*B work**, and
requires no integer or finite-field factorization oracle. It is slower than
the expected-time option, but its exponent is already the assumed 2b
linear-algebra scale. Character/root stages still have their own conditions.

### Exact valuations by a bounded Hensel lift

Let `E=v_p(|Res(f,g)|)` from integer factoring and fix one irreducible factor
h of degree r=1 or 2 in step 3. Start with
`H_1=h` and `C_1=(f mod p)/h`, which are coprime monic factors modulo p.
Lift the factorization `f=H_j C_j mod p^j` to `k=E+1` digits. One executable
digit step computes

    D_j=(f-H_j C_j)/p^j mod p,
    U_j=(C_1^(-1) D_j) mod h,
    V_j=(D_j-C_1 U_j)/h in F_p[X],
    H_(j+1)=H_j+p^j U_j,
    C_(j+1)=C_j+p^j V_j.

Here the inverse is computed by polynomial extended gcd; U_j has degree <r,
V_j has degree <d-r. Coefficients are represented modulo p^(j+1), leading
coefficients stay 1, and the lift identity is checked. The coprimality of
H_1,C_1 guarantees existence and uniqueness. Doubling precision is possible
but unnecessary for a polynomial overhead bound.

Reduce g modulo monic H_k in `(Z/p^k)[X]`, obtaining r coefficients. The
minimum of their p-adic valuations (truncated at k) is exactly
`v_(P_(p,h))(g(alpha))`. Indeed the local component is the unramified
degree-r extension with integral basis `1,X,...,X^(r-1)`, and its uniformizer
is p. Membership in p^j is coefficientwise divisibility. This is a **local**
basis proved by the square-free lift, not an assumed global integral basis.

Equation (6) bounds this valuation by E/r<=E. Thus k=E+1 is enough to
distinguish the exact finite valuation; an all-zero remainder at that
precision is a consistency failure. Finally verify

    sum_{h divides h_all} deg(h)*v_(p,h) = E.              (7)

This verifies the weighted norm accounting without confusing it with the
separate parity vector `(v_(p,h) mod 2)_h`.

Every modulus here has bit length at most
`(E+1) log2 p + O(1) <= w+log2 p+O(1)`, which is O(w) for a prime actually
dividing a nonunit w-bit resultant. There are <=w lifting steps per support
entry; all polynomial degrees are <=d. Plain polynomial arithmetic and
schoolbook integer arithmetic therefore suffice **locally**, with a uniform
polynomial bound in `(d,w,log A,log H,log B)`. For example an ample allowance
is `O((d+w+log(A+2)+log(H+2)+log(B+2)+1)^12)` per support entry, including
field gcd, the digit lifts and valuation checks; optimization is unnecessary.
There are at most w support primes per row, and at most two relevant ideals
per such prime. The total good-prime stage is S poly(n) expected work, or
`(B^2+S) poly(n)` with the deterministic precomputed-root option.

We need not factor f mod p completely for every p. Store canonical labels
`(p,monic h)` with coefficient residues in `[0,p-1]`; sort labels to obtain
matrix-column numbers and preserve the map. Globally there are at most
`d*pi(B)` possible such good ideals, so their count and bit storage are
`B poly(n)`. Per-row support is polynomial in n. Sorting and provenance
costs depend on log S and are covered by (5). An ideal of degree two has
norm p^2, possibly >B; this base is bounded by **rational p<=B**, exactly
as Card C stipulates. Replacing it with an ideal-norm cutoff B would change
the accepted set and its smoothness model.

## 8. Exceptional primes, square-class information and failures

### A safe complete rejection policy, with a real supply cost

For the restricted ideal pipeline retain an otherwise smooth row only if

    gcd(|Res(f,g)|, |Delta|)=1.                            (8)

Compute this gcd on polynomial-width integers for each row, or use the
already recovered support and Delta mod p tests. This detects the bad-prime
intersection **without factoring Delta**. All valuations above the excluded
primes are then zero, so the good-prime construction gives the complete
maximal-order ideal factorization of every retained element. Delta=0 is a
failed field prerequisite, not a case where this filter licenses ideal use.
Negative Delta and norm ±1 cause no ambiguity in (8).

This policy does not prove that enough rows survive. Smoothness and useful
population assumptions must now refer to the actual set after (8), or a
bound for its loss must be added. That loss could destroy the optimistic
envelope. This task establishes no lower supply and does not reinterpret the
H014 upper count as supply.

To retain exceptional rows instead, repeated factors of f mod p alone do
not suffice. When p divides the index, factors of f mod p can fail to label
the distinct maximal-order primes; ramification changes the local valuation
calculation, and h and its complement may not be coprime, so the digit lift
above is unavailable. A separately verified local p-maximal order/prime
decomposition algorithm, its bases and transformation costs, and its exact
valuation computation must be paid for. Such a full handler is not supplied
or assumed polynomial here. Enumerating all bad p<=B by testing Delta mod p
costs B poly(n), but is not the same as solving those local problems. Bad
prime factors >B cannot divide an accepted B-smooth integer norm; neither
they nor a complete factorization of Delta need be obtained for (8).

### Signs and characters are additional columns

Real signs of g at f's real embeddings can be determined by exact algebraic
sign evaluation/root isolation in polynomial time per row under the degree
and height bounds, with no common f,g root in the field case. Record these
signs and the separate rational sign. Even ideal valuations plus these signs
still do not prove an algebraic square: units and the relevant square-class
quotient remain.

For a **supplied and verified** auxiliary prime-ideal label `(q,h)`, with
q odd, q not dividing Delta, h irreducible of degree r, and g mod h nonzero,
one character can be evaluated as

    (g mod (q,h))^((q^r-1)/2) in F_q[X]/h,                (9)

which is ±1. The exponent has O(r log q) bits and modular polynomial
arithmetic makes its evaluation polynomial in `(d,log q,log H)`. For
J=poly(n) such characters of polynomial-width labels the cost is
`R*J*poly(n)` and J extra bits per retained row. If q>B and the integer
norm is B-smooth, the image is automatically nonzero; otherwise zero is an
undefined character evaluation and the row/character choice must be handled
explicitly. A new choice and every failed search are charged.

Producing a sufficient set of useful auxiliary ideals/characters is a
different obligation: include `P_char`, including prime search, splitting,
irreducibility checks, exclusions and unsuccessful choices. Finite-field
factoring of each tested polynomial has expected polynomial cost, but neither
the number/range of suitable tested primes nor a spanning/distribution
guarantee for these selected rows is established here. Equation (9) proves
evaluation cost, not sufficient characters or a square-class theorem.
Stevenhagen §§8–10 is precisely the background warning: parity relations,
character constraints and actual algebraic square roots are distinct stages.
No class group, unit group, square-root oracle, or free maximal order is used.

### Failure accounting

Nonprimitive/reducible g rejected under H014's intended filter, zero values,
non-smooth sides, bad-prime rows, duplicate rows, character zeros and failed
field/splitting attempts are all charged to their corresponding stream or
preprocessing count. This construction can fail to deliver any usable row
without invalidating its processing bound. It does not call quota failure
success, interpret duplicate rows as new rank, or count a trivial congruence
as a split. A factor test `gcd(value,N)` on any polynomial-width value costs
poly(n); only `1<gcd<N` is a verified proper divisor. Gcd equal to 1 or N
and aborted collection attempts remain unsuccessful outcomes.

## 9. The exact conditional envelope that changes

Retain H014's provisional generator and set S=S_all, **including** emitted
triples later rejected. It pays `H^2 poly(n)+S poly(n)`. Appending §§2–5 gives
the deterministic integer-processing statement

    T_generator+integer = (H^2+B+S) poly(n).              (10)

This conclusion uses no probability of smoothness. With
`H=L_N[1/3,a]`, `B=L_N[1/3,b]`, H014's upper-population allowance is

    s = max(2a, 3a-2(1-eta)/delta^2).

Conditional on H014's enumerator, its full stream plus integer processing
therefore has the **upper cost envelope** `L_N[1/3,max(2a,s,b)]`.
The upper count gives no usable lower population. If the actual attempted
population has exponent u<s, charge its actual number plus H^2 and B;
do not insist it actually incurs exponent s.

At `eta=1/10`, `a=153/200`, `b=189/200`, `delta=21/10`, H014 records

    2a = 1.53,
    s = 18491/9800 = 1.8868367346...,
    b + [2(1+eta)/delta+a*delta]/(3b)
      = s-1343/238140 < s,
    2b = 1.89.

Thus ordinary independent trial division's `s+b = 13876/4900`, about
2.832, is **not a necessary processing cost**. The construction removes
that extra b. It replaces an upper-bound implementation, not a proven lower
bound. It does not undo H008's thin-root obstruction or reopen H013's
unchanged full-H^3-scan model. H014's eta=.4 conditional exclusion is also
unaffected by making processing efficient.

The strongest total statement justified at this witness is:

> If H014's enumerator is correct at its stated bit cost; if enough primitive,
> irreducible, distinct, good-prime rows survive with the stipulated joint
> smoothness/yield law (or exceptional rows have a separately paid handler);
> and if field/character preprocessing, filtering, rank, sparse linear algebra,
> dependency lifting and algebraic square roots all fit the conventional
> completion allowance, then the per-trial upper envelope is
> `L_N[1/3,1.89]`.

Good-prime ideal processing fits this envelope either in expected time by
the quadratic splitting construction or deterministically with the extra
B^2 preprocessing. The deterministic option avoids silently assuming
deterministic polynomial-time finite-field root finding. It does not make
the other conditional stages deterministic or prove their success.

More explicitly the full trial still pays

    P_field + P_char + (H^2+B+S)poly(n)
      + C_ideal + F(R) + T_LA + T_root + T_gcd.             (11)

With (8), `C_ideal` has the good-prime cost above. For R on the B scale and
polynomial row weight, a suitable sparse linear-algebra model may have
`T_LA=L_N[1/3,2b]`; fill, extra rows, deficient useful rank and restarts
cannot simply be assumed away. Exact row processing neither proves this
rank behavior nor provides square roots. Retaining irreducible degree-two
ideals enlarges the possible column set by at most a polynomial factor d,
but says nothing about the rank those columns attain.

Moreover, a square root in the maximal order need not be represented in
Z[alpha]. The homomorphism alpha -> m modulo N on Z[alpha] does not by
itself extend to arbitrary denominators in a recovered root. Root
representation, denominator clearing or the usual multiplier construction,
invertibility checks modulo N, and any resulting proper-factor gcd are
part of T_root and T_gcd; they have not been supplied for free by ideal
factorization.

If independent trials produce a verified proper divisor with probability
sigma_N, an expected splitting bound includes the complete failed-trial
and restart cost, schematically `T_trial/sigma_N`. To retain the 1.89
leading constant requires at least `sigma_N^(-1)=L_N[1/3,o(1)]` and the
appropriate uniform trial-cost bound; no such result is proved here.
No all-composite or useful-splitting guarantee follows from integer smoothness.

## 10. Disposition and review target

**Integer obligation: constructive solution using known algorithms, with a
provisional project-level proof of the full exponent/output accounting.**
The hidden S*B objection is removed for this downstream integer stage.
**Ideal obligation: solved here only for the explicitly restricted good-prime
rows, with randomized/deterministic costs distinguished.** The rejection
policy is executable but its supply loss is unknown; retaining bad-prime
rows and obtaining sufficient square-class information remain separate work.

The next action is independent review of (3)–(4), exponent extraction and
data movement, the local Hensel valuation argument and its precision bound,
the deterministic B^2 option, and the interpretation of (10)–(11). Supply
and correlation work belongs to the separate population task. No implementation
or density experiment is needed to validate a claimed finite speedup, because
no such speedup is claimed. No shared code, Lean, STATE, registry, hypothesis,
prior evidence, package, delegate, commit, publication or scheduler was changed.

**Verified factoring complexity improvement remains NONE.**
