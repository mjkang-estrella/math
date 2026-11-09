# H016 — Independent review of batch integer and good-prime ideal processing

Date: 2026-10-08. Reviewed the full
[H016 construction](H016-batch-smoothness.md), its provenance and retained
primary sources. **Disposition: accept the integer-processing construction
and the restricted good-prime ideal construction, with the source, sampling,
access and memory qualifications below.** No correctness defect invalidating
either subroutine was found. These are reviewed informal mathematical
algorithms and cost bounds, not an implementation benchmark, Lean refinement,
novel batch-factorization algorithm, or completed NFS algorithm.

**Verified factoring complexity improvement: NONE.** The value 1.89 remains
a conditional per-trial envelope. In particular, rejection of all rows meeting
the polynomial discriminant introduces an unquantified supply loss.

## 1. Scope and decisions

Read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md and research/STATE.md; the H016 hypothesis; W001 Card C
and shared accounting; the full H008 and H013 dispositions; and the full
H014 enumerator report, independent review and disposition. H014's current
disposition supersedes H016's historical description of it as provisional:
its exact enumeration primitive has passed review. Its factoring interpretation
remains conditional. H017's supply certificate and H018's degree model are
separate reviews and are neither assessed nor assumed here.

The individual decisions are:

1. **ACCEPT — integer interface and polynomial-overhead conclusion.** All
   signed inputs, both sides, repetitions, zeros, units and failed candidates
   can be processed in `(B+S) poly(n)` including prime construction, provided
   scalar, payload and identifier widths have the stated polynomial bounds.
   The aggregate-bit formula must be retained without those promises.
2. **ACCEPT — exact smooth parts.** The remainder tree, logarithmically many
   modular squarings, and gcd give the entire smooth part with multiplicities.
   The corrected double-exponential cutoff is essential and is present in
   the source PDF.
3. **ACCEPT — full sparse exponent recovery.** The prime-partition invariant
   bounds fragment mass at every depth; it avoids a separate prime-base scan
   for every input. Leaf exponent decoding is logarithmic in the exponent,
   and tags preserve repeated occurrences. Output and routing are paid.
4. **ACCEPT WITH EXPLICIT REALIZATION — cost and memory bounds.** The arithmetic
   bound `O(b_total L^3 L2)` follows for this construction, independently of
   the sharper smooth-parts theorem. The larger bit-access bound in H016 is
   sufficient with the levelwise scheduling described in section 4 below.
   It is not a theorem about arbitrary RAM-to-tape simulation or CPython.
5. **ACCEPT — good-prime ideal labels and quadratic splitting.** Under monic
   irreducible f, primitive g, nonzero norm and p not dividing disc(f), the
   gcd finds exactly the relevant degree-one or degree-two factors. Expected
   polynomial splitting and deterministic `B^2 poly(n)` preprocessing are
   correctly distinguished. Sampling and table access need the explicit
   interpretations in sections 5 and 7.
6. **ACCEPT — Hensel valuations.** The digit update is correct, the local
   coefficient criterion gives the ideal valuation, and precision `E+1`
   suffices. Degree drops, repeated roots of g and primes dividing its leading
   coefficient do not invalidate this construction.
7. **ACCEPT — restricted completion statement; REJECT stronger readings.**
   Bad-prime rejection needs no discriminant factorization or global integral
   basis, but does not preserve useful supply by theorem. Character evaluation
   is costed only for supplied verified labels. Sufficient characters, useful
   rank, square roots, denominator handling, splitting and restarts remain
   separate obligations. Removing an upper implementation cost `S B` proves
   no factoring improvement or lower bound on other methods.

The specific clarifications to carry into parent synthesis are:

- Bernstein's *small-factors* Algorithm 7.1 literally assumes odd primes;
  strip the 2-part separately if using it. H016's own algorithm includes 2
  directly, so its integer lemma does not need revision.
- In quadratic randomized splitting, interpret a uniform linear polynomial
  as `a X+b` with both coefficients independently uniform in F_p, including
  a=0. This makes the stated CRT independence exact.
- For deterministic root preprocessing, use sorted joins or paid indexed
  access. Scanning the entire root table anew for each row would invalidate
  the claimed cost. A sequential join realization is supplied below.
- The `B poly(n)` streaming memory statement is working memory. Retaining
  every failure/vector on disk or all relation rows adds their actual size.
  During integer recursion, discard temporary trees between frontiers;
  retaining every intermediate tree at every recursion depth is unnecessary.

These are clarifications of the reviewed algorithms, not a new factoring
mechanism. No substantial positive claim beyond the supplied brief is proposed
for acceptance. Any future strengthening of supply, bad-prime handling or
completion still requires its own independent review.

## 2. Primary-source and provenance audit

Fresh requests to the author's server retrieved both Bernstein PDFs and the
paper index. Their SHA-256 digests agree exactly with the retained PDFs. The
index contains the retained small-factors PDF link. The web tool separately
returned HTTP 502 for the smooth-parts PDF and index; standard-library HTTP
retrieval succeeded. Both outcomes are recorded in
[H016-review-inputs.json](H016-review-inputs.json).

The full retained smooth-parts text was read, including Algorithm 2.1 and
Theorems 2.2–2.3. The retained page-three image was inspected: the condition
is `2^(2^e) >= x`, not `2^e >= x`. Theorem 2.3 gives
`O(b log^2(b) log log(b))` for smooth parts, with b the input-bit mass.
It does not claim this bound for labeled prime exponent vectors. The paper
explicitly separates subsequent factoring, and states its conventional
memory-access model. [Bernstein, smooth parts](https://cr.yp.to/factorization/smoothparts-20040510.pdf).

The small-factors introduction and sections 4–7 were inspected, including
the multiplication model, division, product/remainder trees and recursive
support algorithm. With nonempty positive-integer multiset N, distinct odd prime list P,
`U=bits(N)`, `Pbits=bits(P)`, and minimal nonnegative j,k bounding their
cardinalities by powers of two, Theorem 7.2 has the bound

    [(100jk+108j+j(j+1)/2+12)U +25k Pbits+24*2^k]
      * mu(2 max(U,Pbits+1)).

Thus H016's asymptotic simplification is valid. Removing powers of 2 by a
binary scan costs linear input work if this particular source algorithm is
used. Its output is distinct prime support; full multiplicities require
another step. H016 uses its own prime-partition construction for that step,
whose cost is checked below rather than attributed to Theorem 7.2.
[Bernstein, small factors](https://cr.yp.to/papers/sf-20020923-retypeset20220327.pdf),
[author index](https://cr.yp.to/papers.html#sf).

The H016 report and all five retained Bernstein source artifacts match their
proposer-manifest byte lengths and hashes. All listed historical inputs also
match except research/STATE.md, which is an actively updated parent checkpoint.
The review read the updated checkpoint. This difference is not a change to
the mathematical report. H014's newer review/disposition are additional review
inputs. Hashes establish correspondence, not historical execution chronology.

The relevant primary Dedekind–Kummer statement, finite-field splitting discussion,
and NFS square-class/root discussion were also opened. Their roles and limits
are stated where used below. No indexed abstract substitutes for an algorithm.

## 3. Exact integer algorithm and exponent output

Use H016's notation: P is the sum of the bit lengths of all primes <=B;
U is the sum of bit lengths of all absolute scalar entries >=2 in S pairs;
`b_total=2+P+U+2S`; `L=max(1,log2(b_total+2))` and
`L2=max(1,log2 log2(b_total+4))`. I is other input payload in bits.
The intended cutoff B is a nonnegative integer, encoded and read as part
of the input. The small cases B<2 and S=0 are dispatched explicitly.

For x>=2, let ell=bitlength(x), let Z be the product of the base primes, and
choose `e=ceil(log2 ell)`. Then `v_p(x)<ell<=2^e` for every prime divisor p.
For a base prime, `v_p(Z^(2^e))=2^e`; for a prime outside the base it is zero.
Consequently

    gcd(x,Z^(2^e)) = product_(p<=B) p^v_p(x).

The algorithm obtains the argument modulo x by a remainder tree followed by
e squarings. It never constructs Z raised to this exponent. A zero remainder
correctly yields gcd(x,0)=x. Repeated input moduli need not be coprime: each
child product divides its parent product, which is all the remainder-tree
identity requires. There are no CRT inversions between input moduli.

Zero is excluded before constructing the input product tree: it has no finite
largest smooth divisor. Both signs and units have explicit output statuses.
For a negative input the absolute value is processed and the sign retained.
For ±1 the vector is empty and residual is 1; this does not certify that an
algebraic element of unit norm is a square. With an empty base every nonzero
input has smooth part 1. Every occurrence retains `(row,side)` even if all
its numbers match another occurrence. No distinctness or success fraction
is assumed in the processing lemma.

For exponent recovery, a node owns a disjoint prime interval Q and tagged
Q-smooth fragments z>1. Extracting the left-prime smooth part gives l;
exact division gives r=z/l. Unique integer factorization proves that l and r
are coprime and have exactly the required prime supports. A tag has at most
one fragment in any particular prime-tree node. At a leaf that fragment is
`p^e`, and the prime label is known from the leaf. Neither a norm factor nor
another row's exponent can be substituted for this labeled output.

At any recursion frontier, fragments belonging to an original s_x have
product dividing s_x (equal to it if completed leaves are included).
Since every retained fragment z>=2 has
`bitlength(z)<=2 log2(z)`,

    sum_frontier bitlength(z) <= 2 sum_x log2(s_x) <= 2U.

This remains true when some leaves are already finished. Fragment count is
at most U, and prime-group bit masses sum to at most P. Thus an entire
prime-tree depth has the aggregate mass of one smooth-part computation, up
to a constant. The depth is O(log(K+2)), K the number of base primes, hence
O(L). There is no multiplication by K of the original input mass.

At a leaf, repeatedly square p until the first power `p^(2^j)>z`; it has
at most twice the width of z. In descending j order, divide the current
remainder by that power whenever exact, adding `2^j` to the exponent counter.
If the current remainder is `p^t`, divisibility holds exactly when `t>=2^j`.
Descending binary subtraction therefore ends at t=0 with the exact exponent.
Only O(log bitlength(z)) divisions/comparisons and squarings are needed.
All operands have O(bitlength(z)) bits. In particular p=2 and an enormous
exponent do not cause e successive divisions.

There are at most U emitted `(tag,p,e)` records. For a leaf p^e, both
`log2 p` and `log2(e+1)` are bounded by a constant times `e log2 p`;
the nonidentifier output-bit mass is O(U). Row and side identifiers add
O(U L). Smooth-part/residual values contribute O(U), signs/statuses O(S),
and retained candidate payload I. Reconstructing powers/products and checking
`x=s_x*c_x` is possible in the same allowance. A dense S-by-K output is not
part of the claim and would have a different output cost.

## 4. Arithmetic, access, prime construction and streaming

Take fast integer multiplication
`M(t)=O(t log(t+2) log log(t+4))`, fast division O(M(t)), and gcd
O(M(t) log(t+2)). These are bit-cost primitives on the actual operand widths.
They cannot be replaced by schoolbook multiplication at aggregate nodes
while preserving a near-linear aggregate bound.

For a balanced product/remainder tree, total numeric width on each level
is O(b_total) and the number of levels is O(L). If the dividend at the first
reduction is larger than the entire modulus product, that single division
is charged at the larger width, at most O(P+U). Subsequent remainders have
their parent-product width. The nondecreasing envelope M(t)/t bounds the sum
of costs on each level; highly unequal input widths do not break it.
The recognition pass therefore costs `O(b_total L^2 L2)`. Leaf powering
and gcd obey the same aggregate bound.

At each prime-partition depth the preceding section gives total numeric
mass O(P+U+S), including fragment and active-node counts. Another O(L)
depths give `O(b_total L^3 L2)` arithmetic work. Leaf exponent recovery is
no larger. This derives H016's formula (1) for its actual described route;
it does not assert that the smooth-parts theorem alone includes labeling.

For clarity, the larger formula (2) has a sequential realization. Store
records with explicit lengths and O(L)-bit tags/tree-node identifiers.
Process product/remainder levels by sequential passes, pairing adjacent
children and routing to children by tags; use merge sorting where regrouping
is necessary. At one numeric tree level there are O(b_total) numeric bits
and at most O(b_total L) total tagged bits. Sorting costs at most another
O(L) passes. There are O(L) numeric tree levels within each of O(L)
prime-partition depths. A conservative total of O(b_total L^4) bit movement
therefore suffices, in addition to the arithmetic. Keep unrelated payload
separate from fragments and join it by row tag only when needed; repeated
payload copying down the prime tree is unnecessary. Reading, retaining and
sorting that payload fits the stated `(I+1)log^2(I+b_total+2)` allowance.
This supports

    O(B log^3(B+2) + b_total L^4 L2
      + (I+1)log^2(I+b_total+2)).

It is an existence bound for scheduled bit algorithms, not a blanket claim
that random access to a huge table costs one bit step. Bernstein's sharper
theorem is not silently promoted to this different access model.

The prime base is constructed. Generating all composite marks k*j<=B with
`2<=k<=sqrt(B), j>=k` makes O(B log(B+2)) records. Each has O(log(B+2))
bits. Repeated addition generates a row of multiples at that width; merge
sorting and complement scanning cost O(B log^3(B+2)) bits of work. Every
composite has a divisor <=sqrt(B), so the complement is precisely the
primes. Duplicates and the scratch O(B log^2(B+2)) bits are paid. An ordinary
sieve is also valid with its access model specified. The elementary bound
`P<=B log2(B+1)` is enough for the conclusion; no prime-count asymptotic
is being used to hide base construction.

Discard temporary product/remainder trees after producing the next fragment
frontier. Keeping the current frontier, its temporary trees and sorting
scratch then fits `O(b_total L^2+I+output_bits)` bits, plus sieve scratch.
Fast arithmetic is done on its own charged scratch. This is compatible with
full-batch operation; it does not require retaining every temporary tree
from every prime depth simultaneously.

For streaming, use scalar batches of total nontrivial bits at least
`C=max(2,P,w)` and at most C+2w except the last. With J nonempty batches,
`J<=1+U/C`, so repeated base work has mass

    JP <= P+U,       JC <= C+U.

The looser O(P+U+w) allowance is valid, including a short final batch.
Pairs can be kept together with overshoot 2w, or one partial row can be
carried across a boundary; an unbounded queue of unpaired sides is not
required. Zeros and units are emitted immediately and still incur identifier,
payload and status work. Prime generation is performed once.

Consequently the full integer conclusion is `(B+S) poly(n)` when w,
log(B+2), log(S+2), and record/payload widths are polynomial in n. For H014,
its degree/coefficient promises and `S<=H(2H+1)^2` provide the required
width and identifier bounds. Without these promises, formula (2), including
I, is the accepted statement. Neither B nor S is being declared polynomial
in n. The near-linear statement concerns expanded aggregate data and has
logarithmic overhead; constructing that data from the binary cutoff B is
explicitly charged.

Working memory is B poly(n) in the H014 regime (including the polynomial
buffer-width term). Retained R relation rows cost R poly(n) additional bits;
retaining all S statuses and exponent vectors costs S poly(n). No small-memory
claim erases those output costs. None of this proves a finite speedup for
an unimplemented fast-arithmetic library.

## 5. Good-prime labels and splitting

Assume f is monic irreducible of degree d>=3, alpha is its root, and
Delta=disc(f) is nonzero. These are field prerequisites, not consequences of
ordinary base expansion. Computing Delta as a determinant/resultant has
polynomial bit cost in the stated degree and coefficient widths; factoring
Delta is not required.

The identity `disc(f)=[O_K:Z[alpha]]^2 disc(O_K)` implies that
p not dividing Delta is both unramified and locally prime to the order index.
Dedekind–Kummer then labels maximal-order primes by the monic irreducible
factors h of f mod p, with norm p^deg(h). Its hypotheses are met without
constructing a global integral basis. [Sutherland, Theorem 2.1 and the
following good-prime discussion](https://math.mit.edu/~drew/ArithmeticEquivalenceLectureNotes.pdf).

Primitivity makes g mod p nonzero for every prime. With f monic, p divides
its resultant with g exactly when these reduced polynomials have a nonconstant
gcd, even if g loses degree. Since f mod p is squarefree,
`h_all=gcd(f mod p,g mod p)` is squarefree of degree <=2. Its irreducible
factors are exactly the relevant prime ideals. A higher-degree irreducible
factor cannot divide the nonzero polynomial g mod p. A prime dividing the
quadratic leading coefficient merely changes the actual reduced degree;
no division by that leading coefficient is needed. A double root of g is
included once by the gcd, with its ideal valuation determined separately.

Linear h_all is already factored. For quadratic h_all, compute
`gcd(h_all,(X^p mod h_all)-X)` to decide whether it is irreducible or split. A
squarefree quadratic with one linear factor has two distinct linear factors.
At p=2 enumerate the two residues.

For odd p in the split case, choose z=aX+b with independent uniform a,b
in F_p. Evaluation at the two distinct roots is an invertible linear map
F_p^2 -> F_p^2, so its two components are independent uniform residues.
Exactly one zero component already gives a proper gcd with h_all. Conditional
on both components being nonzero, their quadratic signs differ with probability
1/2, and gcd(h_all,z^((p-1)/2)-1) gives a proper factor then. The unconditional
success probability is

    2(p-1)/p^2 + (p-1)^2/(2p^2) >= 1/2   (p>=3).

This is a direct verification of H016's degree-two procedure. Each attempt
costs poly(log p), and uniform sampling by rejection from binary strings also
has constant expected retries. Verify the returned factors. All failed attempts
are included in the expected bound. This is Las Vegas expected time, without
a deterministic worst-case cap. The cited primary notes give the general
randomized gcd-splitting context; the independent-component calculation here
uses H016's full affine sampler rather than assuming independence for a
single random shift. [Sutherland, sections 3.11–3.12](https://math.mit.edu/classes/18.783/2022/LectureNotes3.pdf).

The parity example in H016 is correct. For
`f=X^3+2X^2+X+5=(X+2)(X^2+1)+3` and `g=X^2+1`, none of ±1,±5 is a root,
so f is irreducible. The cubic discriminant formula gives
`4-4-160-675+180=-655`. Modulo 3 the factors are X-1 and the irreducible
quadratic X^2+1. Evaluating f at the two roots of g gives resultant 9.
The degree-one ideal does not divide g(alpha), so the degree-two ideal has
valuation 1. An even integer norm exponent has indeed hidden an odd ideal
valuation. This is a symbolic verification of the supplied example, not a
new finite experiment or evidence of useful candidate supply.

## 6. Hensel lifting and exact local valuations

Fix a relevant factor h of degree r in {1,2}, put
`C_1=(f mod p)/h`, and let `E=v_p(|Res(f,g)|)`. The two monic factors are
coprime. Suppose monic H_j,C_j lift them and f-H_j C_j is divisible
coefficientwise by p^j. Define D,U,V exactly as in H016:

    D=(f-H_j C_j)/p^j mod p,
    U=(C_1^(-1)D) mod h,
    V=(D-C_1 U)/h in F_p[X].

The inverse is modulo h. By its definition D-C_1 U is divisible by h,
so V is a polynomial, not a rational function. Leading monic terms cancel
in f-H_j C_j, giving deg D<d. Thus deg U<r and deg V<d-r. With coefficient
representatives chosen in [0,p-1], the updates preserve monicity and satisfy

    (H_j+p^j U)(C_j+p^j V)
      = H_j C_j+p^j(C_1 U+h V) mod p^(j+1)
      = f mod p^(j+1).

The omitted cross term is divisible by p^(2j), hence by p^(j+1) for j>=1.
Coprimality also gives uniqueness of the degree-bounded correction. The
sequence therefore extends coherently to the unique monic factor H over Z_p
lifting h, with its complement. No inverse of p or nonunit integer is used.

Because p is good, the local component Z_p[X]/H is the integer ring of
the unramified extension associated with the prime (p,h(alpha)). Its
reduction is the field F_p[X]/h and p is a uniformizer. The power basis
`1,X,...,X^(r-1)` is a Z_p-basis of this component. Thus an element is in
p^t times this ring exactly when all its basis coefficients are divisible
by p^t. This local statement follows from the monic, separable factorization;
it assumes no integral basis for the global field.

Polynomial remainder modulo a monic polynomial commutes with reduction
modulo p^k. Therefore `g mod H_k` gives the coefficients of the local element
g(alpha) modulo p^k. Their minimum p-adic valuation is its exact ideal
valuation whenever that minimum is <k. Zero coefficients are assigned
truncated valuation k in this computation.

The principal-ideal norm identity is

    E = sum_(P|p) residue_degree(P)*v_P(g(alpha)).

All terms are nonnegative since g(alpha) is integral. Each relevant valuation
is at most E/r, so k=E+1 is strictly larger than it. At that precision not
all remainder coefficients can vanish. Hence the minimum criterion is exact;
an all-zero remainder indicates inconsistent input or computation. The final
weighted sum over factors of h_all equals E because factors outside that
gcd have valuation zero. The vector records the separate valuations, not
only this weighted check or the norm exponent parity.

Every lifting modulus has at most `(E+1)log2 p+O(1)<=w+log2 p+O(1)` bits,
and a support prime has log2 p<=w. There are E<=w steps, degrees at most d,
and original coefficients have the promised widths. Exact formation of D
also reads f at its own coefficient width; this remains polynomial even
when larger than the current modulus. Monic reduction of g, field gcd and
inversion, digit lifting, repeated coefficient divisions by p, and the norm
check can all use ordinary polynomial and schoolbook integer arithmetic at
these local widths. No fast aggregate multiplication theorem is needed here.

For example, with
`Q=d+w+ceil(log2(A+2))+ceil(log2(H+2))+ceil(log2(B+2))+2`,
there are polynomially many scalar operations per digit (a generous O(Q^3)),
O(Q) digits, O(Q^2)-bit intermediate scratch suffices, and ordinary arithmetic
plus sequential local storage access fits within O(Q^12) per support entry.
The allowance is loose; its role is an explicit uniform polynomial, not an
optimized implementation claim. Random splitting uses an expected number
of such bounded attempts. At most w support primes and two ideals per prime
therefore give S poly(n) expected work. Growth of d is paid throughout.

## 7. Deterministic root table, labels and storage

The alternative preprocessing really is deterministic. For each base prime
p, evaluate f(r) for all r=0,...,p-1 by modular Horner evaluation and store
only its roots. There are at most d roots per p, including when p<d, and

    sum_(p<=B) p <= B^2.

This establishes `B^2 poly(n)` construction work and `B poly(n)` storage.
It does not factor f mod p completely. A split degree-two h_all has its two
roots among the stored roots of f. Test that list and divide out the resulting
linear factors; if it contains none of h_all's roots, h_all is irreducible.
Only at most d tests are required once the correct prime's list is available.

That last lookup must be charged. A sequential realization collects tagged
support records, sorts them by p, and merges them with the root table ordered
by p. Buffer the current prime's at most d roots and process every support
record for that p before advancing. Attach g or its polynomial-width data
to the records; replication over its at most w support primes stays polynomial
per row. Sort the resulting labeled valuations by row when reassembling rows.
There is one table scan per batch, not per support entry.

For a single full batch this adds `(B+S) poly(n)` sorting/scan work. If B-scale
working memory is required, use batches of B rows (or a comparable B poly(n)
bit buffer), plus the final partial batch. There are at most 1+S/B batches
for B>=2, so all table scans cost `(B+S) poly(n)`. B<2 is dispatched before
this stage. The original integer batching can be coarsened or its outputs
buffered to this size. The joint deterministic stage therefore retains
`(B^2+S) poly(n)` work and B poly(n) working memory, plus retained output.
This is the explicit access repair supporting H016's deterministic option.

Canonical labels are `(p,monic h)` with coefficients in [0,p-1]. They do not
depend on the randomized factor-return order or on choices of integer lifts.
Sort and deduplicate the labels, assign column identifiers, and preserve the
tag-to-column map. There are at most d*pi(B) possible relevant good-prime
labels. Their universe and map occupy B poly(n) bits; each row has polynomial
weight. Global sorting of all occurrence records costs S poly(n) under
log S=poly(n); retaining all such records is additional S poly(n) storage.
It is not necessary to enumerate all degree-two factors of f in advance.

The base cutoff is rational p<=B. A degree-two ideal can have norm p^2>B
and is still included. This agrees with Card C. Imposing ideal norm<=B would
change both the accepted rows and the smoothness model.

## 8. Exceptional rows, characters and the remaining boundary

The test `gcd(|Res(f,g)|,|Delta|)=1` is an exact polynomial-width gcd per row.
For a retained B-smooth norm it removes every possible ramified or index-prime
contribution; any ideal above a prime not dividing the norm has zero valuation.
The good-prime procedure then yields the complete maximal-order ideal
factorization of that element. Negative Delta and norm ±1 are harmless.
Delta=0 or failure of the field prerequisite does not license this argument.

No factorization of Delta, no global maximal order, and no exceptional-prime
ideal handler is concealed in this rejection policy. Conversely, it gives
no quantitative lower bound on the surviving useful rows. Rejecting all
such rows may exhaust the population needed by the 1.89 model. Handling
them instead requires a separately costed local-order/ramification procedure;
the present lift cannot be applied when h and its complement are not coprime.

For supplied verified odd good auxiliary ideals (q,h), nonzero g mod h has
the quadratic character obtained by exponentiation to `(q^r-1)/2`, r=deg h.
The exponent has O(r log q) bits. Polynomial-width labels and polynomially
many characters give polynomial work per row, with zero residues handled
explicitly. If q>B and the norm is B-smooth, zero is impossible. Exact signs
at real embeddings can likewise be obtained by polynomial-time algebraic
sign determination with the stated degree/height bounds. The rational sign
and individual real signs must not be replaced by the norm sign.

These evaluations do not prove that a sufficient character family can be
obtained cheaply or that its kernel consists of squares. Even complete even
ideal valuations can leave class-group and unit square-class obstructions.
A square root in O_K may have denominators in the power basis and need not
lie in Z[alpha], where alpha -> m mod N is defined. These distinctions are
the explicit issues in the primary NFS treatment. [Stevenhagen, sections
6–10](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/04psh.pdf).

Character selection/search, useful rank, filtering/fill, dependency lifting,
algebraic square roots and a valid modular image with paid denominator or
multiplier handling remain obligations. Any gcd from a failed invertibility
test must satisfy 1<gcd<N to count as a split. A gcd equal to N is not a
proper factor. Repetitions can consume work without supplying fresh rank;
quota exhaustion and completed trivial congruences remain failures.

## 9. Accepted conditional envelope and handoff

With H014 now accepted as an exact enumerator, take S=S_all, including every
emitted candidate later rejected. The unconditional processing composition
within its input/width domain is

    T_enumeration+integers = (H^2+B+S) poly(n).

This includes evaluation of the polynomial-width integer pairs. After a
suitable field is supplied and the stated good-prime row restriction is used,
the ideal stage adds S poly(n) expected work, or `(B^2+S) poly(n)` deterministic
work. These are valid subroutine bounds whether or not one useful row exists.

In H014's unchanged upper-count notation,

    s=max(2a,3a-2(1-eta)/delta^2).

The integer stream has upper envelope max(2a,b,s), not s+b. The deterministic
good-prime alternative increases it to max(2a,2b,s), which is already the
conventional conditional sparse-linear-algebra scale in this model.

At eta=1/10, a=153/200, b=189/200 and delta=21/10, the supplied exact
fractions agree:

    2a=153/100,             s=18491/9800,
    s-[b+(2(1+eta)/delta+a delta)/(3b)] =1343/238140>0,
    2b-s=31/9800>0,         max(s,2b)=189/100.

The previous trial-division upper envelope s+b=13876/4900 is therefore not
needed for integer processing. It was an upper implementation cost, never
a lower bound. H016 does not reopen H008's thin-root route or H013's full
cube model, and it does not change H014's eta=.4 conditional exclusion.

The strongest justified 1.89 statement is still conditional on enough actual
distinct primitive irreducible **good-prime** useful rows with the stipulated
joint smoothness/yield law, together with paid field/character preparation,
filtering, useful rank, sparse linear algebra, dependency lifting, algebraic
square roots and proper modular reconstruction within that envelope. Replacing
the upper count by achieved supply, or applying the old smoothness assumption
unchanged after an unquantified bad-prime filter, is not justified.

This is a per-trial statement. Expected proper splitting further requires
a lower bound on success probability sigma_N and the cost of all failed
trials/restarts. Preserving the same leading constant requires, at minimum,
`sigma_N^(-1)=L_N[1/3,o(1)]` in the specified input scope and an appropriate
uniform expected trial-cost guarantee. Deterministic root enumeration does
not make the remaining factoring stages deterministic. There is no all-input
success or improved factoring theorem here.

No new executable, finite experiment, trial-division reference run, density
test or speed benchmark was needed or run. This was proof review, primary
source inspection, and read-only provenance checking. Shared build/Lean checks
were not rerun because there were no code or Lean changes. Writes are confined
to this review and adjacent H016-review-* provenance files. No proposer report,
evidence, hypothesis, registry, STATE, shared code or Lean was edited; no
package, delegation, commit, publication or scheduler was used.

The coordinator can accept the integer bottleneck as resolved by known paid
batch methods and the good-prime ideal stage as resolved in this explicit
restricted scope, carrying the clarifications in section 1. The next work is
the separately owned supply/completion question, not another unregistered
integer speed test. Final hashes and scope checks are recorded in
[H016-review-provenance.json](H016-review-provenance.json).

**Verified factoring complexity improvement remains NONE.**
