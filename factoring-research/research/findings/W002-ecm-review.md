# W002 Lens C — first independent review of the Ward norm tensor

2026-10-08. **Independent symbolic review; no prior review round or proposer response.**
**Verified COMPLETE classical factoring complexity improvement: NONE.**
**Recommendation: accept the scoped algebra and extraction result after the local
completions below; reject the two specified implementations as an additive batch
speedup. Do not accept a universal norm/compression obstruction or a new factoring
bound.** Acceptance and edits to shared records remain the coordinator's work.

The negative conclusion is supported by an independent check of the construction,
not used as a substitute for checking it. I found no error in the four base
values, eight-coordinate transition, tensor invariant, or full-gcd recovery
criterion. The exact success identity is valid on its residual input branch,
and the distinct-semiprime formula remains valid when a characteristic divides
K. There are necessary domain, access-accounting, comparison-quantifier and
provenance completions. None supplies the missing useful-mass theorem or a
faster recurrence.

All submission line references below refer to the unchanged 518-line report.
The [frozen evidence directory](W002-ecm-review-evidence/) contains the original
report, preserved draft, intake, brief, instructions, relevant dispositions,
source bytes and saved lifecycle snapshots. No sibling W002 report or review
was read. No source/delivery manifest, shared file, code or Lean file was changed.

## 1. Evidence boundary and identities

The report and W002-ecm-submitted-draft.md independently hash to
`c73d5c34bd6ba6dc1a283d94edf75fd36fcbacf53f3a539cabc3722c1f80f8df`.
The intake hashes to
`90dd593cde0be7778dec9baed3343b8ea18eeca52a3a4a501cce95b7197aa78f`.
The frozen W002 brief hashes to
`5f34c276110ba4ad79781b16b4a86d7ea3860671d168939aca9c399b0480f723`.
All match the user-provided identities.

I froze 46 input files and independently verified all 20 original input
snapshots, all 30 delivery entries and all 10 new-source artifact identities.
These are 60 manifest checks with overlaps, not 60 distinct sources. Results
and byte counts are in [freeze-manifest.json](W002-ecm-review-evidence/freeze-manifest.json).
The current STATE and synthesis were copied separately from the constructor's
saved versions; their differences do not invalidate the saved hashes.

I read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, the current STATE, W001 synthesis, W001-dynamics Card 4,
the full H009 finding, the Li prior-art note, and H030/H031 dispositions.
Those dispositions establish the lifecycle boundary; this review does not
reopen their mathematics. Shared documents contain summaries of other work,
but no sibling W002 draft/review was opened or independently audited.

The reviewer-specific instruction is preserved in
[reviewer-brief.txt](W002-ecm-review-evidence/reviewer-brief.txt).
The review's final delivery manifest is separate from all original manifests.

## 2. Exact domains and scalar invariant

**R1 — make the domains explicit.** The algebraic evaluator takes odd N>1,
positive integer K, and s>=0 supplied residues a_i modulo N. It does not need
squarefreeness, distinct parameters, or a nonsingular discriminant. Its
polynomial identities hold over Z[1/2] and hence over Z/NZ. Elliptic group
interpretation needs the nonsingular field reduction, separately. K=0 and
even N are not covered by the stated implementation. The factoring driver
accepts arbitrary composite N>1, first returning a proper divisor 2 or 3.
On the remaining branch gcd(N,6)=1. These distinctions should be added at
submission lines 63 and 355.

Li's Definition 3.1.1, printed p.17, gives the base values and the odd/even
identities with q>=2 and q>=3 respectively. Substituting x=0, y=1, b=1 gives

    f_1=1, f_2=2, f_3=-a^2, f_4=-4(a^3+8),
    f_(2q+1)=f_(q+2) f_q^3 - f_(q-1) f_(q+1)^3,
    f_(2q)=(1/2) f_q (f_(q+2) f_(q-1)^2 - f_(q-2) f_(q+1)^2).

This checks the signs and the factor 1/2 in the even formula. In the evaluator,
1/2 means the fixed unit u=(N+1)/2 modulo N. There is no division by f_q,
a difference of parameters, a discriminant, K, or a hidden prime. Zeros and
other nonunits can pass through every update.

For initialization, use the odd identity for indices 5,7,9,11 with
q=2,3,4,5, and the even identity for 6,8,10 with q=3,4,5. Every required
input index is strictly smaller than the output index and at least 1.
For example, the largest needed input for f_11 is f_7. Consequently increasing
index order constructs f_1 through f_11 from the four displayed base values.
The first three bits give m in {4,5,6,7}, so [m-3,m+4] is contained in [1,11].
For h=3 this is already the final window. For h<3 and positive K, only K=1,2,3
occurs; the output is the product of the corresponding base values. The empty
list returns 1 without tensor construction.

For one later bit b, write q=m+t. When b+j=2t+1, the requested output is
f_(2q+1). For b=0, odd t runs from -2 through 1; for b=1 it runs from -1
through 2. Thus t+2,t,t-1,t+1 all lie in J={-3,...,4}, and q>=2.
When b+j=2t, t runs from -1 through 2 for either b; t+2,t-2,t+1,t-1 all lie
in J, and q>=3. This checks the endpoints, including the even t=-1 case
that uses the old offset -3. The two four-tuples in (1) are exactly the
factors of these recurrences. In particular the even output is quartic,
not cubic: its outer f_q is essential.

Induction on the remaining binary digits therefore gives the scalar invariant
v_m(a)=(f_(m+j)(a))_(j in J). The proof variable m need not be represented or
arithmetically doubled during execution; the program can stream K's bits.
The recurrence itself is a finite fixed table and does not conceal scalar-size
advice or a growing expression that is treated as a unit-cost operation.

**Recommendation:** accept (1) and the initialization with R1's domain sentence.
No base-value or transition formula needs replacement.

## 3. Tensor closure and the precise obstruction

Fix an output tuple j and choice vector epsilon. Substituting (3) into a term
of (4) gives

    product_(l=1..4) T_m(alpha^(l))
      = product_(i=1..s) product_(l=1..4)
          v_m(a_i)_(A_(b,j_i,epsilon_i,l)).

The product of the coefficients c_(b,j_i) is u^e_b(j); it is independent of
epsilon. Distributing the sum over all independent epsilon_i therefore
produces product_i F_b(v_m(a_i))_(j_i). This proves (4) and the next tensor
invariant. Repeated addresses mean repeated factors, not distinct lookups
that may be dropped. Cancellation and duplicate a_i do not change the proof.
At the final prefix, the all-zero tuple selects product_i f_K(a_i).

Initial successive tensor products write sum_(t=1..s)8^t=O(8^s) entries.
An expanded transition enumerates 8^s output tuples and 2^s branches per
tuple, hence precisely 16^s summands. This is an actual distributive
algorithm over a commutative ring, not an unevaluated norm or resultant.

The identity in submission line 180 is correct. Over the formal polynomial
ring, swapping u and v preserves xy and uv but changes the difference product
by the nonzero polynomial (x-y)(u-v). This demonstrates failure of those two
statistics on unrestricted formal row data. It does not construct two actual
ECM parameter lists having every proposed scalar statistic equal. Additional
elliptic relations, symmetric representations, circuits, or a different
compressed state remain possible. The submission explicitly maintains this
boundary; retain it in any disposition.

The lower bound (8) also has the right scope. Each specified transition writes
8^s separately allocated n-bit residues, whether zero or not. For h>3 the
write count is Omega((h-3)8^s n). This is a lower bound for this storage and
execution rule, not a density result, information-theoretic minimum, or lower
bound on factoring. An implementation skipping unwritten zeros or retaining
the known tensor factors would be a different implementation.

The obstruction has an attainable branch in the fixed driver: on every
composite N coprime to 6, the raw tape with every word a=0 passes the
screen because gcd(27,N)=1. It retains s=r=n, including all duplicates.
With B=n^2 and h=Theta(n^2), the specified expanded execution has
Omega(n^3 8^n) transition bit writes for large n. This is a symbolic witness
to its worst-case cost, not an experiment or success assertion. It already
excludes a uniform (s+h)poly(n,log(s+h)) bound for this implementation.
The general statement about s=Theta(log h) only identifies a power of h
in the slot count; whether that power can be hidden in poly(n) depends on
the relation between h and n. No stronger conclusion is needed.

Keeping the s initialized eight-vectors preserves their tensor factorization
without ever factoring a tensor over Z/NZ. There are O(sh) scalar ring
operations. Fixed-size blocking still processes Theta(s) blocks through
Theta(h) steps. These facts close the specified expanded and retained-factor
executions as the requested uniform additive escape. They do not close all
norm-first algorithms.

## 4. Setup, widths and the expanded sequential implementation

The setup sieve is finite and input-only. Enumerating j<=B/2 and
2<=k<=floor(B/j) writes O(B log B) composite marks; every composite at most B
has such a representation. Sorting and scanning remove duplicates and expose
the primes. Mark widths, loop arithmetic and merge passes cost B polylog B.
Constructing the maximal prime powers and multiplying them in a balanced
integer product tree yields K. Since log K is the Chebyshev function psi(B),
h=Theta(B). Product-tree levels have total operand length O(B), up to rounding,
so regular multiplication bounds give O(M(B)log B). Standard routines with
quasilinear workspace fit the stated B polylog B setup space. An arbitrary
multiplication black box is not granted an independent free workspace.

Screening can reduce after every multiplication in 4a^3+27; gcd is unchanged
by reduction. It costs O(r(M(n)+G(n)+n)), plus writing or reading original
slot identifiers if stored. The additional r log(r+1) traffic is already in
the final trial bound. The exact inverse u is available in O(n) time.
K is stored in h bits and raw randomness costs rn bits on the sampled branch.
No prime-counting, order-finding or factor-dependent choice is used here.

For a tensor update, reduce after each binary multiplication. Then each
multiplication's unreduced operands produce at most 2n bits. A sum/difference
needs at most n+O(1) bits before reduction. Multiplying all four factors as
one unreduced integer would need a different width statement; it is neither
necessary nor assumed. Each old/output address has 3s bits, epsilon has s,
and the factor number has constant width. Thus the stated request width
O(n+s) is sufficient.

A fixed number of sequential tapes can perform the two merge sorts and
joins. There are O(16^s) requests and O(s) sorting passes; each pass copies
O(16^s(n+s)) bits, with O(s)-bit key comparisons. Ordered emission,
address construction and modular arithmetic fit

    C(s,h,n)=O(h 16^s [M(n)+s(n+s)]), s>=1.

During the old-state join, one old value can serve any repeated requests
with that address. No missing address or nonunit exception arises. Reading
the final target entry by a scan costs O(8^s(n+s)), already within C.
Successive initial tensor products are also sequential: hold one new
constant-size vector and expand each old entry into eight new entries.

**Cache-access completion.** Computing u^0,...,u^s takes O(s) modular
multiplications and O(sn) bits. Looking up u^e is not free RAM access.
Scanning this cache once for each output costs O(8^s s(n+log(s+1))) per
transition, which is within C. Alternatively it can be joined by sorted
exponent requests. Computing e and the branch sign while enumerating tuples
also fits C. This completes the advertised access bound without changing it.

The two tensor generations, requests, merge scratch, cache and counters fit
O(16^s(n+s)+h+s(n+log(r+1))+W(n)) bits. The exponentially larger request
storage, not merely the 8^s tensor, is the relevant upper bound. After releasing
setup scratch, the overall peak is the maximum of this and B polylog B,
plus the stored raw words/label map O(r(n+log(r+1))). Arithmetic workspace is
reused; standard M,G,division implementations give W(n)=n polylog n.

**R2 — repair the label-traffic statement at lines 329–330.** If each subquery
rescans records carrying original log(r+1)-bit labels, the displayed
O(s log(s+1)(n+log(r+1))) scan term is not uniformly absorbed in C(s,h,n)
alone when r is unrestricted. C has no r argument; with fixed s,h,n, label
width can grow without bound. This does not invalidate the final whole-trial
bound, and it is not an exponential-cost escape.

A precise replacement is:

> C bounds tensor arithmetic and access using positions within the retained
> list. Keep the original slot-label map separately. If labelled records are
> rescanned during recovery, add
> Lscan=O(s log(s+1)(n+log(r+1))). This term is absorbed by
> C(s,h,n)+O(r(n+log(r+1))), not necessarily by C alone.

To check absorption, the n term is below C. Set L=log_2(r+1). If L<=s,
s log(s+1)L=O(s^3), again below C. If L>s, then r+1>2^s and
s log(s+1)=O(r), so this part is O(rL). All s>=1 are covered by changing an
absolute constant. For s=0 no tensor/recovery scans occur. This establishes
the submission's final trial bound while correcting its intermediate claim.
Keeping labels static and using ordinal positions for subqueries is also
valid; no parameter occurrence may be deleted or deduplicated.

## 5. Every recovery branch, and a sequential scalar fallback

Let z_i be any residues, not necessarily elliptic values. If a node's product
is a unit modulo N, each factor is a unit: for every prime dividing N, no
leaf is divisible by that prime. Hence a gcd-1 node contains no useful leaf.
If its gcd is proper, exact divisibility verification returns a valid factor.
If its gcd is N and it is a singleton, the leaf is a genuine failure, not a
factor. Otherwise its two children are searched. A proper-gcd leaf cannot
be pruned by a gcd-1 ancestor. A proper-gcd ancestor has already succeeded.

Conversely, if every leaf gcd is either 1 or N, each leaf is either a unit or
zero in Z/NZ. A node product is consequently a unit if every leaf is a unit,
and zero if at least one is zero. It never has a proper gcd. Thus

    extraction succeeds <=> some i has 1<gcd(z_i,N)<N

for every composite N. This proof handles repeated prime powers directly.
Products of partially divisible leaves can saturate a parent to gcd N, but
such a leaf is already a proper-gcd leaf and the descent finds one. No prime
factorization is used by the algorithm or required to implement the proof.

For s>=1 a full binary tree has 2s-1 nodes and s leaves. A failed singleton
is never subdivided. Original order and multiplicity are retained; division
of one modular product by another is never used. Each queried sublist is
freshly initialized, so the cost includes its own f_1 through f_11, cache,
tensor construction and K traversal. Counting initialization only once would
be wrong; the submitted C includes it every time.

For the balanced tree let F(s)=sum_v16^(s_v). The base is F(1)=16<=2*16.
For s>=2, with a=floor(s/2), b=ceil(s/2), induction gives
F(s)<=16^s+2*16^a+2*16^b. Since 1<=a<=b<=s-1,
2*16^a+2*16^b<=4*16^(s-1)<=16^s. Hence F(s)<=2*16^s.
Multiplying by the nondecreasing factor M(n)+s(n+s) proves that all tensor
queries together fit C(s,h,n), plus the R2 scan term, O(sG(n)) gcd work,
and one final verification. In the full trial, s<=r absorbs those gcds into
its screening-sized gcd term.

Release a node's tensor and sort scratch before descending. The largest
query controls peak space. A stack of O(log(s+1)) interval descriptors uses
O(log^2(s+1)) bits; the original list/labels and any failure-record indices
are additional but within the stated list bounds. Copying the two contiguous
parameter sublists can be done by scans, with O(sn) total live slice storage
along a depth-first path. The empty root returns FAIL immediately.

The warning about a hypothetical additive oracle is essential. If every
nonempty query costs B+t with no retained shared data, summing B over
Theta(s) visited nodes can cost Theta(sB). The tensor's exponential geometric
sum proves nothing comparable for such an oracle.

**R3 — complete the scalar fallback's sequential recovery.** Lines 273–285
and 332–334 count arithmetic operations and stored nodes, but do not specify
how the tree is accessed. O(s) node visits alone is not a sequential bit-time
argument. The following explicit schedule preserves the bound (9) for a
fallback returning a verified proper factor or FAIL:

1. Process the retained parameters one at a time. Stream K for each, retaining
   only its two constant-size scalar windows while computing z_i; rewinding
   K costs O(h) per parameter. Store the final z_i in order. This costs
   O(shM(n)+s(n+log(s+1))) bit work, since M(n)>=n.
2. Pad to the next power-of-two number of leaves with units. There are fewer
   than 2s leaves and fewer than 4s nodes. Padding does not change any useful
   factor event. Build each level in order from consecutive pairs on the
   previous level, reducing every product modulo N. Retain the level files
   consecutively; their total length is O(s(n+log(s+1))). A fixed number of
   tapes suffices, reusing level buffers and appending completed levels.
3. Sequentially scan every stored node, compute its gcd, and retain a proper
   one if found. If left-first behavior is desired for this padded tree,
   retain the proper node of minimum preorder key. Keys consist of a binary
   root-to-node path and its length; prefix-first lexicographic comparison
   costs O(log(s+1)) per node. The earliest proper node cannot be below a
   unit ancestor, and any proper ancestor precedes it. Thus it equals the
   answer of pruned left-first search on that tree. Verify the selected
   divisor, or return FAIL if there was no proper node.

This may inspect more nodes than a stopping descent, but inspects only O(s)
nodes. No lookup jumps are used. The extra record traffic is
O(s(n+log(s+1))), not O(s) unbounded-address operations. Therefore products,
gcds and access cost O(s(M(n)+G(n)+n+log(s+1))). With the original raw labels
stored separately, (9) remains

    S(B)+O(rhM(n)+rG(n)+r(n+log(r+1))).

Its live space is O(s(n+log(s+1))+h+W(n)), plus any original raw-word/label
records retained by the driver. The O(r log r) label space cannot be replaced
by O(s log s) when original labels must remain live and r is unrestricted.
No probability statement changes: a tree has a proper node iff it has a
proper leaf, and the padded leaves are units. This is an on-paper execution
completion, not a run or a claim of novelty.

If the coordinator instead insists on the exact unpadded depth-first order
and its original stopping schedule, a conservative alternative is to construct
a preorder serialization bottom-up, copying each subtree at each merge level.
Every level moves O(s(n+log(s+1))) bits and there are O(log(s+1)) levels.
Then a single preorder scan implements pruning by skipping contiguous subtree
records. This gives the safe replacement bound

    S(B)+O(rhM(n)+rG(n)+r(n+log(r+1))log(r+1)).

Peak space stays O(r(n+log(r+1))+h+W(n)). The extra logarithm does not change
the later L_p comparison. Do not price unspecified pointer jumps as free;
adopt the explicit streaming schedule above to retain (9), or use this
conservative logarithmic correction. Both retain ordinary multiplicative
batch-size/scalar-length work.

## 6. Fixed tape, field interpretation and the exact useful law

**Domain completion to (10).** On the branch gcd(N,6)=1, define U and tau as
in the submission. An arbitrary composite divisible by 2 or 3 succeeds in
step 1 with probability 1, so (10) is not literally the whole-driver formula
on those inputs. The replacement is

    sigma_driver(N)=1,                         if gcd(N,6)>1;
    sigma_driver(N)=1-(1-tau_(N,B))^r,          if gcd(N,6)=1.

The composite promise makes the returned 2 or 3 proper. The exact rn-bit tape
is the sampler's tape on the second branch. A total-function specification may
also assign that tape to the first branch and leave it unused. No such early
branch requires paying tensor or K-setup costs.

For one raw word, there are exactly 2^n equiprobable possibilities. A useful
word is either a successful discriminant gcd, or a retained residue whose
final value has proper gcd. Values at least N and discriminant gcd N do not
qualify. If any discriminant success occurs, the driver succeeds even if it
halts before looking at later words. If none occurs, all retained slots are
processed, and the recovery equivalence makes success exactly the existence
of a useful retained word. Thus on the full raw tape success is precisely
the union of r independent copies of the same useful-word event. Repetitions
are allowed and there is no conditioning on having r distinct curves. This
proves (10), including every rejection and failed full-gcd leaf.

**Annihilation including characteristic dividing K.** For a nonsingular
short Weierstrass curve over a field of characteristic ell>3 and positive K,
the standard multiplication formula gives
x([K]P)=phi_K(x(P))/psi_K(P)^2 as rational functions. The numerator and
squared denominator, viewed as polynomials in x, are coprime. At an affine P,
psi_K(P)=0 therefore gives a pole of x composed with [K], exactly when
[K]P=O; when psi_K(P) is nonzero, both multiplication coordinates are finite.
Hence psi_K(P)=0 iff [K]P=O iff ord(P) divides K. Separability is not used.
These source facts hold for all positive K: Sutherland's 2021 Lecture 5,
Theorem 5.21, Lemma 5.24 and Theorem 5.25, explicitly distinguish inseparability
when ell divides K. The vanishing leading coefficient K is not evidence that
psi_K vanishes at every point. See the
[primary lecture PDF](https://ocw.mit.edu/courses/18-783-elliptic-curves-spring-2021/680a7686aabd24b22a15eeb96e733838_MIT18_783S21_notes5.pdf)
and its [frozen copy](W002-ecm-review-evidence/sutherland2021-lecture5.pdf).

The ring evaluator only divides by 2; it remains exact when gcd(K,N)>1.
The field argument is used componentwise solely on retained nonsingular
reductions. It does not grant an elliptic group or separable K-torsion
count over an arbitrary singular/composite ring.

For (11), let N=pq with distinct primes p,q>3. A cubic over F_ell has at
most three roots, so |D_ell|>=ell-3>0. Thus the conditioning denominators
in eta_p and eta_q are positive. Uniform a modulo pq gives independent,
uniform components. Conditioning both to be nonsingular gives the product
of the two uniform laws on D_p and D_q. The two successful singular events
are singular at p only and singular at q only; their probabilities are
(1-t_p)t_q and t_p(1-t_q). If both are nonsingular, the final gcd is proper
exactly when annihilation occurs at one component and not the other. Its
conditional probability is eta_p(1-eta_q)+(1-eta_p)eta_q. Multiplying by
t_p t_q and then by N/2^n proves (11).

Distinctness and squarefreeness are needed for that two-component formula.
For N=p^2, partial p-adic divisibility matters and no independent CRT pair
exists. For more factors, the productive event is different. The general
U-based formula still applies after screening. No assumption gcd(K,pq)=1,
independence of abstract curve orders, or uniform isomorphism classes is
needed for this exact calculation. The event is divisibility of the point
order by K, with all prime-power exponents, not merely B-smoothness of a
group order.

For independent repeated trials of a fixed law, a renewal equation gives
E[T_total]=E[T_trial]+(1-sigma)E[T_total], hence E[T_trial]/sigma when
sigma>0. Trial duration need not be independent of that trial's outcome.
If sigma=0, repetition cannot succeed. Capping at Q trials gives the stated
success and worst-case work upper bounds. Neither identity proves positive
useful mass. Exhaustive division after failure supplies only the known
O(sqrt(N)poly(n)) additional work, with the tensor cost still present.
A complete prime factorization also needs the usual primality/recursive
splitting wrapper; no new all-composite splitter bound is obtained here.

## 7. Conditional comparisons and their missing hypotheses

The minimizations are algebraically correct. Let Lambda=sqrt(log p log log p)
and fix b>0. Under the stipulated useful-word law,
B=exp((b+o(1))Lambda), h=Theta(B), and a choice
r=Theta(tau^(-1)) gives log r=(1/(2b)+o(1))Lambda and constant-order success.
The scalar full-cost envelope has leading exponent b+1/(2b), minimized at
b=1/sqrt(2) with value sqrt(2). A genuinely uniform additive evaluator with
paid extraction would instead have max(b,1/(2b)), minimized at the same b
with value 1/sqrt(2). These are conditional cost expressions, with the
polynomial factors in n retained, not successful factoring theorems.

**R4 — make the comparison quantifiers and batch scale precise.** Merely
matching log r=(1/(2b)+o(1))Lambda does not ensure constant success: the
unspecified error can make r tau tend to zero. The required statement is
r tau>=c>0 (and, for an inverse-scale comparison, r tau=O(1)). Then
1-(1-tau)^r>=1-exp(-c). Setting r=ceil(c/tau) illustrates the model but is
not an algorithm for discovering tau. Likewise p is not an input parameter
the factorer may know. A uniform, input-only parameter schedule and its
cost/success theorem would be separate work. None is provided.

Use p=min(p,q)->infinity and q>=p for the retained-slot argument, and require
r->infinity with r=exp(O(Lambda))=p^o(1). This is the regime relevant to the
stated inverse law for fixed positive b; arbitrary r denoted only by an
O(1) L-constant need not grow. Define I_j on the full pre-sampled tape as
1 exactly when word j is below N and nonsingular at both primes, whether
or not execution would later stop early. Then S*=sum_j I_j has binomial
law with

    rho=(N/2^n)t_p t_q >= (1/2)(1-3/p)(1-3/q).

For sufficiently large p this is at least 3/8. Chernoff's bound therefore
gives Pr(S*<r/4)<=exp(-c_0 r) for some absolute c_0>0. Let A be the event
of any early discriminant factor. A union bound gives
Pr(A)<=3r(1/p+1/q)=o(1). On A's complement the actual retained size is S*.
Consequently

    Pr(no early exit and actual s>=r/4)
      >=1-3r(1/p+1/q)-exp(-c_0 r)=1-o(1).

This proof never assumes that the stopped list itself consists of independent
slots. It shows that the expensive tensor allocation is reached with high
probability in this regime. It is not valid as a blanket claim with p an
arbitrary larger factor and the other prime fixed, or with bounded r.
It requires no order-distribution theorem beyond the independently specified
choice of the r scale.

Suggested replacement for lines 427–444:

> In this comparison only, assume the stated useful-word law uniformly and
> a batch size satisfying c<=r tau<=C for fixed positive constants. This is
> a model choice, not an executable N-only estimate of tau or a supplied p.
> Take p to be the least prime factor of the distinct semiprime, p->infinity.
> Then r->infinity and r=p^o(1). The full-tape retention count and the union
> bound on early discriminant exits give s>=r/4 without an early exit with
> probability 1-o(1). Thus this explicit tensor is exponentially costly in r.

Quasilinear M makes S(B) have B scale, up to logarithms. Scalar recovery's
possible conservative log r correction likewise does not change either
leading comparison constant. Polynomial factors in n must stay outside the
L_p expression unless a regime making their logarithms o(Lambda) is imposed.
The fixed driver B=n^2,r=n is a different parameter rule; these model
optimizations do not analyze its success or improve its worst-case bound.

The familiar small-factor ECM comparison is conjectural in Lenstra's original
abstract, visually checked at printed p.649. Coppersmith's printed pp.169–170
state the NFS exponent 1/3 and the heuristic nature of the probability model.
For balanced p,q, even the hypothetical additive ECM improvement retains
exponent 1/2 in N and does not beat that heuristic NFS exponent. No such
comparison is a rigorous complete-factoring result, and N^(1/6) would remain
exponential in binary input length.

## 8. Prior art and the saved-snapshot lifecycle correction

The primary Li passages support the submission's narrow prior-art claims:
Definition 3.1.1 supplies the recurrences; section 3.3 retains a short adjacent
window; Algorithm 4.1.1 uses batch gcd and binary splitting; sections 4.5–4.6
state ordinary evaluation and special-input cyclic costs. Theorem 4.6.2's
curve-count times log-scalar dependence is visible on printed p.49. Its
success analysis is not a theorem for this fixed raw-word family: the proof
of Theorem 4.1.3 explicitly assumes independent order-smoothness events.
No FFT precision or complete implementation claim is imported. The earlier
plus-case parity caveat is not repaired or reused by this tensor algorithm.
The source check is bounded; the report correctly makes no novelty claim for
a distributive tensor expansion.

**R5 — preserve history, correct the lifecycle attribution.** The constructor's
saved STATE has SHA-256
`c18ea42829aef215700161c2795fe6151285933c23b0a5c928f545ca1931eca8`.
It already says H027–H031 reviews are complete at lines 17–19 and gives the
completed H031 disposition at lines 51–61. It also retains stale statements
at line 204 and lines 590–591 saying the H031 review is live/unaccepted.
Thus that saved STATE is internally mixed; neither “wholly old” nor “wholly
updated” describes its bytes.

The saved W001 synthesis has SHA-256
`fb148d61e5f77f591a799bb3c670872a85165889a82f1aeb99b5eb2a72abace0`.
Its lines 77–84 record H031's reviewed acceptance/closure, and lines 151–152
say the reviews and coordinator updates are complete. The verifying snapshot
does not support the provenance limitation that STATE **and W001 synthesis**
“still refer to H031 as live.” The submission's lines 20–21 also overgeneralize
the source of the old wording. The saved Li note and H030 disposition have
older lifecycle references too; those are historical context, superseded by
the completed H031 disposition and the user's handoff.

The constructor's provenance gives snapshot_utc
2026-10-08T13:14:40.552980+00:00. It does not preserve a distinct earlier
version of synthesis establishing the alleged earlier live wording. This
review does not infer that no earlier read occurred; it distinguishes that
uncaptured possibility from the saved evidence.

Recommended clarification, in a later corrected report or coordinator
addendum, without changing the original provenance/delivery manifests:

> The verifying snapshots already contain H031's completed disposition.
> Saved STATE also retains stale live-review statements in older sections;
> saved W001 synthesis records completion. Any earlier synthesis version
> read before these snapshots is not separately preserved by this manifest.
> This report follows the completed H031 disposition and the explicit handoff.

The review-time current STATE and synthesis were separately frozen with hashes
`6d4817dfaa373463f2e32934a0a3d150d161483ee7e171444b22e4b2b1deb4f3`
and `34d430457dfd7b19c02b7059d81f70596d6e9f03440a210c616c04dcab556d8d`.
Their differences from the constructor's snapshots are not hash failures or
evidence of mathematical invalidity. Originals must remain untouched.

## 9. Acceptance boundary, open objections and execution record

The following recommendation is deliberately narrower than an unconditional
acceptance of every sentence in the submission:

- **Accept after local completion:** the finite scalar/tensor invariant on R1's
  domain, (6)–(8) with sequential cache access and R2's label accounting, and
  full-gcd recovery including nonsquarefree inputs and unsuccessful leaves.
- **Accept the scalar bound only with an access schedule:** R3 gives a sequential
  fallback realizing (9); the stricter original DFS alternative has the stated
  harmless logarithmic access correction. This is a proof completion, not a
  new batching result.
- **Accept the exact laws with their domains:** (10) is the post-small-factor
  branch, completed piecewise for the full driver; (11) is for distinct primes
  greater than 3 and includes characteristics dividing K. No positive useful
  probability follows.
- **Accept only conditional comparison algebra:** use R4's r tau condition,
  least-prime/asymptotic regime, full-tape early-exit argument and explicit
  unknown-parameter limitation. This is neither an implemented parameter
  schedule nor an ECM distribution theorem.
- **Correct provenance by addendum:** R5's saved-snapshot description replaces
  the overbroad lifecycle attribution. Preserve all original hashes.
- **Reject as a speedup:** the explicitly expanded tensor and the ordinary
  retained-factor/block implementations. Reject promotion to a new complete
  factoring bound or to a universal impossibility result for norms, compressed
  states, actual ECM parameter statistics, or factoring.

After these repairs there is no unresolved objection to the displayed finite
recurrence or the extraction equivalence. The unresolved positive-result
obligations are a materially smaller explicit state/transition with all
construction/access/recovery paid, a useful-success lower bound for the actual
family/tape law, an executable input-only parameter strategy, and the complete
all-input factoring reduction/cost. They are not discharged by this review.
The inherited status UNACCEPTED is not silently changed; the coordinator may
adopt these scoped recommendations and completions.

No numerical test or Lean work is proposed: neither would resolve the absent
algorithmic and distribution statements for this already-costly construction.
A reopening should begin with a materially different finite transition and
its extraction interface. There is no quota of new candidates.

The inspected inherited primary archives are directly available as
[Li 2006](W002-ecm-review-evidence/frozen/research/findings/W002-ecm-input-research--findings--ECM-priorart-li2006.pdf),
[Lenstra 1987](W002-ecm-review-evidence/frozen/research/findings/W002-ecm-source-lenstra1987.pdf),
and [Coppersmith 1993](W002-ecm-review-evidence/frozen/research/findings/W002-ecm-source-coppersmith1993.pdf).

Primary reading in this review was limited to Li printed pp.17–19, 23–24,
29–30, 33–35 and 45–49; Lenstra p.649; Coppersmith pp.169–170; and the 2021
Sutherland notes' multiplication-polynomial passages, principally pp.10–14.
Li p.17,45,49, Lenstra p.649, Coppersmith p.169–170 and Sutherland p.11,14
were visually inspected. Their whole PDF bytes, or pre-existing whole archives,
are preserved; no whole-document proof audit is asserted. The additional OCW
PDF hashes to
`35e4f2fc62ab6f1f30ee20afe4a7a6849d277fbde04909aea859251ed999dc68`.
The 2013 MIT version was a discovery read via the web tool; its returned
excerpt/metadata is archived, but direct PDF retrieval failed with HTTP 403.
The 2021 file is the additional mathematical source used above.

[Retrieval limitations](W002-ecm-review-evidence/retrieval-limitations.txt) record
that failure, an unused UPC endpoint failure, an abstract-only discovery lead,
and the Poppler warning on the OCW PDF. Rendered equations were legible.
All inherited primary-source hashes are in the freeze manifest; new-source
retrieval identity is in [new-sources.json](W002-ecm-review-evidence/new-sources.json).

Only reading, source retrieval/extraction/page inspection, symbolic reasoning,
archival copying, hashing and review/evidence writing occurred. No finite
mathematical experiment, parameter sweep, benchmark, factoring implementation,
Lean proof/invocation, package installation, recursive delegation, outside-project
write, commit, publication, scheduler, or shared-file modification was performed.
