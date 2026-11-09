# W019-B torsion-cancellation review

Review date: 2026-10-08 America/Los_Angeles (evidence timestamps 2026-10-09 UTC).
Role: independent review child, scope W019 section B only. The parent remains
principal researcher. Sections A and C are reviewed separately.
Verified new end-to-end factoring improvement: **NONE**. The parent claims none.

The [exact brief](W019-torsion-cancellation-review-evidence/brief.txt), frozen inputs,
primary-source copies, read scope, and the single preregistered certificate run are in
the [evidence directory](W019-torsion-cancellation-review-evidence/). The submitted
W019.md has SHA-256 `afea2b58f83e36801e8630bfac5ed787f29801c4f589914aeaa04fb29e6f40df`.

## Decisions

1. **Accepted:** the order-reduction step (B1), termination in at most s cancellations,
   and a polynomial group-operation bound. The exact bound is at most m(m+5)/2
   squarings and products, where 2^m = max(ord A, ord B). This is O(s^2), as the
   parent stated.
2. **Corrected:** the criterion. With the swap rule the procedure returns a useful
   involution **iff <A,B> is noncyclic**. W019's sentence "if no useful involution
   occurs, the original B is in <A>" is true only without a swap. After a swap the
   failure case is A ∈ <B>.
3. **Rejected as stated:** "probability at least one half per fresh uniform sample,
   regardless of the relative sizes of invariant factors." A counterexample family
   (proved below and checked exhaustively) gives success probability 2^-k in
   C2 x C_(2^k). Even the natural "pivot = previous chain that hit J" model gives
   0.45 < 1/2 in C2 x C4.
   **Correct replacements:** (a) if the pivot has maximal order in G_2, the success
   probability is exactly 1 - 1/[G_2:<A>] >= 1/2. (b) From any pivot, keeping the
   larger-order element after each failure gives success within two fresh uniform
   samples with probability >= 1/4, and at most 4 expected samples.
4. **Accepted with a sharper statement:** odd-part projection by an individual,
   genuinely verified annihilator cannot bias the outcome. The outcome depends only on
   the cyclic subgroup <g_2>, and that is the same for every odd exponent. Bias enters
   through how g itself is produced, through conditioning on whether an annihilator was
   found, or through samples that are not fresh relative to the pivot.
5. **Proved (the interface):** for an odd squarefree semiprime N = pq with N ≡ 1 mod 4
   and D = -4N, C(D)[2] ≅ C2 x C2. Its reduced ambiguous forms are exactly four, and
   every nontrivial ambiguous class other than J = [(2,2,(N+1)/2)] gives p or q.
   For N ≡ 3 mod 4 and D = -N, C(D)[2] ≅ C2 and its single nontrivial class splits N.
   **The 2-Sylow subgroup is therefore cyclic, so cancellation is unnecessary in the
   N ≡ 3 mod 4 case.**
6. **Prior art:** this is already implemented. Schoof's Algorithm 6.4 (1982) runs the
   same process for N ≡ 1 mod 4 with D = -3N and the known involution (3,3,(N+3)/4).
   Sutherland's p-group basis algorithm (Lemma 4 / Algorithm 4, arXiv:0809.3413) is
   the general form, and it starts from an element of maximal order. That is exactly
   the condition W019 omits. No novelty or asymptotic gain is established, and the
   exponent stays at the GRH-conditional N^(1/5+eps) of the interval-search stage.

The certificate passed all 11 preregistered assertions in one run. It was not tuned,
not rerun, and nothing failed: 4,454 of the 20,000 budgeted events, 0.02 s.
It is a finite consistency check of the hand proofs below. It is not a performance
or class-group-distribution claim.

## 1. The abstract procedure

G is a finite abelian 2-group, written multiplicatively. A has exact order 2^s with
s >= 1, J = A^(2^(s-1)) is known, and B has order 2^t. "Useful" means an element of
G[2] \ {1, J}.

**Procedure.** If B = 1, return FAIL. Compute t and Z = B^(2^(t-1)) by repeated
squaring. If Z ≠ J, return Z. If t > s, swap the roles of A and B. The old A also has
top involution J, so J is unchanged. Repeat until termination:
B <- B * A^(-2^(s-t)). If B = 1, return FAIL. Otherwise recompute t and Z, and return
Z if Z ≠ J.

**Lemma 1 (order drop).** Let t <= s and top(B) = J. Then C = A^(2^(s-t)) has order
2^t and top C^(2^(t-1)) = A^(2^(s-1)) = J. Since G is abelian and J^2 = 1,
(B C^(-1))^(2^(t-1)) = J J^(-1) = 1, so ord(B C^(-1)) divides 2^(t-1).
After a swap the condition t <= s holds, so t strictly decreases at each cancellation.
That gives at most s cancellations, with s the pivot's exponent after any swap.

**Theorem 2 (criterion).** The output is useful iff H = <A,B> is noncyclic.
*Proof.* Every intermediate element lies in H, so every Z examined lies in H[2].
If H is cyclic, H[2] = {1, J}, so the procedure can never return a useful element.
Since t strictly decreases, it must end in FAIL. Conversely, a cyclic group's
exponent equals its order and is the larger of ord A and ord B. So H is cyclic iff
the smaller-order element Q lies in the cyclic group <P> of the larger-order element.
The pivot after any swap is P. If the run ends with B = 1, then Q · P^(-c) = 1 for
the accumulated exponent c, so Q ∈ <P> and H is cyclic. If the run returns Z, then Z
is an involution, nonidentity by construction and ≠ J by the test. ∎

So W019's "B ∈ <A>" is the no-swap special case. The certificate's assertion I2
checks the iff against brute-force span enumeration for every pair in seven groups
of order at most 16.

**Cost.** Let m = max(s,t). Building the table of A^(2^i) costs s squarings. B's
initial order costs t squarings. Each cancellation costs one product plus at most
t_i squarings, with t_i distinct and at most m-1. The total is at most
2m + m + m(m-1)/2 = m(m+5)/2. The certificate (I3) never exceeded this.
In a class group, inversion of (a,b,c) is (a,-b,c), which is free. Equality with J
is tested on unique reduced representatives, so each step costs one composition plus
reduction. Since s <= log2 h = O(log N), the procedure is polynomial in log N.
Faster discrete-log versions are known (Teske, O(n^2); cyclic O(n lg n); Sutherland
O(n lg n / lg lg n), cited from Sutherland's introduction, pp. 1-2). They are
irrelevant here because this stage is not the bottleneck.

## 2. Success probability: the W019 claim and its repair

W019's argument covers only the failure event B ∈ <A>, which has probability
1/[G:<A>] <= 1/2. Once the swap is allowed, failure is the larger event "B lies in
some cyclic subgroup containing A". A union of cyclic subgroups containing A can
cover almost all of G.

**Counterexample (proved; certificate I5).** Take G = C2 x C_(2^k) = <x> x <y>,
with J = y^(2^(k-1)) and pivot A = J (s = 1). Every element of order >= 4 has top J,
so it swaps and contains J, and the run fails. Of the order-<=2 elements, 1 and J
fail and x, xJ succeed. The success probability is 2/2^(k+1) = 2^-k. The naive chain
has the same 2^-k here, so the cancellation gains nothing with this pivot. The
certificate confirms the count of exactly 2 successes for k = 1..5.

**A more realistic pivot also fails the bound (reported, not asserted).** Let A be
uniform among elements whose top involution is J. This models a previous chain that
hit J. One fresh uniform B then succeeds with probability 0.45 in C2 x C4
(J = (0,2)) and 0.4712 in C2 x C8 (J = (0,4)). The naive chain gives 0.25 and 0.125
there, so the cancellation genuinely helps, but it does not reach 1/2.

**Theorem 3 (repairs).** Let G be noncyclic, with exponent 2^e.
(a) If ord A = 2^e, then no swap occurs and P[success] = 1 - 1/[G:<A>] >= 1/2.
Equality with the formula is checked in I4.
(b) Upgrade rule: after a failure, replace the pivot by whichever of {A, B} has
larger order. They generate the same cyclic group. The elements of order 2^e are the
complement of the proper subgroup G[2^(e-1)], so they have density >= 1/2. With
probability >= 1/2, the first sample either succeeds or installs a maximal-order
pivot, and then (a) applies. Hence P[success within 2 samples] >= 1/4. The certificate
(I6) found a minimum of 0.5156 over all pivots in the five noncyclic groups. The
expected number of samples is at most 2 (to reach a maximal-order pivot) plus 2.

Sutherland's Algorithm 4 begins by choosing an element of maximal order, for the same
reason: his Lemma 4 needs |β| <= p^m (pp. 12-13).

## 3. Individual annihilators and selection bias

Suppose a sample g comes with an annihilator m = 2^a u (u odd) that has been verified
by g^m = 1. Write ord g = 2^b w with w odd. Then w | u, and g^u = g_2^u.
Since u is odd, <g^u> = <g_2>.
By Theorem 2 the cancellation outcome depends only on <A> and <B>. **So the choice of
odd part, even an adversarial choice that depends on g, cannot change the outcome.**
Separate annihilators per sample suffice. No common exponent or class number is needed.

What can bias the result, and must be proved or paid for:

- **The law of g.** Theorem 3 needs g_2 uniform in G_2, which holds when g is uniform
  in G. Products of small split-prime forms with exponents from a bounded range have
  an unproved law. If exponents are uniform modulo a known multiple of the exponent
  of G (for example h, once known), the image is exactly uniform on <S>. This is
  because (Z/h)^r -> G is a surjective homomorphism when <S> = G. Generation by small
  primes is Schoof's Corollary 6.2, which is GRH-conditional.
- **Subgroup coverage.** If every sample lies in a subgroup K with K_2 cyclic, success
  is impossible. This is the 2-group analogue of W017's C2 x C3 example.
- **Selection on annihilator discovery.** If an interval search may miss h, keeping
  only samples whose order has a multiple in the searched interval conditions on
  ord(g). That correlates with ord(g_2), and the uniform bound no longer applies.
- **Freshness.** B must be independent of <A>. A power of the pivot's own sample, or
  a product supported on the same primes, is not fresh.

There is also a deterministic alternative that needs no uniformity, and it is the one
Schoof uses. If S generates G, the 2-parts of S generate G_2. Run the cyclic pivot
process over all s ∈ S, starting from H = <J>. If every step stayed cyclic, the final
cyclic H would contain every s_2 and hence all of G_2. So when G_2 is noncyclic,
success is guaranteed, at the cost of one annihilator per generator.

## 4. The quadratic-form interface

These are primitive positive definite forms (a,b,c) with b^2 - 4ac = D, reduced in the
usual sense: |b| <= a <= c, and b >= 0 if |b| = a or a = c. Each class has a unique
reduced form. This standard uniqueness theorem is the only external input in this
section.

**Lemma 4 (shapes).** A reduced f lies in a class of order <= 2 iff b = 0, b = a, or
a = c. *Proof.* f^(-1) = (a,-b,c). If 0 < |b| < a < c, that form is reduced and
different from f, so f is not ambiguous. If b = a, then (a,-a,c) ~ (a,a,c), and if
a = c, then (a,-b,a) ~ (a,b,a). If b = 0, f equals its inverse. ∎
Schoof p.265 lists the same shapes and the factorizations D = a(a-4c),
D = (b+2a)(b-2a), D = -4ac.

Let N = pq with odd primes p < q. Note q ≠ 3p, so the two subcases below are
exhaustive and disjoint.

**Case N ≡ 1 mod 4, D = -4N (fundamental, b even).** Solving each shape:
- b = 0 gives ac = N: (1,0,N) is principal, and (p,0,q).
- b = a = 2a' gives N = a'(2c - a'). a' = 1 gives J = (2,2,(N+1)/2), which is primitive
  exactly because (N+1)/2 is odd. a' = p gives (2p,2p,(p+q)/2), which is reduced iff
  q > 3p. It is primitive because p ≡ q mod 4 makes (p+q)/2 odd.
- a = c gives N = (a - b/2)(a + b/2). The divisor 1 would need N <= 3. Divisor p gives
  ((p+q)/2, q-p, (p+q)/2), which is reduced iff q < 3p. Any common prime factor would
  divide 2p and 2q, and (p+q)/2 is odd, so it is primitive.

Exactly four reduced ambiguous forms, so C[2] ≅ C2 x C2 and G_2 always has 2-rank 2.
Extraction gives a = p, a/2 = p, or a - b/2 = p. Note that gcd(a,N) = 1 for the a = c
form, so a ± b/2 is required there. **Every nontrivial ambiguous class except J
splits N.**

**Case N ≡ 3 mod 4, D = -N (fundamental, b odd).** b = 0 is impossible.
- b = a gives N = a(4c - a). a = 1 is the principal form (1,1,(N+1)/4). a = p gives
  (p,p,(p+q)/4), with p+q ≡ 0 mod 4, reduced iff q > 3p.
- a = c gives N = (2a - b)(2a + b). Divisor p gives ((p+q)/4, (q-p)/2, (p+q)/4),
  reduced iff q < 3p. It is primitive because a common factor 2 would make q even.

Exactly two forms, so C[2] ≅ C2 and **G_2 is cyclic and nontrivial**. Every element
of even order yields the unique nontrivial involution, which splits N via a = p or
2a - b = p. A uniform g has P[g_2 ≠ 1] = 1 - 1/|G_2| >= 1/2. The cancellation is not
needed in this case, and its noncyclicity hypothesis cannot hold. This matches the
N ≡ 3 mod 4 branch of Schoof's Step 3.

**Certificate II1-II5.** For all 73 odd semiprimes 15 <= N < 400 (35 with
N ≡ 1 mod 4), the reduced forms were enumerated and each was squared by Arndt
composition and reduced. The ambiguous set equals the closed-form prediction above,
the counts are 4 and 2, and the extraction rule gives d = 1 exactly on the principal
form and J and gives p or q otherwise. This checks the derivation. It is not a proof
beyond those N.

**Scope limits.** The interface is proved only for squarefree odd N = pq, p ≠ q.
Squarefreeness of an unknown N cannot be verified cheaply. For N = p^2 q, D = -4N is
not fundamental and the primitive class group of that order needs its own extraction
argument. Perfect squares and even N are trivial to remove. For prime N the useful set
is empty in both cases, so FAIL is the correct outcome there. My own sketch, not
certified: the same enumeration for squarefree N with r prime factors gives one
ambiguous form per divisor pair {d, N/d} of each type, and only d = 1 (principal, and
J in case 1) is trivial. A complete splitter must still handle all composites, as
docs/SPECIFICATION.md requires.

## 5. Prior art

- **Schoof 1982, Algorithm 6.4 (printed p.271, read from page image).** For
  N ≡ 1 mod 4 it uses D = -3N with H initialized to {(1,1,(1-D)/4), (3,3,(N+3)/4)} (printed as (1,1,1-Δ/4), (3,3,N+3/4)).
  For each small split prime p it adjoins a generator of the 2-primary part of <f>.
  When H becomes noncyclic, the three involutions of H other than (3,3,(N+3)/4) give
  the factorization. W019-B is this process in pivot form, with 2 in place of 3. Using
  D = -4N avoids Schoof's 3 ∤ N condition and needs nothing new. Schoof's generator
  set and correctness rest on GRH (Corollary 6.2), and his cost is O(N^(1/5+eps)).
- **Sutherland, arXiv:0809.3413v3, section 4.** Lemma 4 and Algorithm 4 extend a basis
  by γ = β α^(-x), with x from an extended discrete log, starting from a
  maximal-order element. (B1) is the bit-serial greedy instance for a one-element
  basis α = (A), stopping at the first new involution instead of building a full
  basis. Pohlig-Hellman and Teske are the antecedents Sutherland cites (p.2).
- Schnorr-Lenstra 1984 was not audited for this point (see read scope).

## 6. What this saves, and what would change total cost

Saved work: no interval-search annihilator is wasted because its chain hit J. With a
maximal-order pivot and uniform samples, the expected number of annihilated samples
is O(1) (at most 4). The naive repeated-chain baseline is not the right comparator:
Schoof's deterministic H process already needs at most c1 log^2|D| annihilator
searches under GRH. The cancellation changes at most this polylogarithmic sample
count. Each sample still needs its own annihilator, which costs one
N^(1/5+eps)-scale interval search unless something below supplies it. **Total
factoring exponent: unchanged. End-to-end improvement: NONE.**

Ingredients that could change total cost, none of which is supplied:

1. **Amortized annihilators.** If one interval search certifies that it found the only
   annihilator of g1 in an interval known to contain h, that annihilator is h. Every
   later sample is then annihilated for free. With uniform exponents mod h over a
   generating set and a maximal-order pivot, extraction after ONE search costs
   expected polylog(N). This is still N^(1/5) overall, but it removes the per-sample
   search. It needs an argument that uniqueness actually occurs, for example ord(g1)
   larger than the interval width, which no current result guarantees for every N.
2. **A sub-N^(1/5) source of a single annihilator**, or of any element whose 2-part
   lies outside <J>. Only this would change the exponent. Ambiguous classes encode
   the factorization (Schoof p.265), so this cannot come from 2-group bookkeeping.
3. **An unconditional generation or uniform-sampling theorem** to replace GRH. This
   would change the theorem's status, not the exponent.

Cheapest decisive next step, if the parent pursues item 1: state the uniqueness event
precisely, then bound its probability or construct a family of N on which it fails.
No further abstract-group check is useful. Theorems 2 and 3 settle that layer.

## Evidence index

- `preregistration.md`, `certificate.py`, `preregistered-manifest.json` (frozen hashes)
- `run-record.json` (one run, exit 0), `certificate-output.json`, empty `certificate-stderr.txt`
- `read-scope.md`, `brief.txt`, `inputs/`, `sources/`
- `delivery-manifest.json` hashes every payload, including this report.
