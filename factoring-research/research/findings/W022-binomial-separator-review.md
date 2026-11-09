# W022 B — central-binomial Frobenius-multiplicity separator: review

**Disposition: symbolic claim accepted and its scope widened; the computational
proposal is rejected as an acquisition route. No verified algorithmic improvement.**
Every identity in W022 B is correct. Correctness does not depend on q<2p. The only
exact condition is the base-p carry condition the parent stated. A Kummer proof
gives a cleaner, stronger statement that also covers non-semiprime N≡3 (mod 4).
But I found no primary source and no construction that computes
C((N−3)/2,(N−3)/4) mod N without first exposing a factor by an existing paid
mechanism. Every known general method falls into one of three cases:
(a) it manipulates a Θ(N)-bit integer;
(b) it is a holonomic baby-step/giant-step method whose unit hypotheses fail at
index min(p,q), so it reduces to Strassen's factorial-gcd search;
(c) it achieves polylog(N) by using Frobenius in a *known* prime characteristic,
which is circular here.
Any oracle for this residue, or just its gcd with N, factors a large semiprime
family in one gcd. So a fast method would be a factoring result of the same
strength. I do not claim hardness: no lower bound is known or asserted.

Ownership: this report and [its evidence directory](W022-binomial-separator-review-evidence/)
only. I made no delegation, installation, commit, or shared solver/Lean/STATE/registry/task
edit. Section A has a separate review and is not assessed here.

## Frozen scope and provenance

- [brief.txt](W022-binomial-separator-review-evidence/brief.txt) has SHA-256
  `92fe555bd32a97b8bbb85ae3843fe23dce72ffacbe79315ba23b3704fa31b171`.
- [input-freeze.json](W022-binomial-separator-review-evidence/input-freeze.json)
  hashes and snapshots `inputs/` for AGENTS.md, RESEARCH_TEAM.md, RESEARCH_LOOP.md,
  README.md, docs/SPECIFICATION.md (all read in full) and W022.md. W022.md was
  read in full; only lines 132–178 (section B) are reviewed. Its hash is
  `46af485d802c5303f8eb920d7691519c74a9fbc68beea41eeae49cd0567a2d67`. The live
  file was unchanged when this report was written. The section B excerpt is
  `W022-section-B.txt`, with hash `7c04b257…9e3850`.
- STATE.md and the W021 reviews were not read. The brief says the B review does
  not depend on them.
- Sources, retrieval failures and exact read scopes are listed in
  [source-read-scope.json](W022-binomial-separator-review-evidence/source-read-scope.json).
  Downloaded PDFs are untrusted data. The only processing run on them was `pdftotext`.

## 1. Symbolic verification

Notation: N=pq with distinct odd primes p≡3 and q≡1 (mod 4); n=(N−1)/2=2m+1.

**Integer identities (accepted).** H_n(−1) is the x^n coefficient of
(1−x)^n(1+x)^n=(1−x²)^n, so it is 0 for odd n. To get the derivative, use
jC(n,j)=nC(n−1,j−1):

  H_n′(−1) = n·Σ_k (−1)^k C(n−1,k)C(n,n−1−k) = n·[x^{2m}](1−x²)^{2m}(1+x) = (−1)^m n C(2m,m).

Since 2n≡−1 (mod N), n is a unit modulo N. Therefore gcd(H_n′(−1),N)=gcd(C(2m,m),N).

**Lucas route (accepted, with one clarification).** Termwise Lucas gives
H_n(X)≡H_{n mod ℓ}(X)·H_{⌊n/ℓ⌋}(X^ℓ) (mod ℓ) for any prime ℓ. This holds even
when ⌊n/ℓ⌋≥ℓ, because the second factor is still a polynomial in X^ℓ.

- **Mod p:** n mod p=(p−1)/2 is odd and ⌊n/p⌋=(q−1)/2 is even. The first
  factor has derivative (−1)^{m₀}((p−1)/2)C((p−3)/2,(p−3)/4) at −1, which is
  nonzero mod p because every entry is below p. Igusa-type simplicity is not
  needed. The second factor's value at −1 is ±C((q−1)/2,(q−1)/4). It is nonzero
  mod p iff p does not divide that binomial, and q<2p is sufficient for this.
- **Mod q:** ⌊n/q⌋=(p−1)/2 is odd, so H_{(p−1)/2}(−1)=0 exactly. The derivative
  of the X^q factor is 0 mod q. So q divides H_n′(−1).

**Kummer/Lucas route on C(2m,m) directly. This is the stronger statement.** Let
ℓ be any prime dividing any N≡3 (mod 4). The low base-ℓ digit of 2m is (ℓ−3)/2.

- ℓ≡1 (mod 4): the low digit of m is (3ℓ−3)/4>(ℓ−3)/2. That forces a carry,
  so **ℓ always divides C(2m,m)**. This holds for every N≡3 (mod 4), with no
  size condition.
- ℓ≡3 (mod 4): the low digit of m is (ℓ−3)/4 and causes no carry. Lucas gives
  C(2m,m)≡C((ℓ−3)/2,(ℓ−3)/4)·C((c−1)/2,(c−1)/4) (mod ℓ), with c=N/ℓ≡1 (mod 4).
  So **ℓ divides C(2m,m) iff ℓ divides C((c−1)/2,(c−1)/4)**, i.e. iff adding
  (c−1)/4 to itself in base ℓ produces a carry.

**Accepted and repaired scopes:**

1. Every semiprime N≡3 (mod 4) automatically has one factor in each residue
   class, so the stated family is exactly "semiprimes N≡3 mod 4". For them,
   gcd(C(2m,m),N)∈{q,N}. It equals q exactly when p∤C((q−1)/2,(q−1)/4).
2. Within this family, q<2p is equivalent to (q−1)/2<p, because q=2p+1 is
   impossible mod 4. It is sufficient, not necessary. For example N=39, 203 and
   979 (all with q>2p) give q. It covers **every** case where the 1-mod-4 factor
   is the smaller one, including tiny q, which trial division finds anyway.
   "Close semiprimes" undersells the family. The relevant asymmetry is the
   residue class, not balance.
3. p=3 is fine: (p−3)/2=0. For N=15, C(6,3)=20 and the gcd is 5. Labels need
   not be ordered: N=35 and 323 both give q.
4. For general N≡3 (mod 4), the selector reveals the product of all ≡1 (mod 4)
   primes together with every ≡3 (mod 4) prime that has the carry. It can still
   be nontrivial when every prime is ≡3 (mod 4): N=231 gives 3. It can also be
   the full N: N=75 and 195.
5. **N≡1 (mod 4) controls:** (N−3)/4 is not an integer, so the selector is
   undefined. The natural analog C((N−1)/2,(N−1)/4) reverses the roles: ≡3
   (mod 4) primes always divide it, and ≡1 (mod 4) primes divide it under the
   carry condition. Blum N gives N, and balanced 1·1 pairs give 1. The construction
   therefore separates exactly the mixed-class semiprimes. It is not an all-input
   splitter, and the brief's negative controls behave as predicted.

## 2. Preregistered certificate (single execution)

The protocol, case list, predictions P1–P5 and code were frozen before execution:
[protocol.json](W022-binomial-separator-review-evidence/protocol.json),
[certificate.py](W022-binomial-separator-review-evidence/certificate.py),
[certificate-freeze.json](W022-binomial-separator-review-evidence/certificate-freeze.json).
It ran once, with no reruns or tuning. Raw output is in
[certificate-result.json](W022-binomial-separator-review-evidence/certificate-result.json)
and [execution-log.txt](W022-binomial-separator-review-evidence/execution-log.txt).
The [postflight-audit.json](W022-binomial-separator-review-evidence/postflight-audit.json)
recheck confirms the freeze hashes match.

- 26/26 cases completed, using 11,335 charged events out of the 20,000 cap. The
  run was not capped and took 0.011 s.
- **P1:** all 16 p≡3, q≡1 semiprimes gave the predicted gcd. All 9 close cases
  gave q (N=15…11663). Among the 7 unbalanced cases, 3 gave q and 4 gave the
  full N: 87, 183, 791 and 19171.
- **P2:** the exact integer checks H_n(−1)=0 and H_n′(−1)=(−1)^m n C(2m,m) passed
  for all 9 cases with N≤700.
- **P3:** termwise Lucas, for both primes, had 0 mismatches in the 8 cases with
  N≤400. In all 16 cases the derivative mod p equalled the Lucas-factor product
  and the derivative mod q was 0.
- **P4/P5:** all 6 N≡1 (mod 4) controls and all 4 non-semiprime N≡3 (mod 4)
  cases matched the per-prime predictions.

Caveats: factor labels were used only by the verifier. The selector line itself
used only N. `math.comb` was an exact oracle here, with outputs up to 9,578
bits. The central coefficient has about N/2 bits, so this is exponential in
log N and has **no** speed meaning. Finite checks support, but do not replace,
the proofs in §1.

## 3. Prior art (primary sources only where retrieved)

- **No exact match found** for gcd(C((N−3)/2,(N−3)/4),N) as a factor separator.
  This is not a novelty claim. The search was bounded, and secondary hits
  (competitive-programming pages, an unverified 2026 ePrint) are not authorities.
  The standard composite-modulus binomial algorithms all factor the modulus
  first and then apply Lucas/Granville plus CRT.
- **Factorial-gcd factoring is classical and is the governing analogy.** Costa–Harvey
  (arXiv:1201.2116, lines 28–45) present Strassen's method: for p<q, gcd(⌊√N⌋! mod N,N)=p.
  Bostan–Gaudry–Schost (SIAM J. Comput. 2007; preprint lines 75–90, 130–170,
  745–800) give O(M_int(N^{1/4} log N)) for it. Harvey (arXiv:2010.05450, Thm 1.1)
  gives the current deterministic bound N^{1/5+o(1)}. W022 B is a *different
  index and coefficient* with the same "gcd of a huge holonomic quantity" shape.
- **Holonomic N-th terms over a ring** (Chudnovsky–Chudnovsky; BGS Thm 8 and
  Lemmas 1–2) cost Õ(√index) ring operations. They require 2,…,⌈√index⌉ and
  further shifted values to be **units**. BGS's own factoring application
  (Lemma 12) exists to locate the non-unit. There is no unit-free variant at
  polylog cost.
- **Polylog-cost coefficient extraction exists only in known characteristic.**
  Bostan–Christol–Dumas (arXiv:1602.00545, abstract) compute the N-th coefficient
  of an algebraic series over F_p in O(log N) operations, with cost quasi-linear
  in p. In characteristic zero the best they cite is quasi-linear in √N. C(2m,m)
  is the m-th coefficient of (1−4x)^{−1/2}, an algebraic series. The log N method
  rests on Christol/Frobenius at a specified p, which is exactly the Lucas
  computation the brief forbids as an algorithm.
- **Shamir (1979; MIT/LCS/TM-91, not retrieved, bibliographic only)** factors in
  O(log n) *arithmetic* steps by allowing operands of exponential size. Search
  snippets say the memo itself disclaims polynomial bit complexity. That is the
  precise precedent for "representation of a binomial ≠ cheap extraction".
- **Hasse/CM interpretation (background, analogy only).** E: y²=x³−x has CM by
  Z[i]. For ℓ≡3 (mod 4), x³−x is odd and −1 is a non-residue, so #E(F_ℓ)=ℓ+1
  and E is supersingular. For ℓ≡1 (mod 4) the Hasse coefficient is
  ±C((ℓ−1)/2,(ℓ−1)/4)≡±2a (Gauss; Chowla–Dwork–Evans 1986, abstract only). The
  W022 index couples these local invariants across two primes. Composite-ring
  point counting is known to be factoring-equivalent (Kunihiro–Koyama 1998,
  bibliographic only; wording of hypotheses unverified). Drinfeld/Hasse methods
  for factoring polynomials over finite fields are an analogy only, not a
  transfer theorem. I found no source turning either into an integer-factoring
  extraction at this index.

## 4. Actual acquisition cost of C(2m,m) mod N (no factors supplied)

| Route | Cost | Why it fails or what it reduces to |
|---|---|---|
| Exact integer (binary splitting / prime-swing) then reduce mod N | Θ̃(N) bit ops; output ≈N/2 bits | Exponential in log N, worse than trial division's √N |
| Fraction-free (2m)!/(m!)² mod N | — | (2m)! and m! are both ≡0 mod N once m≥max(p,q) (true for N≥15), so 0/0 |
| Keep (2m)! and (m!)² modulo N^e so the p-parts survive | e ≥ v_p((2m)!) ≈ q/2, i.e. Θ(√N)-fold modulus for balanced N | Operands of Θ(N^{1/2}·log N) bits per step, over ~N steps |
| Ratio recurrence B_{k+1}=B_k·2(2k+1)/(k+1), naive | m≈N/4 steps | Division by k+1=min(p,q) is a non-unit, so the method reveals a factor at step ≈min(p,q) (trial division) |
| Same recurrence, Chudnovsky/BGS BSGS to index m | Õ(N^{1/2}) ring ops, and the unit hypotheses fail | Detecting the failing block is Strassen/BGS Lemma 12: Õ(N^{1/4}), or N^{1/5} by Harvey. The binomial value is never reached before a factor is exposed |
| Coefficient of (1+x)^{2m} / CT of (x+2+1/x)^m via powering | Degree-m dense object: Θ̃(N) | Reducing mod a small cyclic modulus aliases away the multiplicity (the W021 C failure mode) |
| Christol/Lucas O(log N) extraction | polylog N **in F_p** | Requires p: circular |

This settles the parent's question. In each route the denominator obstruction
is not incidental. Over Z/NZ every route either keeps exact Θ(N)-bit data, or
it must divide by multiples of p and q. The first such division is itself a
factor witness, and it occurs at an index no larger than min(p,q). Within
recurrence-based methods, then, the binomial adds nothing beyond the
factorial-gcd search that already finds the smaller factor first. That search
costs Õ(N^{1/4}) by Strassen/BGS and N^{1/5+o(1)} by Harvey. This is a statement
about these method classes, not a lower bound for all algorithms.

Circularity: the gcd-oracle for this index is polynomially equivalent to
factoring mixed-class semiprimes with q<2p. The residue gives the factor in one
gcd. Conversely the factorization determines the gcd (=q) trivially, although
the full residue mod p may still need a C(a,b) mod p computation with a,b<p.
So the separator is a re-encoding of the target. It becomes a factoring
mechanism only together with a new coefficient-extraction algorithm. **The
missing computation, stated exactly:** a uniform procedure that, given only N,
outputs C((N−3)/2,(N−3)/4) mod N, or any multiple of it coprime to the unknown
p, in time below the relevant factoring baseline. It must not invert any element
of Z/NZ that might be a non-unit, and must not use Frobenius at an unknown prime.
I found no candidate for this.

## 5. One materially different, paid attack — priced, and why it is not new

The binomial is a *P-recursive* coefficient: it separates the primes
deterministically but costs √index. The cheap alternative is the *group* side of
the same CM curve, which uses constant-coefficient doubling. Take E: y²=x³−x
over Z/NZ with N≡3 (mod 4), and compute [k]P by an x-only ladder in O(log k)
ring operations. Watch for a non-invertible denominator, as in ECM. Modulo the
supersingular p, #E(F_p)=p+1. Modulo q the order is q+1−a_q.

- With k=N+1 this is Gordon's CM elliptic pseudoprime test (Math. Comp. 1989;
  bibliographic only, not retrieved). Because N+1≡1−q (mod p+1), it splits N
  only through group-order coincidences.
- With k=lcm(1..B) it splits N when ord_p(P) is B-smooth. Since the group mod p
  has order p+1, this is **exactly a Williams p+1 / fixed-curve ECM step**.

The cost is polylog N times B·log B, fully paid and well known. It does not
recover the Hasse/multiplicity separation, whose deterministic content lives in
the non-group coefficient. So it is a decisive, cheap way to see the trade-off:
group structure makes extraction cheap but brings smoothness requirements, while
the multiplicity coefficient is deterministic but has no cheap extraction. A
genuinely new route would need an object with both properties. An example would
be a constant-coefficient recurrence over a small Z/NZ-algebra whose N-th term
encodes a Hasse invariant without aliasing. No such object is known to me.

## Summary for the parent

- **Accepted:** the identities, the Lucas and Kummer proofs, gcd∈{q,N} for all
  semiprimes N≡3 (mod 4), the exact condition p∤C((q−1)/2,(q−1)/4), and q<2p as
  sufficient. These are supported by a frozen certificate with all 26 cases
  correct.
- **Repaired:** "close semiprimes" becomes "mixed-class semiprimes; the size
  condition matters only when the 1-mod-4 factor exceeds twice the other". Also
  added: the per-prime rule for every N≡3 (mod 4), and the role reversal for
  N≡1 (mod 4).
- **Rejected:** any reading of this as an acquisition route. Every known
  computation of the residue is exponential, circular, or reduces to
  factorial-gcd search, which already reveals min(p,q).
- **Verified improvement: NONE.** Next decisive step, if the line is pursued: write
  down a candidate unit-free extraction for a single holonomic coefficient at
  index ≈N, and test whether it implicitly divides by k≤min(p,q). The cheap
  falsifier is to instrument any proposed scheme for non-unit inversions.
