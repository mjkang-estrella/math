# Full-scope target, unresolved

## Source and exact quantifiers

Robert Heffernan and Des MacHale, *The genesis of a conjecture in number theory*, Irish Mathematical Society Bulletin 93, Summer 2024, pp.39–41, DOI 10.33232/BIMS.0093.39.41. Actual publisher-linked PDF:
https://www.irishmathsoc.org/bull93/wef/Articles/Heffernan/Heffernan-wef.pdf

Conjecture 1 on p39 says: for EVERY positive integer n, if the ordinary unrestricted integer partition number p(n) divides n!, then

    n ∈ S={1,2,3,7,9,10,11,12,14,15,16,17,18,19,20,21,24,28,32,33,39}.

There is no bound on n, primality restriction, exceptional density-zero set or assumption about p(n)'s factorization. A single n outside S with literal integer divisibility refutes the whole assertion. Proving the assertion needs every n outside S. The phrase natural number is read in its explicit positive-integer setting; introducing n=0 is neither research nor an admissible endpoint correction.

All three pages were text-read in full, including the nearby theorem statements, the source's solved Problems 1–2, and p41's discussion. The journal index expressly links the wef PDF; two guessed alternative paths returned 404, preserved. No claim that some other journal revision was obtained. Source received 17 January 2024, revised 3 May 2024. No later correction or same-object author follow-up was found in bounded searches and the retrieved MTU departmental article page; that page is not a complete author bibliography.

## Early duplicate/classical screen

Before downloading the target PDF, exact title/DOI/author aliases and claim aliases were queried in original report roles. `history-receipt.json` reuses r137's retained r133-derived SHA/path records, refreshes original named SUMMARY/discovery/PROOF/review/DECISION files, and records 1692 path bodies and four new/changed paths. No 400k inventory was rebuilt. Original r111–r113 are in the queried records; their SUMMARY dispositions were also explicitly read. Queries read full bodies, without a match cutoff. This is lexical report coverage, not all-source semantic coverage.

Inherited alias paths include several replay/packet copies, candidly recorded rather than silently called distinct scientific originals. A broad partition/factorial regex hit the original structural-r233 REVIEW: its precise passage concerns derivatives of partitions of unity and factorial Gevrey bounds, not p(n). The exact title/author/DOI/source-ID pass has zero such hits. On extending aliases to Cilleruelo for the closest literature, t164f99's original public review was reopened in full: its Cilleruelo references concern finite-field sum/product colorings and routine characteristic transport, not partition-number factorization. Scratch control copies are echoes, not new dispositions. The mutated scratch review is not used as original science.

Two pools were dropped before source retrieval: the CN-energy query matched original sol-fresh-probability-algebra-r12/discovery.md, which identifies explicit same-source public proofs of the old CN conjectures; common-transversal aliases matched r115 and factorial-product reviews, already screened. Their original reports were reopened/retained, with no new work on their questions. Initial concatenated console reads of several long historical reports were clipped; clipped excerpts are NOT full-body semantic evidence. Hash/body query coverage is separately recorded and does not imply every matched long review was fully intellectually audited. The target's exact aliases do not depend on those clipped reads. No old reject is reversed.

## Current primary follow-ups and chronology

The complete current OEIS A046668 body was read and retained (entry revision #56, 6 July 2026). It retains the same 21 values and cites the 2024 article. It records bounds >30000 (Deutsch 2005), >350000 (Corneth 4 July 2018), >2000000 (Kotesovec 6 July 2018). Its code credit includes Wilson 23 November 2004. These dated credits are the oldest public indications observed here, not an assertion that the current fetched body existed in 2004. The exact finite-list conjecture is explicitly printed in 2024. No creation date or priority has been invented.

The 23 June 2026 Flynn-Connolly comment says finiteness would follow if A192885 has only finitely many negative terms; it does not prove that hypothesis or the exact cutoff 39. Full A192885 body (revision #34, 30 June 2026) records Sondow's stronger observation P(p(n))>n for n>39, checked there through 2500. Its author credit dates to 16 August 2011. This stronger assertion is conjectural; it is sufficient, not equivalent to the source assertion. An n with P(p(n))<=n may still fail divisibility because a prime exponent exceeds its factorial valuation.

Closest actual theorem: Cilleruelo–Luca, *On the largest prime factor of the partition function of n*, Acta Arithmetica 156.1 (2012), 29–38, DOI 10.4064/aa156-1-4. Actual complete publisher PDF retained from
https://www.impan.pl/shop/en/publication/transaction/download/product/82357
All ten extracted pages, including the entire section 3 proof, were read. Theorem 1 asserts P(p(n))>log log n on a set of asymptotic density one. The proof uses Rademacher approximation, a short interval with K~sqrt(log x) smooth values, pigeonhole coefficients, Matveev for a nonzero logarithmic form, and a Taylor/Vandermonde argument when that form vanishes. It neither asserts the n-scale bound nor removes all exceptional integers. The aggregate Schinzel–Wirsing bound cited in its introduction likewise does not bound each individual value. The 1987 original body was not independently obtained/read, and is not promoted to a complete subsumption screen.

Both attempted UAM author-copy downloads failed normal TLS verification; no insecure option was used. The legitimate publisher copy succeeds. Search located a different author-copy URL, but its full bytes were not obtained and no byte/statement identity with the journal is asserted. Search-rendered first-page author material has a different MSC listing. No substantive version difference is inferred from that. The journal article is received 27 July 2011, revised 31 January 2012. Its similar-titled single-author Luca reference is a different, weaker paper; they are not conflated.

DLMF27.14 actual generating-product, Euler recurrence, Hardy–Ramanujan asymptotic and congruence statements were read. They give standard tools, not a divisibility resolution. All new source URLs, observation UTCs, byte lengths and hashes are in http.jsonl. Search-result snippets were leads, never full-body clearance. No current public proof of this exact conjecture was located; absence is not established.

## Mathematical route actually attempted

For each prime q, exact divisibility is equivalent to

    v_q(p(n)) <= Σ_{j>=1} floor(n/q^j).

Every q>n dividing p(n) is an immediate obstruction. Small-prime congruences usually prove the wrong inequality: divisibility by q does not say its exponent exceeds the very large valuation in n!. A largest-prime-factor upper bound <=n also does not establish divisibility without the exponent checks.

The following routine estimate clarifies where the route stalls; it is NOT a proposed discovery. From the literal generating product, for t>0,

    log Σ_m p(m)e^(-tm)
      = Σ_{j>=1} 1/[j(e^(tj)-1)]
      <= (1/t) Σ_{j>=1} 1/j² < 2/t.

All terms are nonnegative; finite truncations and monotone limits justify rearrangement. Bounding a single coefficient and optimizing t=sqrt(2/n) gives

    log p(n) < 2 sqrt(2n).

Put s=sqrt(n)>=64. For every prime 2<=q<=s,

    v_q(n!) log q >= (n/q-1)log q > 2sqrt(2n).

Here h(q)=(n/q-1)log q decreases for q>=3, so its minimum over 3<=q<=s is h(s)=(s-1)log s. Since log s>3 and 3(1-1/64)>2sqrt2, this is enough. For q=2 use log2>=1/2 and log s<=s/8 for s>=64: h(2)>=s²/4-1/2>=s²/8>=h(s). The log bound follows at64 from log64<6<8 and from derivative 1/s<=1/8 afterward. Thus no q<=sqrt(n) can have an excessive exponent in p(n) for n>=4096. In particular a sqrt(n)-smooth p(n) would divide n! at such an n.

This does not provide such a smooth value or exclude one. It reduces the obstruction to prime powers at primes q>sqrt(n). For sqrt(n)<q<=n, the factorial exponent is floor(n/q); for q>n it is zero. The remaining universal statement is therefore: for every n outside S with n>=4096, some q>sqrt(n) divides p(n) to exponent greater than floor(n/q). That statement has NOT been proved. A finite exact witness with no such obstruction would refute the source, but none was found.

Trying to transplant the closest density-one linear-forms proof does not close this. Its very small allowed smoothness threshold pr<=log log x is essential in the comparison with Matveev's exponential dependence on the number of logarithms. Allowing primes all the way to n introduces roughly pi(n) logarithms. The resulting bound does not contradict the Rademacher error. Moreover its density estimate explicitly allows exceptional isolated n, whereas the source needs none beyond39. No new uniform argument handles those exceptions. This is a route failure, not a refutation of either paper.

Growth alone cannot force a prime obstruction: 2^floor(sqrt(n)) divides n! for every n>=4 (v2(n!)>=floor(n/2)>=floor(sqrt(n))). This exponential-in-sqrt(n) sequence has entirely small factors. It does not have the exact partition asymptotic, and is used only to block an order-of-growth shortcut, not as a counterexample about p(n). The actual recurrence offers no multiplicative propagation that would transport a single exclusion to all later n. No such propagation lemma has been proved.

## Exact checks, strongest objection and falsifier

checks.py independently computes 5001 partition values by generating-product DP and Euler's recurrence, checks exact factorial remainder against the complete prime-valuation criterion for n=1..5000, verifies the known list S, and checks small-prime and smooth-growth controls. No prime factorization oracle or floating-point certificate is used. The residual after stripping every prime<=n is an exact integer; if >1 it has a prime divisor>n by unique factorization. This does NOT identify that prime, and is not represented as a full factorization.

These checks do not extend the already reported two-million search, do not certify its correctness independently, and cannot establish universal exclusion. They validate the implementation and route, with no separate mathematical credit. The first 2000-value run is superseded by the 5000-value control; no scientific conclusion relies on search scale.

Strongest objection: the only established deductions are classical reductions and finite controls; the full prime-power obstruction for every remaining n is absent. Exact falsifier of the original conjecture: an explicit positive n not in S and an exact computation/proof of p(n)|n!. Exact falsifier of the small-prime estimate: n>=4096 and a prime q<=sqrt(n) with v_q(p(n))>v_q(n!). Exact clearance needed for a proof route: a genuine all-n obstruction theorem with all exceptional n resolved. Neither density-one nor an empirical cutoff supplies it.

## Fixed registry refresh and remaining gates

One HEAD observation at 23:40:02UTC on 29 October gives Omega a19a578cd06b57a4ea4d287cb0df92f9085117ae (commit23:34:23UTC), and unchanged OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. The fixed aa026→a19a response contains six of six commits, correct merge base and zero behind, but exactly300 paths. `caps_ok=false`: path coverage is capped, not complete. Visible sphere-topology paths do not clear unseen paths. We do not chase the moving head or rebuild unchanged inventories. r137's qualified 8a9f→aa026 and r136/r133's older bounded receipts are retained by reference and hash, without extending their semantic scope to this target.

No candidate-specific complete current registry-body screen was completed. Registry novelty is HOLD; a head observation is not clearance. Because no full ordinary resolution exists here, no investment request, Lean, paper, new review, acceptance or count change follows. A future complete proof/refutation would still need current target-specific proof-body screening, classical/substantive adjudication and independent investment clearance before major formal or manuscript work. Zero nominees is the final outcome of this lane.
