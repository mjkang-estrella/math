# Fresh MathDB discovery shard 2 (algebra / number theory, ID ≡ 2 mod 3): retry report

Date: 2026-11-08 UTC. This is a retry after two rate-limit failures; no earlier output existed in this
lane. Scope: this directory only. No shared edits, commits, children, browser tabs, external messages
or submissions. Formalization is deferred to separate routing.

## 1. Outcome

| MathDB | Result | Status |
|---|---|---|
| **362111** | **Explicit counterexample n = 170** to Dolfi–Hafezieh–Spiga, J. Algebra 685 (2026), Conjecture 4.3 (arXiv:2402.19335 Conj. 1) | Complete ordinary proof with exact certificates. Candidate for root qualification review |
| 374432 | Necessity conjecture for the divisor-sum mod-4 congruence (Jirattikansakul et al. 2026) | Strongest open target. Partial mechanism; gap stated in §3 |
| 362288 | α(PSL₂(q)) = q for q ≡ 1 (mod 4) | Proved for q ≥ 9. Fails literally at q = 5. **Not claimed**: routine extension plus domain correction |

The count of credited outcomes is not changed by this report. Only the root can accept a result.

## 2. Candidate: MathDB 362111 refuted at n = 170

The full proof is in `362111-counterexample.md`. Exact check script: `verify_170.py`, output in
`verify_170.out.json`.

- **Literal statement.** If ℓ ≥ 3 distinct primes divide n and gcd(2ⁿ−1, n) = 1, then 2ⁿ−1 has at
  least 2^ℓ distinct prime divisors.
- **Counterexample.** n = 170 = 2·5·17 and gcd(2¹⁷⁰−1, 170) = 1. The factorization is
  2¹⁷⁰−1 = 3·11·31·43691·131071·9520972806333758431·26831423036065352611.
  That is exactly 7 < 8 distinct primes.
- **Certificates.**
  - Exact product check.
  - Small primes by trial division.
  - The two large primes by Pocklington–Lehmer with m−1 fully factored, using explicit witnesses.
  - Independently, deterministic 13-base Miller–Rabin.
  - FactorDB externally reports `FF` with the same seven factors.
- **Sharpness.** The authors' Lemma 4.2 lower bound 2^ℓ − 1 is attained for ℓ = 3. This answers their
  remark "we have no examples … except when ℓ ≤ 2".
- **Bounded uniqueness.** 170 is the only counterexample with n ≤ 10⁵ (`scan_ell3_100000.txt`, about
  12 minutes). Composite verdicts are rigorous MR witnesses. One caveat: perfect prime-power detection is
  skipped at 1000 bits or more.
- **Odd case open.** The authors' application (a putative 11-vertex graph) needs an odd n = q·t₁·t₂.
  That case is *not* settled. There is no odd counterexample with n ≤ 10⁵. The targeted screen over three
  Mersenne exponents is in `odd_pairs_60000.txt` (§5).

### Novelty, chronology and registry checks

- **Primary bodies read.** arXiv e-print TeX v1 (the only version), and the J. Algebra 685 (2026) 337–360
  version of record (open access, from boa.unimib.it). The conjecture text is unchanged in the VoR. The
  VoR adds that the conjecture is "compatible with" the Brillhart et al. tables. Those tables in fact
  contain the factors of 2⁸⁵ ± 1 that refute it.
- **MathDB live (2026-11-08T02:29Z).** 362111 is `open`, created 2026-08-11. solutions, model_attempts,
  human_solves, comments and replies are all empty.
- **Web search** (two queries, standard mode) found no public note connecting 2¹⁷⁰−1 to this conjecture.
- **Repository.** No file in the working tree or HEAD mentions 362111, 2402.19335 or Hafezieh, except
  coincidental hash substrings, which were inspected. No commit message mentions them either.
- **Chronology.** The factorizations of 2⁸⁵ ± 1 are classical Cunningham-table data (Brillhart et al.).
  They are background, not a prior refutation. The connection to the 2024/2026 conjecture appears new.
- **Not done.** The accepted-campaign public proof registries (Omega/OpenAI trees) were not re-pulled live
  for this record. A root prior-art audit should do that before acceptance.

### Significance: honest assessment for the root

What counts in favour:
- An exact, small counterexample to a conjecture stated in a 2026 J. Algebra paper.
- It shows that the authors' general bound is sharp.
- The AGENTS.md standard explicitly prefers small exact counterexamples.

What a reviewer may object to:
1. The counterexample can be read directly off classical factor tables.
2. The authors' motivating application concerns odd n, so a reviewer could call an even counterexample a
   "domain" technicality.

Against objection 2: the conjecture as stated, as published and as recorded on MathDB has no parity
hypothesis. The paragraph introducing it treats an arbitrary positive integer n. The adjudication is left
to the root.

## 3. Strongest open target: MathDB 374432

**Statement.** Let S(N) = Σ_{1≤k<√N} σ₀(N−k²). If S(An+B) ≡ 0 (mod 4) for every n ≥ 0, then
A ≡ 0 (mod 4) and B ≡ 2 (mod 4).

Source: arXiv:2604.25394, final conjecture. MathDB live: `open`, no solutions or attempts. The companion
record 374431 (sufficiency for N ≡ 6 mod 8) already has a public MathDB proof by Shivam Patel, dated
2026-08-20.

### Established in this lane, ordinary arguments

1. **Reduction.** It suffices to show that every AP {A′n + B′} with 4 | A′ and B′ ≢ 2 (mod 4) contains an
   N with S(N) ≢ 0 (mod 4). If 4 ∤ A, pass to the sub-progression n ≡ c (mod 4) for which Ac + B ≢ 2.
2. **Parity.** S(N) is odd if and only if N = 2k². The odd terms are the representations N = k² + j², and
   swapping k and j fixes only k = j. So any AP containing a number of the form 2k² fails.
3. **Character identity.** For an odd non-square m and any real character χ with χ(m) = 1,
   σ₀(m) ≡ Σ_{d|m} χ(d) (mod 4). This gives χ₋₄ for m ≡ 1 (mod 4), χ₋₈ for m ≡ 3 (mod 8), and χ₈ for
   m ≡ 7 (mod 8). The last one is indefinite, which is the obstruction.
4. **Scaling identity, odd N.**
   S(4N) ≡ S(N) + 2·#{l ≥ 1 : odd part of N−l² is a square} + 2·r₂(N)/4 (mod 4).
   The j-odd terms reduce, through χ₋₈ and a swap involution, to the representations 2N = j² + y².
   Numerically, S(4N) ≡ S(N) for N ≡ 5, 7 (mod 8).
5. **Empirical.** Every violating AP with A ≤ 1000 has a failing N ≤ 2·10⁵. The worst case is
   (A, B) = (594, 210), first failing at N = 50700 = 12·65².

### Gap, not paid

Within a residue class, S(p) mod 4 for primes p is roughly equidistributed (data mod 16). Some APs, such as
N = 12M with M ≡ 67 (mod 99), fail only at square-rich N. So a full proof needs control of a
class-group-level (Chebotarev or 4-rank type) invariant on every AP, or a construction with special
factorizations. Neither has been found. Next concrete step: derive S(N) mod 4 for N = g·m² families, using
the χ-identities and the swap involution.

## 4. Other screened records (compact)

There are 30 literal records with ID ≡ 2 (mod 3). Each was selected only if it had no mention in any
MathDB-context repository file. Dispositions and statement SHA-256 values are in `literal-records.json`.

- **Excluded as publicly resolved:**
  - 372149: He–Zhang arXiv:2512.17195.
  - 373310: de Weger's live page states both parts as theorems (with Monticone). It also follows from
    Monier's formula; our derivation agrees, and was checked numerically to 3·10⁵.
  - 374120: Cui–Tang arXiv:2604.08839.
  - 374837: the MathDB statement itself says it has been proved.
- **Probable resolution, not verified:** 353195.
- **Defective record:** 362918 (empty formula placeholder).
- **Infeasible:** 362564, 373547.
- **Source read, no mechanism found:** 375404 (Sun, zero-sum, arXiv:2606.18234v5).
- **Not attempted:** the rest.

This is a selection screen, not exhaustive coverage of the lane.

## 5. Bounded odd-case screen (362111)

`odd_pairs.py` covers odd Mersenne exponents p < q with pq ≤ 60000. It flags pairs whose Φ_pq(2) is a
base-3 strong probable prime; composite verdicts are rigorous. An odd ℓ = 3 counterexample needs a
triangle of flagged pairs.

The run stopped at its 1200 s cap after pair (61, 127): 104 pairs decided, 8 pairs with pq ≤ 60000 left
undecided. The flagged (probable-prime) pairs are (3,5), (3,31), (5,13), (5,17) and (7,19). No triple is
fully flagged. Ten triples with product ≤ 10⁷ survive only because some of their pairs are undecided or
out of range, for example (7,19,9689) and (89,107,127). Details are in `odd_pairs_60000.summary.txt`.

**The odd case remains open.** No exhaustion is claimed.

## 6. Files and hashes

`SHA256SUMS` covers every file this lane wrote. Downloaded sources are under `sources/`: arXiv
abstract/e-print, the VoR PDF and text, MathDB live JSON, the de Weger page and the FactorDB response.
Each is kept once; nothing is copied recursively.
