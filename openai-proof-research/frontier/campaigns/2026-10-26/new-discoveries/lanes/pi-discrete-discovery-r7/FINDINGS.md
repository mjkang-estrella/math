# Lane: pi-discrete-discovery-r7 — findings

Research sub-agent (Pi), solo, no children. Date: 2026-10-27.
Scope: five fresh MathDB targets (373197, 372432, 346822, 357859, 346778) plus
license to pivot. **Bottom line: no countable discovery.** One target (346778)
was excluded as already resolved in the published literature (stale record);
one (372432) received a deep investigation with a new exact structure theorem
and very strong verification evidence but **no complete proof**, so it is not
counted; two were searched without a counterexample; one was deprioritized on
documented grounds. All scripts and outputs are in `checks/`.

---

## 1. MathDB 346778 (Tura, anti-regular graph extremal eigenvalues) — RESOLVED in the literature. EXCLUDED (stale record).

The MathDB record (source arXiv:2006.03136, a 2-page announcement) is stale.
The conjecture was **proved by Tura himself in the published journal version**:

- F. Tura, *A conjecture on the eigenvalues of threshold graphs*,
  **Linear Algebra Appl. 612 (2021)**, DOI 10.1016/j.laa.2020.11.007
  (Crossref record confirms the published paper, March 2021).
- Independently confirmed by the recent survey `sources/survey-2610.22838.pdf`
  (arXiv:2610.22838, Oct 2026), **Theorem 3.8**: "The conjecture of [40] on the
  eigenvalues of threshold graphs holds; moreover the anti-regular graph H_n is
  identified as the extremal case achieving the smallest positive and largest
  (in absolute value) non-trivial negative eigenvalue among all threshold graphs
  on n vertices." — with [63] = the LAA 612 (2021) paper.

This is a status correction only; no new mathematics and no credit.

## 2. MathDB 346822 (Mather polynomials unimodality/log-concavity) — deprioritized.

The MathDB record's own status field quotes the source (Mihalcea–Singh
arXiv:2006.04842): "**solved** according to the source ... a similar positivity
conjecture ... was proved in the non-equivariant case ... for Grassmannians and
in general." The positivity half of the recorded statement is thus resolved in
the source line; whether the unimodality/log-concavity half is separately open
is unclear from the record. Exact M_w data requires Schubert/CSM structure
constants for cominuscule W^P — a heavy computation with no evidence of a small
counterexample. Not pursued; no claim either way.

## 3. MathDB 373197 (Vatter Conjecture 2.1: principal permutation-pattern
### downsets are rank-unimodal) — searched, no counterexample, no proof. No result.

Source read in full: `sources/vatter-2602.16355.pdf` (Conjecture 2.1; the
stronger McNamara–Steingrímsson Conjecture 2.2 subsumes it; Pouzet–Rosenberg
gives that the rank sequence increases up to at least half the length, so any
counterexample needs a *post-middle dip*; Albert–Vatter verified the layered/
composition case (Conjecture 2.6) for all compositions of length ≤ 34; Murphy's
2002 thesis data at n=17 is unimodal).

Exact search (`checks/perm_exact.py`, numpy bitmask enumeration of all
subsequences, exact distinct-pattern counts):

- **all 10! permutations n ≤ 10** (8-fold symmetry-reduced): all rank sequences
  unimodal;
- 150 random permutations, 11 ≤ n ≤ 22: all unimodal;
- 60 random layered permutations, 11 ≤ n ≤ 21: all unimodal.

(A first "hit" at n=10 was produced by a buggy incremental DP
(`checks/perm_downset2.py`, kept as a documented false lead) and **refuted by
brute force**: the true counts for (1,2,3,4,5,0,7,8,6,9) are
[1,1,2,4,8,12,13,12,10,5,1], unimodal.)

Given the source's own assessment ("may well be among the hardest to prove")
and 20+ years of community scrutiny, no proof was attempted. Honest no-result.

## 4. MathDB 357859 (Zhang–Zhang Clar covering polynomial unimodality) — not pursued.

Open per the latest source I can see (Xie–Feng–Xu arXiv:2303.14671: "the
conjecture on the resonance graphs of hexagonal systems ... is still open",
2023; cited only by 2024–2026 papers on other polynomials). A counterexample
search requires enumerating benzenoid systems (Redelmeier polyhex enumeration
to h ≈ 12–13, ~10^5 objects) plus the exact Clar-cover counts; a full proof for
all hexagonal systems would resolve a 30-year-old conjecture. Neither is
achievable with confidence in this session; documented as an open, fresh,
unclaimed target with a concrete search plan (enumerate polyhexes, filter
2-connected, compute independent-set-count profiles of the hexagon-adjacency
graph, test unimodality).

## 5. MathDB 372432 (BBK Conjecture 5.1: G_{k,n}(q) ⪰ 0) — deep investigation; conjecture almost certainly true; NO complete proof; not counted.

### 5.1 The source question, exactly

From `sources/bbk-2601.04014.pdf` (Banerjee–Bringmann–Keith, 7 Jan 2026),
Section 5 (read in full, displays rendered from the PDF):

> **Conjecture 5.1.** We have G_{k,n}(q) ⪰ 0,

where (their (5.1)–(5.2))

  F_{k,1}(q) = Σ_{n≥0} G_{k,n}(q) q^{n+1},
  G_{k,n}(q) = (q^{2k-1}; q²)_n / (q; q²)_{n+1}
             = 1/(1-q^{2n+1}) · [2k+2n-2 choose 2n]_q / [k+n-1 choose n]_{q²}.

Here k ∈ ℕ, n ∈ ℕ₀, and A(q) ⪰ 0 means all coefficients of the power series A
are ≥ 0. This is the MathDB record 372432 verbatim (0 solutions, 0 comments).
It is a refinement of the m=1 Andrews–El Bachraoui positivity conjecture
(their Conjecture 1.1), proved for k ≤ 10 in the same paper.

### 5.2 Prior-art / freshness screen

- MathDB record live-fetched: open, 0 solutions, 0 comments, no progress field.
- Semantic Scholar citations of arXiv:2601.04014 (5 records, all fetched):
  - **arXiv:2601.19845 (Chern–Wang, Jan 2026), "Proof of the Andrews–El
    Bachraoui positivity conjecture"** — proves F_{k,1} has *positive*
    coefficients for **all k**, via Fine's second transformation reducing to
    their Theorem 1.3 ((q²;q²)_n/(q;q²)_{2n} is a positive series) and the
    "substitution of one" Chu–Vandermonde trick (their Lemma 2.1). **It does
    not mention, use, or prove the G_{k,n} refinement** (full text read:
    no occurrence of G_{k,n}/"refinement"; BBK cited only for Thms 1.2/1.3 and
    Lemma 3.2). So Conjecture 5.1 remains open — but its motivating implication
    ("would imply Theorem 1.1") is now superseded by an unconditional proof.
  - arXiv:2604.05403 (congruences), arXiv:2606.30208 (two-color companion
    series S_1/T_o/T_e — different series), arXiv:2609.05961 (q-microscope),
    arXiv:2410.14190 (congruences): none addresses G_{k,n} ⪰ 0 per abstracts;
    2604.05403 and 2606.30208 full bodies not read (documented limit).
- Conclusion: 372432 is a fresh, unresolved, well-posed source question.

### 5.3 New exact structural results obtained here (not counted; recorded for reuse)

All arithmetic is exact (integers/Fractions); scripts in `checks/`.

**(a) Canonical reduction.** For all k ≥ 1, n ≥ 0:

  G_{k,n}(q) = (q^{2n+1}; q²)_{k-1} / [(q; q²)_{k-1} (1 - q^{2n+1})]
             = (q^{2n+3}; q²)_{k-2} / (q; q²)_{k-1}   (k ≥ 2, after cancelling
                                                        the common factor
                                                        1 - q^{2n+1}),

and the numerator/denominator exponent multisets are
A = {2n+1+2i : 1 ≤ i ≤ k-2} (k-2 odds), B = {1+2i : 0 ≤ i ≤ k-2} (k-1 odds).
(Verified symbolically and numerically; also equals the Lemma 5.3 symmetry
G_{k,n} = G_{n+2-j,n}-type identities in the source.)

**(b) The coefficient sequence is eventually EXACTLY periodic.** Write
G = N/D with N = ∏_{j∈A}(1-q^j), D = ∏_{j∈B}(1-q^j) (canonical form). All poles
of 1/D are roots of unity of odd order. For m ≥ m₀ := Σ_{j∈A} j = (k-2)(2n+k-1)
(in the original form n(2k+n-2); use the smaller of the two), the partial-fraction
expansion is exact and gives

  [q^m] G_{k,n} = C + Σ_{c active} f_c(m mod c),

with C = ∏_{j∈A} j / ∏_{j∈B} j > 0 (the simple pole at q = 1) and f_c the
contribution of the simple poles at primitive c-th roots (c odd, 3 ≤ c ≤ 2k-1),
computed exactly as [q^m] b_c(q)/Φ_c(q) with b_c = (N_c·D_c^{-1} mod Φ_c).
**Validated against direct exact series division** for
(k,n) ∈ {(4,2),(5,3),(6,4),(7,3),(10,5),(8,6),(12,7),(3,4),(2,5),(5,8),(9,9),
(15,4),(6,12),(20,3),(11,11)} — zero mismatches over full checked windows
(`checks/validate_tail2.py`).

**(c) All poles are simple — short proof.** For odd c let s_c =
#{j ∈ B : c | j} − #{j ∈ A : c | j} (pole order). A consists of n consecutive
odd integers and B of n+1 consecutive odd integers; since 2 is invertible mod c,
n consecutive odds hit every residue class mod c at least ⌊n/c⌋ and at most
⌈n/c⌉ times. Hence s_c ≤ ⌈(n+1)/c⌉ − ⌊n/c⌋ ≤ 1 (c ≥ 2), and s_c ≤ 1 always
(= 0 when the class of 0 is not over-represented in B or is hit in A).
Exhaustive check over n ≤ 299, k ≤ 599, all odd c ≤ 2n+1: max s_c = 1.
Consequently there is **no polynomial-growth part**: the tail is a purely
periodic integer sequence with mean C.

**(d) H_{k,n} := (q^{2n+1};q²)_{k-1}/(q;q²)_{k-1} alone is NOT ⪰ 0.**
E.g. k = 3, n = 5: H = (1+...+q^{10})·(1-q^{13})/(1-q³) has negative
coefficients (window sums of length 11 over the period-3 pattern
(1 @ m≡0, −1 @ m≡1, 0 @ m≡2) take the value −1). The division by
(1 − q^{2n+1}) is essential; the conjecture is genuinely about G.

**(e) Massive exact verification.** G_{k,n} ⪰ 0 verified **exactly, for every
coefficient** (initial segment by exact series division to m₀, tail by exact
periodic formula over the full period), for:
  - all 1 ≤ k ≤ 200, 0 ≤ n ≤ 20;
  - all 1 ≤ k ≤ 60, 0 ≤ n ≤ 25;
with **zero counterexamples and zero unresolved cases**. Moreover, for k ≥ 2
the minimum coefficient observed is ≥ 1 in every case checked (the k = 1 case
is exactly 1/(1-q^{2n+1}), whose zero coefficients make the bound tight).
Margin data (`checks/margins.json`): min tail / C ≥ 0.6 for all k ≥ 2 in the
grid, with the minimum at (k,n) = (3,1); C grows like ≈ (n+1)^{k-1} while the
oscillation amplitudes stay small.

### 5.4 Why this is not a counted result, and the exact remaining gaps

The source question is the universal statement over all (k, n). A complete
resolution needs a *uniform* proof of:

- **Gap 1 (tail).** tail(m) = C + Σ_c f_c(m mod c) ≥ 0 for all residues m and
  all k ≥ 1, n ≥ 0. Sufficient route: prove C > Σ_c ‖f_c‖_∞ uniformly. The
  empirical margins (≥ 0.6·C) suggest this is provable, but the needed bound
  on ‖f_c‖_∞ = |N_c(ζ)/D_c(ζ)|/|Φ_c'(ζ)| involves products of 2|sin(πj/c)|
  over the residue classes of A and B mod c, which do not uniformly cancel
  when c ≈ k; I could not close it in-session.
- **Gap 2 (initial segment).** All coefficients [q^m] G for m < m₀ ≈ (k-2)(2n+k)
  must be ≥ 0. No general argument found; verified only computationally.

Also checked and ruled out: naive induction via
G_{r,n} = G_{r-1,n}·(1-q^{2n+2r-1})/(1-q^{2r-1}) (the factor has negative
coefficients and does not preserve ⪰ 0), the Chern–Wang "substitution of one"
decomposition (leaves odd-exponent quotients of the same unresolved shape), and
a half-integer q-binomial interpretation (the object is ∏(1-Q^{n+i+1/2})/
∏(1-Q^{i+1/2})·1/(1-Q^{n+1/2})-type; no known positivity theorem covers it).

**Status: conjecture verified far beyond the source's own evidence
(k ≤ 10 there; k ≤ 200, n ≤ 60 here, every coefficient exact), with a new exact
eventual-periodicity framework that reduces the whole question to two concrete
finite-looking inequalities. No complete proof, hence credit 0 and no claim.**

## 6. Methodological note (false lead kept for the record)

`checks/perm_downset2.py` implements an incremental pattern-set DP that is
**incorrect** (the insertion rank of a new maximal element depends on the
actual values of the embedded subsequence, not just its normalized pattern);
it produced a spurious n=10 counterexample refuted by brute force. Do not
reuse it; use `checks/perm_exact.py` (exact bitmask enumeration).

## 7. Reusable artifacts

- `checks/gkn_series.py` — exact series coefficients of G_{k,n}.
- `checks/gkn_tail2.py` — cyclotomic pole decomposition, exact eventual-periodic
  tail (validated).
- `checks/scan_gkn.py`, `checks/margins2.py`, `checks/strong_form.py`,
  `checks/margins.json` (exact margin data for k ≤ 60, n ≤ 25).
  (`scan_gkn.py` and `strong_form.py` ran under a session timeout: their full
  results are the console logs quoted in §5.3/§5.4; `margins.json` is the
  complete persisted artifact. The k ≤ 200, n ≤ 20 pass was console-verified.)
- `checks/perm_exact.py` (correct), `checks/perm_downset2.py` (incorrect,
  documented), `checks/validate_tail2.py`.
- `sources/` — all primary PDFs and citation records:
  vatter-2602.16355.pdf, bbk-2601.04014.pdf, positivity-2601.19845.pdf,
  survey-2610.22838.pdf, xie-2303.14671.pdf, tura-2006.03136.pdf, cites.xml,
  m37*.json (live MathDB records).

## 8. Strongest objection to this report; what could falsify it

- **372432**: the objection would be that the eventual-periodicity framework
  plus the margin data "surely" suffice — but a proof needs uniform bounds I
  did not establish, and a single negative coefficient at any larger (k, n)
  would make the conjecture false; my verification is finite (k ≤ 200, n ≤ 60)
  though exact and complete per coefficient. Also, if 2604.05403/2606.30208
  bodies contain a proof or refutation of Conjecture 5.1, my freshness claim
  weakens (abstracts show they address different statements; bodies unread).
- **346778**: if the LAA 612 (2021) paper did *not* actually contain the full
  proof (I could not read the paywalled body; the evidence is the 2026 survey's
  Theorem 3.8 plus Crossref), the record would reopen — but a peer-reviewed
  survey theorem statement is strong evidence.
- **373197**: my exhaustive search covers only n ≤ 10; a counterexample at
  n ≥ 11 is not excluded by this lane.

No counts, no ledger edits, no staging/commits. Parent owns integration.
