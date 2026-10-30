# Preliminary adversarial review — parent-hermite-bound (MathDB 346243)

Reviewer: pi-hermite-preliminary-review lane (solo, no children, standard speed).
Date: 2026-10-27. Scope: preliminary source / math / novelty / substantive-eligibility
review only. NO formal PASS, NO manuscript PASS, NO count/acceptance/packet decision.

## Verdict summary

| Gate | Result |
|---|---|
| G1 Source literalness | **PASS** |
| G2 Mathematical correctness | **PASS** |
| G3 Substantive eligibility (not an immediate known corollary) | **PASS** |
| G4 Prior-art / novelty screen | **PASS with documented limits** |
| G5 Freeze / provenance integrity | **PASS** |
| G6 Formal checkpoint | not claimed (inspected only) |

**Independent substantive decision: the candidate is substantively ELIGIBLE for
investment in a discovery packet.** The proposed argument is a complete and
correct proof of the literal Guo–Liu Conjecture 1 (arXiv:2004.10441 Eq. (30)
p.10; Commun. Theor. Phys. 73 (2021) 075002, Eq. (29) p.8; MathDB 346243,
status open), the source question is **not** an immediate corollary of known
results (verified quantitatively, not just asserted), and no published
resolution was found. Residual novelty risk is documented in §7 and is
commensurate with a *preliminary* review; a final review must widen the
citation-graph and registry reach before acceptance.

## 1. Freeze and provenance (G5)

* All 19 files in `preliminary-review-hashes.json` verified four ways:
  `git show 34272878fe` blob == recorded SHA-256 == current working tree ==
  my own bytecopy (`bytecopy/` in this lane). Freeze commit `34272878fe`
  ("Record complete proposed Hermite envelope argument and prior-art checks")
  exists on `main`. Result: `ALL 19 ... True`.
* I edited nothing outside my lane. Ledger untouched; no staging/commits.

## 2. Source gate (G1)

Read directly from the actual PDFs in `sources/` (not summaries):

* **arXiv:2004.10441 v1, Eq. (30), p.10**: |H_n(x)e^{−x²}| ≤
  [2^nΓ((n+1)/2)/√π]·g_n(min(x,x_n))·e^{−x²/2}, g_n(x)=(1−x²/(2n+1))^{−1/2},
  x_n = √(2n+1)(1−π/(2(2n+1))), for all n∈ℕ⁺, x>0. "We have checked
  numerically that the conjecture holds at least for n ≤ 20."
* **Published CTP 73 (2021) 075002, Eq. (29), p.8** (DOI 10.1088/1572-9494/abf1dd):
  identical statement (I rendered the publisher PDF page and read it).
* The linearization of x_n is ambiguous in both text extractions; I resolved it
  against the published **Table 1** (n=2..10): a = √E(1−π/(2E)) reproduces
  1.534, 2.052, 2.476, 2.843, … exactly; the alternative reading 2/(πE) does not.
* **MathDB 346243 live record**: statement literal, `status: "open"`, every
  activity array (`comments`, `solutions`, `model_attempts`, `human_solves`,
  `replies`, `formulations`) empty. That is source evidence of openness, not
  evidence of novelty.
* Physicists' normalization confirmed: the source defines H_n by Rodrigues
  H_n = (−1)^n e^{x²}(d/dx)^n e^{−x²}. PROOF.md's restatement is literal.

## 3. Mathematical gate (G2) — independent rederivation

Fresh code (`review/exact_checker.py`, mpmath 60 dps + sympy exact + dense
sampling; output `evidence/exact_checker_output.txt`). Written from the
statement, not from `check_proposal.py`:

* **Constants**: C(2m) = (2m)!/m! (exact, half-integer Gamma); γ_m closed form
  matches A²/(EC²) to <1e−50 for m=0..29; γ_0 = π/3, γ_1 = 9π/28 exactly.
* **Wallis identities (symbolic, sympy)**:
  γ_{m+1}/γ_m = (2m+3)²(4m+3)/(4(m+1)²(4m+7)) = 1 − 1/(4(m+1)²(4m+7)) — both
  differences simplify to **0**. γ_m strictly decreasing → 1 (γ_190−1 ≈ 8.6e−7),
  γ_m > 1, and γ_m < r_m = 2E²/(2E²−1) for m = 0..199. 9π/28 < 99/98 (⟺ π < 22/7).
  Note γ_m > 1: the *naive* energy bound B(x) ≤ B(0) = A² = γ_m E C² is too
  weak by exactly √γ_m — the odd case genuinely needs the proposal's mechanism.
* **Sine comparison (3)** both directions plus positivity of y on (0,x0]:
  verified for m ∈ {1,2,3,5,10,50} on 200 points each (sign-corrected; H₁₁'(0)<0
  is why the proposal says "change the sign of y").
* **§4 constants**: Taylor gives cos √2 ≥ 7/45 *exactly* (1−1+4/24−8/720 = 7/45);
  sin √2 ≤ (7/10)√2; c > 9/10; min over E ∈ {7,11,15,31,63,201}, u ∈ (0,√2] of
  c·cot(cu) − u/(E²−u²) = **+0.1539** ≫ 0. M(u) increasing (m ∈ {1,2,3,10});
  q y²/(EC²) < 99/100 on all of (0,x0] for m up to 100, dense.
* **Energy loss**: ∫₀^√2 u sin²u du = 0.63500 > 1/4; sin 1 > 5/6;
  (5/6)²·½ = 25/72 exactly; B(x0) < A²(1−1/(2E²)) verified numerically
  (m=1,2,3,5) and < EC² exactly for all m ≤ 119 via γ_m < r_m.
* **Bulk**: (E−x²)y²/(EC²) ≤ 1 dense over [0,√E) for n = 1..60.
* **n=1**: quadratic 1 − 15v/7 + 65v²/42, discriminant **−235/147** (exact,
  matches the candidate's own `proposal-check.json`); literal conjecture dense.
* **n=2**: sup_{x≥0}|(4x²−2)e^{−x²/2}| = 8e^{−5/4} = 2.292038… < C₂g(a) = 2.748190…;
  exp(5/4) > 16/5 by four Taylor terms.
* **Tail**: DLMF 18.14.9 read from the official HTML: (2n·n!)^{1/2} e^{−x²/2}|H_n(x)| ≤ 1,
  i.e. |H_n e^{−x²/2}| ≤ √(2^n n!) — numerically confirmed n ≤ 25 on |x| ≤ 200.
  S_n = 2^n n!/C² = √π Γ((n+2)/2)/Γ((n+1)/2) (exact, duplication) ≤ √(π(n+1)/2)
  (log-convexity); S_n < g(a)² for all 3 ≤ n ≤ 200 (S₁, S₂ fail, as the proposal
  correctly handles separately); n=3 ratio = (3π²/28)(1−π/28) < 750/784.
* **Literal conjecture (evidence)**: holds on dense grids for every n = 1..120,
  x ∈ (0,30]. The candidate's own 20100-sample check is thereby corroborated.
* Attribution nuance (no math impact): DLMF credits 18.14.9 to **Szász (1951)**;
  "Cramér–Indritz" names other proofs (Indritz 1961 is paywalled — AMS 403,
  transparent HTML only; no fake PDF was constructed). The inequality itself is
  exactly what §6 uses.

**No mathematical error found.** The argument is complete: even n exact (§1);
odd n ≥ 3 near-zero (§4), bulk (§5) via the energy loss; n = 1 explicit; tail
for n ≥ 3 via 18.14.9 and n = 1,2 directly (§6). Every step I rederived
independently passed.

## 4. Substantive eligibility (G3) — the decisive analysis

The eligibility question: is the source question an immediate corollary of
Foster–Krasikov (2000) Thm 1, Krasikov (2004) Thms 1–2, Szász/Cramér–Indritz,
Sonin–Pólya, or asymptotics (Shi–Nemes–Wang–Wong 2023)?

I read the actual Foster–Krasikov PDF (rendered pp. 307–308). Theorem 1: for
x² < 2k−3/2, (H_k)²e^{−x²} ≤ C(k)·(2y²−4y+3)/√(y(4y⁴−12y³+9y²+10ky−12k))·
exp(15x²/(2y(2y−3)²)), y = 2k−x². (The txt linearization hides the √; I read
the rendered page. Figure 1's scale, (H₂₄)²e^{−x²} ≈ 2·10³⁰ = (24!/12!)²,
confirms physicists' normalization.)

**Independent quantitative subsumption test** (`evidence/gap_analysis.txt`,
`evidence/gap_analysis.json`):

1. **FK/C² at x = 0** (odd k): 1.0013826583317465948 (k=3), 1.000155… (5),
   1.0000375 (7), … — reproduces the candidate's numbers to 17 digits, and is
   > 1 for every odd k tested (3..101). So FK's displayed bound alone never
   implies the conjecture near 0.
2. **That is not the whole story, and the candidate's caveat was justified**:
   a *combination* could still work. I therefore computed the full pointwise
   comparison FK-envelope vs conjectured envelope on FK's entire range. FK
   exceeds the conjectured envelope on **two** kinds of sets for every odd n:
   a shrinking near-zero interval, **and** a large interval abutting its own
   range end, where it diverges: n=3: [0, 0.151] ∪ [1.519, 2.1213]; n=5:
   [0, 0.060] ∪ [2.466, 2.916]; n=7: [0, 0.034] ∪ [3.146, 3.536]; n=9:
   [0, 0.023] ∪ [3.707, 4.062]; (n=11: [0,0.017] ∪ [4.196, 4.528]; …).
3. **Assembly test** {classical Sturm comparison on [0, π/√E]} ∪ {FK} ∪
   {Szász/CI}: the classical comparison y ≤ (A/√E)sin(√E x) is valid (and beats
   the conjecture) on [0, π/√E] for all odd n (max of √γ_m sin u √(1−u²/E²)
   over n ≤ 1001 is 0.99999975 < 1); CI covers x ≥ √(E(1−1/S_n)). Result:
   **genuine uncovered gaps for n = 3, 5, 7, 9**: (1.519, 2.007), (2.466,
   2.695), (3.146, 3.261), (3.707, 3.753). For n ≥ 11 the three classical
   tools happen to cover everything — but no such assembly exists in the
   literature, and it fails outright for n ≤ 9.
4. Consequently the conjecture is **not** an immediate known corollary. The
   candidate's energy-loss mechanism (sine comparison on [0,x0] + Wallis r_m
   comparison ⇒ B(x0) < EC², then monotonicity of B) is what closes the bulk
   uniformly, and is not replaceable by the surveyed classical bounds.
   Krasikov 2004 Thm 1 bounds only the global maximum M_k (k^{1/6}-scale);
   Thm 2 is FK2000's theorem. Shi–Nemes–Wang–Wong Thm 3.1 gives asymptotic
   error terms on the Plancherel–Rotach scale (C_p/N^p, blowing up toward the
   turning point), not a global explicit envelope. Sonin–Pólya concerns
   monotonicity of relative maxima, not explicit constants.

**Conclusion (G3): PASS.** The only conceivable cheap alternative — exact
computer-assisted verification of the literal inequality on the four small-n
gap intervals — is unpublished, not "immediate," and would be a materially
different (non-analytic) proof. The candidate's uniform analytic route is a
genuine resolution of the source question.

## 5. Novelty / prior-art screen (G4)

* **OpenAlex**: exactly 4 citing works (metadata + **full bodies read**, not
  keyword counts): Schiöberg-oscillator (Sci. Rep. 2023), diatomic molecular
  potential (J. Mol. Model. 2023), cavity dephasing (PRA 2021), Casimir–Polder
  array (2026). All merely *use* the Guo–Liu Euler–Maclaurin formula; none
  states or proves Conjecture 1.
* **Krasikov 2004** (actual body): intro confirms the known-bounds landscape
  (A&S/Laguerre specializations, Michalska–Szynal) — all k^{1/6}-crude; no
  pointwise envelope at the conjectured constant.
* **Targeted searches** (DuckDuckGo; Exa rate-limited, recorded): no published
  proof; only the MathDB record, the source paper, K2004, and generic pages.
  Guo's Semantic Scholar profile shows 4 papers, no resolution.
* **Public registry**: the-omega-institute/trureturing landing README — no
  Hermite/346243/2004.10441 content (GitHub code search needs auth; recorded).
  Semantic Scholar citations API: 429 rate-limited, recorded as an access limit.
* **MathDB 346243**: open, zero activity (as of the frozen fetch and my read).

**G4: PASS as a preliminary screen, with limits** (§7). This is not an absolute
novelty certification; the campaign standard does not require one.

## 6. Process

Solo; no child agents; only my lane written (`review/`, `evidence/`,
`bytecopy/`); no shared/ledger/parent edits; no staging or commits; no external
posts. Read-only `git show` used for the freeze.

## 7. Strongest objections (all non-blocking, ranked)

1. **Citation-graph reach.** OpenAlex shows only 4 citers — a thin graph for a
   2020 arXiv paper; Semantic Scholar was rate-limited; no MathSciNet/zbMATH
   sweep. A proof in an unindexed venue/preprint cannot be excluded at this
   stage. This is the main residual risk and must be widened at final review.
2. **The n ≥ 11 classical assembly.** My own analysis shows {Sturm comparison}
   ∪ {FK} ∪ {Szász/CI} covers all n ≥ 11; the candidate's proof is
   irreplaceable only for n = 3,5,7,9 (plus being the uniform elegant route).
   This does not affect eligibility of the source question (one all-n
   statement; the assembly is unpublished and fails for small n), but a final
   packet should state it honestly as a limitation on "new content per degree."
3. **Classical density of the ingredients.** Every ingredient is classical and
   uncredited (the candidate says so); the substance is the assembly and the
   exact r_m/99-100 bookkeeping. An adversary may call it "elementary once
   seen" — but it stood open 2020→2026 in the literal source and MathDB, and
   my quantitative tests found no known-corollary path.
4. **Attribution imprecision**: "Cramér–Indritz" vs DLMF's Szász (1951)
   credit. Cosmetic; should be fixed in any manuscript.
5. **Slack constants**: §4's chain (7/45, 7/50, 3/94, 99/100) is valid but far
   from sharp (true margins ~0.15 on the cot inequality). No correctness issue.

## 8. Evidence inventory (this lane)

* `bytecopy/` — own byte-copy of the 19 frozen files (hash-verified).
* `review/exact_checker.py` + `evidence/exact_checker_output.txt` — independent
  rederivation (all gates G1–G13).
* `evidence/fk-page-1.png`, `fk-page-2.png`, `fk-norm2-1.png` — rendered
  Foster–Krasikov pp. 307–308 actually read (Theorem 1, normalization, Fig. 1).
* `evidence/gap_analysis.txt/.json` — FK exceed-set and assembly-gap analysis.
* `evidence/sine_region_check.txt` — classical-comparison margin, n ≤ 1001.

— pi-hermite-preliminary-review, 2026-10-27
