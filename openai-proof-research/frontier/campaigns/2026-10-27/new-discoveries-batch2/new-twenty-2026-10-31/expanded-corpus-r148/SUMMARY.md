# r148 research handoff

No qualifying new result is nominated. All 20 reserved IDs have entries
in results.json. Five are excluded by actual prior results or the
source's own resolution; fifteen are parked with explicit gaps. No
campaign count or shared ledger was changed. Root alone decides credit.

## Decisive dispositions

- **323878:** Aval et al., arXiv:1301.4803, Theorem 6.2 and its proof
  establish the polyomino symmetry (JCTA, 2014).
- **357336:** the current source's own Theorem 5 proves nrc(G) <= 15
  for every 2-connected graph. Its remaining question is optimality.
- **374945:** all three source versions were fetched. v1 Conjecture 12
  is refuted by v2/v3's terminal-quartic separator at (n,k) = (23,19).
  v3 Theorem 4.2 and Lemma 4.3 were read.
- **369619:** the primary source itself reports failure of the original
  classical-polynomial inverse Gowers conjecture in low characteristic.
  This is a source-reported known result, not an audited new refutation.
- **370344:** a statistic-specific follow-up search found Lin–Wen–Yan,
  arXiv:2608.11771v1, posted 12 August 2026. Section 2 proves exactly the
  reserved joint-distribution conjecture. JACOBI-NONCANDIDATE.md retains
  the separate elementary count argument; it is not a nomination.

## Actual mathematical coverage

| ID | Experiment | Outcome and limit |
|---|---|---|
| 324030 | Exact avoidance DP on 1,400 sampled posets of orders 8–12 | No inequality violation; not exhaustive, strictness characterization untested |
| 324127 | Modular nullities over F_65521 in eight cases with d = 7–9 | All match Mahonian numbers; no uniform multiplicity theorem |
| 372589 | Exact bivariate ASM transfers at orders 10, 12 and 14; HSASM orders 11, 13 and 15; odd-order polynomial division at 13 | Even factor identity and odd quotient checks pass; source verified only through 9; no uniform factorization |
| 373705 | Exact-cover swap searches on 1,230 seeded biregular matrices | Every sample SAT; certificates independently rechecked; larger regimes 6x9,7x10,8x11,9x12 escape source's direct parameter classes |
| 374355 | 11,500 random profiles plus canonical exhaustive profiles through 3 colors and 4 components | No violation in proposed F2 cubical model; semantic homotopy bridge not formally certified |
| 366636 | Full k=5 reflection-compatible option generation, 67,000 exact-cover nodes | Budget stop, UNKNOWN; neither existence nor impossibility established |
| 367343 | Compatibility-preserving multi-head searches at orders 9–12, 300 trials | No non-2-colorable witness; every final object's complementary coloring classes checked |
| 370344 | Joint-count recurrence through n=28; literal cross-check through 9 | Agreement; subsequently excluded by August prior proof |

The strongest sustained routes were the ASM transfer/factorization route,
Jacobi minimum-letter convolution, and the colorful-complex side-choice
model. Petrov swaps and Dyck wreath exact cover supplied further finite
searches. These are bounded investigations, not exhaustive technical
coverage of all finite objects or proofs of the remaining conjectures.
The source-heavy matching-complex, spread-dimension, flow, asymptotic,
analytic and categorical targets are explicitly parked; no dummy bounded
Lean endpoints were created for them.

## Source and novelty limits

All 20 exact corpus lines including their newlines are preserved. Each
entry records chunk SHA-256, raw SHA-256, statement SHA-256 and one-based
line number. Current arXiv abstracts and PDFs for every source have dated
HTTP/status/hash receipts; versions are indexed in outputs/source-index.json.
The terminal-discriminant source was checked in all three versions.
Review depth is stated separately for each ID; fetching a whole PDF is
not represented as reading every theorem in it.

Current public registry checks used /commits/HEAD. OpenAI/math remained
4eaee87548250b2682affda7d05d947c05554bae. Omega was
2ceb015c289375fd786f33b562bee4d591356a6d. Its complete, nontruncated D5
and Problems trees were fetched and keyword path-screened. The seemingly
relevant PetrTurekWreathEigenvaluesRefutation body concerns arXiv:2501.07269,
not reserved 2501.07277. These are bounded path screens, not full proof
registry clearance. No worldwide novelty claim is made.

Historical screens covered exact IDs and full titles in campaign notes
and results, both campaign ledgers and inherited accepted/excluded context.
No scientific earlier disposition of these exact IDs was located. The
reservation's launch note and accidental substring matches in hashes are
not mathematical prior review. Inherited protected families were retained.

One author-hosted PDF route failed with network-unreachable; TLS checking
was retained and the correct arXiv primary copy was obtained. An initially
mistyped supplementary arXiv number (1301.7005) was fetched but not used;
the correct polyomino proof is 1301.4803. Receipts are retained. No denied
403/429 or challenge route was retried, and no TLS verification was disabled.

## Reproduction and formal status

Every Python process ran with python3 -I under scripts/cap.sh and its
process-group RSS watchdog: two allowed CPUs, CPU 120 seconds, wall 140
seconds, RSS limit 6 GiB, MALLOC_ARENA_MAX=2 and lane-local temporary/cache
paths. Heavy experiments were sequential. Full stdout/stderr logs are in
outputs/. The longest experiment stopped itself at about 101 seconds;
no process reached the watchdog RSS limit. No packages were installed.
Downloads were treated as data; downloaded code was not executed.

Examples, from this directory:

    scripts/cap.sh python3 -I scripts/jacobi.py 28
    scripts/cap.sh python3 -I scripts/petrov.py
    scripts/cap.sh python3 -I scripts/asm.py 14
    scripts/cap.sh python3 -I scripts/asm-odd.py 13
    scripts/cap.sh python3 -I scripts/colorful-exhaustive.py
    scripts/cap.sh python3 -I scripts/validate.py

Run them individually. Do not interpret successful diagnostic checks as
Lean certificates. The Jacobi proof remains excluded even if its diagnostic
replay passes. To regenerate results.json, run scripts/report.py followed
by scripts/jacobi-prior-update.py, both under the cap wrapper.

No Lean or leanchecker was invoked because no eligible endpoint survived.
There is no formal theorem, axiom audit, extracted Lean packet, or upstream
rebuild claim. No child agents, git operations, shared-file writes,
publications, uploads, external messages, or browser tabs were used.
