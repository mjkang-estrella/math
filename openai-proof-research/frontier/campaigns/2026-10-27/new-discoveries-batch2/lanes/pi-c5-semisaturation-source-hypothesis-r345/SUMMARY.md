# pi-c5-semisaturation-source-hypothesis-r345 — SUMMARY

Primary-source-first qualification of MathDB **396813** (ssat(n,C₅) = 11n/8 + O(1),
Füredi–Kim Conjecture 4.1 / OWR 2011-01 Conjecture 2). Solo delegate, no children.
Write scope: this lane only. Counts untouched (root integrates): 9 additional / 39 total / next 40.

## Verdict (one line)

**The conjecture is OPEN and untouched; the v1 display Eq. (6) is a falsified erratum at
n=6 (ssat(6)=8 > 7) and on the whole class n≡6 mod 8; exact ssat(8)=10 is new; the
r343 lower-bound mechanism is refuted as stated and replaced by a precise missing
universal lemma; full-scope proof PARKED.**

## 1. Pre-scientific integrity (freeze before content)

- Intake `root-mathdb-breadth-intake-r344`: its own `verify.py verify` re-run by this lane:
  PASS (`383 reported reviews 29 actual upstream hashes`, exit 0), before any content use.
- Inputs copied into `frozen/` and hash-bound in `bindings.json` (9 flat original↔copy
  pairs, all rehashed, sha256+size) BEFORE reading: retained Füredi–Kim v1 PDF
  (1f049570…df4ea, 188909 B), reserved-records extract, r343 work files and proposals.
- Dedup: 396813 absent from both `root-mathdb-accepted-exclusions-r304` files (verified on
  the actual bytes; copies bound in bindings). Not in credited families. 393907 untouched.

## 2. Gate 1 — actual source read (not summaries)

Full pdftotext of the retained v1 PDF (arXiv:1103.0067v1, only version, 2011-03-01,
never revised) plus ar5iv HTML cross-check, plus the record's own primary
(OWR 2011/01, downloaded from publications.mfo.de, sha256 669acffc…4dd2b):

- **Definition** (§4): G is H-semisaturated iff G+e has strictly more H-copies for every
  non-edge e. Verified equivalent to: every non-adjacent pair joined by a 4-path with
  3 distinct internal vertices (a new C5 must use the new edge). Both implementations
  agree on 12,183 graphs (all n=5 graphs; all n=6 m≤6; samples to n=8).
- **Eq. (6) as printed**: "ssat(n,C₅) ≤ ⌈11/8 (n−1)⌉ **for all n ≥ 5**" — direction upper
  bound, range all n≥5, ceiling. Confirmed verbatim in v1 text and ar5iv rendering.
- **Conjecture 4.1**: "ssat(n,C₅) = 11/8 n + O(1). Maybe equality holds in (6) for n > n₀."
- **OWR 2011/01, printed p. 20, Conjecture 2**: "ssat(n,C₅) = 11/8 n + O(1)" — the record's
  exact source (record's "page 16" is off; actual printed page 20). Workshop Jan 2–8 2011;
  arXiv 2011-03-01; JGT received 2011-04-06, online 2012-08-07, 73(2):203–215.
- **Construction decoded from the actual figure** (ar5iv asset es1_2.png, cross-checked
  with OWR Fig. 1): per block, tree edges {1-2,3-4,5-6,7-8,1-3,3-5,5-7} (spine
  2-1-3-5-7-8 with leaves 4,6) plus spokes y–1,y–3,y–5,y–7 → 11 edges per 8 vertices,
  n=1+8t, e=11t; +j triangles at y: n=8t+1+2j, e=11t+3j; pendant-leaf deletion → even n.
  **All nine construction instances verified C5-semisaturated** (n=8,9,10,11,12,13,14,15,17;
  literal C5-count definition for n≤13), and "every vertex within distance 2 of y" confirmed.

### The n=6 discrepancy resolved (independently recomputed)

Exhaustive, complete, two independent definitions (literal C5-copy count and 4-path):

| n | exact ssat | ⌈11(n−1)/8⌉ | paper's construction | (6) status |
|---|---|---|---|---|
| 5 | 6 | 6 | 6 | ok |
| 6 | **8** | 7 | 8 | **FALSIFIED** |
| 7 | 9 | 9 | 9 | ok |
| 8 | **10 (new)** | 10 | 10 | ok |

- ssat(6)=8: zero hits over all 6,435 seven-edge graphs on 6 vertices (complete); witness
  with 8 edges. ssat(8)=10: zero hits over all 11,199,045 edge-sets with m∈{7,8,9}
  (complete, pruned); witness = the paper's own pendant-dropped construction.
- Internal source check: on n=8t+6 the paper's own construction yields 11t+8 edges but (6)
  claims ⌈11(8t+5)/8⌉ = 11t+7 — the displayed bound is stronger than what the described
  construction achieves, exactly on the n≡6 (mod 8) class, including n=6.
- **Corrected display**: ssat(n,C₅) ≤ ⌈11(n−1)/8⌉ for n ≢ 6 (mod 8), and ≤ ⌈11(n−1)/8⌉+1
  for n ≡ 6 (mod 8). This is a display-level erratum in v1 (journal body inaccessible:
  renyi.hu 403, Wiley paywalled — limitation recorded; JGT abstract matches arXiv).
- **Impact on Conjecture 4.1: none.** A finite-n violation of a displayed upper bound
  cannot refute an asymptotic claim; 11t+7 and 11t+8 are both 11n/8+O(1). Observed
  deficits e−11n/8: −7/8, −1/4, −5/8, −1 (n=5..8), −11/8 (FK construction). Consistent.

## 3. Gate 2 — is the literal conjecture publicly settled? NO.

Bounded current search (2026-10-31, timestamps in access log): no proof/refutation of
ssat(n,C₅)=11n/8+O(1) found. UnsolvedMath lists "Semisaturation Number of the Five-Cycle"
(v1.7, reviewed OWR record) as open; page fetch 429'd (not retried, snippet-level only).
MathDB: open, 0 solutions. Best published lower bound remains the paper's own
9n/8 − O(1) (their §9 + Lemma 8.2 at k=5). Nearest neighbors checked: paths (Burr 2017),
wheels (2503.10268), C≥r-saturated (2002.09882/JCTA), odd-cycle saturation spectrum
(JGT 2021), triangle-free saturation lower bounds (2402.11387). **No retirement; no
routine bridge.** Not an exhaustive registry clearance.

## 4. Gate 3 — full-scope mechanism: PARKED with the precise missing lemma

r343's leaf-block plan is structurally broken (per-block errors don't sum to O(1)). The
repaired, precise target — the **missing universal lemma**:

> Let G be C₅-semisaturated, x = #pendant vertices, G₀ its 2-core (N = n−x vertices).
> Then e(G₀) ≥ (11N + 3x)/8 − C for an **absolute** constant C.

Since pendant neighbors are distinct with degree ≥3 (Lemma 7.1, verified), x ≤ n/2, and
deleting pendants preserves semisaturation, this lemma gives e(G) ≥ 11n/8 − C — the full
lower bound. FK construction shows C ≥ 11/8, so C=11/8 would be tight (ssat = 11n/8 − 11/8
on n≡1 mod 8). The constant is global, so the endblock objection does not apply.

**Refuted naive versions (verified, not hand-waved):**
- "Core alone is 7/4-dense" is FALSE: the friendship graph F_t (t triangles sharing one
  vertex) is min-degree-2 and C₅-semisaturated (verified t=1..6) with e−7N/4 = −t/2−7/4 → −∞.
- Pendants cannot sit on a sparse core: attaching pendants to F_t's center destroys
  semisaturation (no 4-path pendant→outer; verified t=2..5). The content is in how
  4-path witnesses from pendants constrain the core around deg≥3 attachment vertices.

**Why parked:** no concrete mechanism for the absolute constant survived bounded
inspection; the gate forbids a deep discharging project without a surviving full-scope
route. Recommended next bounded step (root decision): exact n=9,10 (permitted now that
the source question is resolved) and small-case minimum of the coupled deficit
(current exhaustive n≤8 minima: −7/8, −1/4, −5/8, −1; FK: −11/8). No universal-constant
claim is made from finite trends. **No complete proof achieved; no new-to-literature
claim is made.**

## 5. Retained sources / provenance (all lawful public HTTP, UTC 2026-10-31)

- `frozen/…/furedi-kim-1103.0067v1-cycle-saturated.pdf` — intake copy of arXiv:1103.0067v1,
  sha256 1f049570ebbe0fbc760c0b6eb964044869bf74184ede791c91f8db78482df4ea (188909 B).
- `sources/owr-2011-01-combinatorics.pdf` — OWR 2011/01 (record's primary),
  https://publications.mfo.de/bitstream/handle/mfo/3216/OWR_2011_01.pdf?isAllowed=y&sequence=1,
  HTTP 200, 686535 B, sha256 669acffc78ac85b9960af120c763b97d8dd5cda176c1416322d238592884dd2b.
- `extraction/es1_2.png` — ar5iv figure asset used to decode the construction,
  https://ar5iv.labs.arxiv.org/html/1103.0067/assets/es1_2.png, HTTP 200,
  sha256 2b2047756a947afe3de4bafd19376bc999f542b6f383c5a9c746ad8d7ae225d3.
- `extraction/furedi-kim-v1.txt`, `extraction/owr-2011-01-layout.txt`, `extraction/owr-2011-01.md`.
- `work/access-log.md` — every fetch, the renyi.hu 403 and unsolvedmath.com 429 (stopped,
  no retry/bypass/TLS change), MathDB-network/GitHub-API/ScienceDirect/browser non-use.
- Journal version JGT 73(2):203–215 body: NOT accessed (limitation, see disposition).

## 6. Bounded computations (fixed guard; peak group RSS ≤ 28 MB, walls 15.8 s / 187.5 s)

- `work/ssat_c5_independent_r345.py` → `.out` — definition agreement, exact minima
  n=5..8, r343 witness re-verification, all nine construction instances, (6) table. guard_exit 0.
- `work/ssat_c5_structure_r345.py` → `.out` — friendship-graph refutation of the naive
  core lemma, pendant-attachment obstruction, exhaustive coupled-deficit minima n≤8. guard_exit 0.
- Preserved failures: first run's reversed-edge harness bug (recorded in the .out history
  and code comment), a dropped edge in the r343 n=5 witness transcription (fixed), and the
  guard-killed nothing (no kills this lane). r343's own killed run remains recorded in r343.

## 7. Deliverables

`SUMMARY.md` (this file), `disposition.json` (exact corrected source claim + evidence
levels), `bindings.json`, `verify.py` (final verifier: rehashes all original/ref/copy
bytes and the exact payload set; exits NONZERO on any mismatch), `manifest.json`
(SHA256+size of every payload except manifest.json/verification-receipt.json),
`verification-receipt.json`. Old targets 393907 / 338062 / 364119 untouched.
