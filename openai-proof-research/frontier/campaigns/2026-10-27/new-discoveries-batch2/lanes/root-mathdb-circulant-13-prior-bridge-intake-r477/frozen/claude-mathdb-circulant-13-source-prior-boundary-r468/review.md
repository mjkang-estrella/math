# r468: source, prior and substantive gate for MathDB 372627

**Recommendation: EXCLUDE as a routine corollary of published prior work.** The root adjudicates.

- **Prior work.** Kim–Hwang–Song, *L(3,2,1)-labeling for cylindrical grid: the Cartesian product of a path and a cycle*, Korean J. Math. 25(2) (2017) 279–301, doi:10.11568/kjm.2017.25.2.279. It is open access under CC BY-NC 3.0. The full body was obtained and read.
- **How the endpoint follows.** It is a short elementary corollary of that paper's published results, through a one-line graph-homomorphism pull-back:
  - For n ≡ 2 (mod 4), KHS Theorem 1(4) is enough at statement level.
  - For n ≡ 4, 8 (mod 12), the explicit periodic classification inside KHS's proof of Lemma 5 closes it, together with Lemmas 1 and 3.
- **Method precedent.** Shao–Vesel, CEJOR 23 (2015) 659–673, published the same transfer-digraph closed-walk method for L(3,2,1)-labelings. It gives the same span 11/12 dichotomy with forced period 12 on the sibling square-grid quotient T_{4,m}.
- **Fallback.** If the root does not accept the use of KHS's proof-internal Lemma 5 classification, then n ≡ 2 (mod 4) stays excluded at statement level. The residual n ≡ 4, 8 (mod 12) should be **PARKED** under the recheck triggers below. It should not be invested in.

This review is solo, with no children. Writes went only to this lane. There were zero MathDB, Google, GitHub, ScienceDirect, browser or account requests. Nothing was formalized. No manuscript was written and no certificate was regenerated. Counts are unchanged: 9 additional / 39 total / next 40. Integrity PASS below is not a mathematics or novelty PASS.

## Hypothesis

MathDB 372627 states: for even n ≥ 142 and G = C_n(1,3), λ_{3,2,1}(G) = 11 if 12 | n and 12 otherwise. The record merges source Theorem 6 (12 | n ⇒ 11) and Theorem 10 (≤ 12 for even n ≥ 142) with the open Conjecture 11. The only open content is therefore:

> λ ≥ 12, i.e. no labeling with labels 0..11, for even n ≥ 142 with 12 ∤ n.

r376 is complete. It proves this endpoint with a 152-state / 128-edge window graph that has exactly two directed 12-cycles. As a by-product, every span-11 labeling of C_n(1,3) for n ≥ 19 has the form c ± 5x (mod 12).

## Gates

| Gate | Verdict | Basis |
|---|---|---|
| Intake integrity | PASS | `logs/validate_intake.json`, described below. |
| SOURCE, arXiv v2 statement | PASS (reused) | r376/r382 read the frozen v2 PDF on 2026-10-31. I re-read pp. 2–11 and the references from the r382 retained extraction (sha `0b6444…`). |
| SOURCE, published DMGT body | HOLD (new negative metadata; not evidence of non-publication) | Crossref has no DMGT-prefix (10.7151) DOI for Holub/Kopřiva except 10.7151/dmgt.1356 (Holub, 2012). The title query also returned no DMGT DOI. zbMATH Open indexes the work only as `arXiv:2601.12574`. The DMGT TLS route was not retried. The arXiv placeholder header is not publication evidence. |
| PRIOR | Complete applicable bridge found (KHS 2017), with a method precedent (Shao–Vesel 2015) | The full bodies of both papers were read. The bridge is given below. |
| Current public registry | HOLD (GitHub routes barred); immaterial to EXCLUDE | The pinned openai/math snapshot fd4aeeb (2026-10-08) has no L(3,2,1), labeling or circulant-labeling entry. The only circulant hit is the unrelated circulant-Hadamard result 179. |
| SUBSTANTIVE | EXCLUDE (routine corollary) | Every load-bearing step except two elementary lemmas is in a 2017 publication. Chronology: KHS accepted 2017-06-21, while the source is v1 2026-01-18 / v2 2026-05-12. The source does not cite KHS or Shao–Vesel 2015; its reference list was checked. |

## Integrity

**Freeze order.**
- At 11:26:11Z, before any content was read, all 57 intake payloads plus `manifest.json` were sha256'd into `logs/intake-prehash.sha256`.
- `tools/validate_intake.py` then ran under the guard: PASS, 0 failures. It checked:
  - the 57 manifest entries against actual files, with the exact file set, excluding only `manifest.json` and `verification-receipt.json`;
  - all 54 bindings, both original and copy;
  - the nested r376 manifest (46 entries) and r382 manifest (58 entries) against the **original** lane files;
  - every frozen copy against its original.
- The upstream `verify.py` was not executed and no receipt was rewritten.
- r382 retained bodies were read only after this validation.
- Every new HTTP body was hashed into `http/*.meta.json` at save time, before it was read.
- `input-bindings.json` is a later consolidated flat-ref file: 72 absolute paths with sha256 and size. It is timestamped as written after reading and is not presented as the initial freeze.

## The bridge

Notation:
- C = C_n(1,3) with n ≥ 19 (only n ≥ 142 is needed).
- P_m□C_n is the cylinder in KHS notation: vertices (i, j), with i ∈ [0, m−1] the path coordinate and j ∈ Z_n the cycle coordinate.
- f: Z_n → {0, …, 11} is an L(3,2,1)-labeling of C.

**Lemma A (pull-back; elementary, new-to-us but routine).** Put φ(i, j) = j + 3i (mod n) and g = f∘φ.

For any m consecutive rows, g is an L(3,2,1)-labeling of P_m□C_n with labels in [0, 11], and each row of g is a cyclic shift x ↦ f(x + 3i) of f.

*Proof.*
1. φ maps path steps to ±3 and cycle steps to ±1, so d_C(φu, φv) ≤ d_cyl(u, v).
2. Let 0 < d_cyl(u, v) ≤ 3, and write Δ = Δj + 3Δi with |Δi| + |Δj| ≤ 3, taking Δj as the cyclic representative of least absolute value.
3. Then |Δ| ≤ 9 < n. Also Δ = 0 would force |Δj| = 3|Δi|, so 4|Δi| ≤ 3 and u = v. Hence φu ≠ φv.
4. So |g(u) − g(v)| ≥ 4 − d_C ≥ 4 − d_cyl. ∎

Checked by BFS for m = 5 and all n ∈ [19, 200] (1,833,468 pairs; `logs/bridge_check.json`). This is corroboration, not proof.

**Lemma B (elementary).** In C with n ≥ 19, the offsets 1, 2, 3, 4, 6 have distances 1, 2, 1, 2, 2 respectively. So f(x + d) = f(x) for all x is impossible when d ∈ {1, 2, 3, 4, 6}. (By r376 (B1); also BFS-checked.)

**Case n ≡ 2 (mod 4): statement level.**
- KHS Theorem 1(4), p. 294 (`http/kjm2017-pdf.txt` l.675): "If m ≥ 5 and n is not a multiple of 4, then λ_{3,2,1}(P_m□C_n) ≥ 12."
- No lower-n restriction is attached to the inequality; the restriction n ≥ 138 applies only to equality.
- By Lemma A with m = 5, a span-11 f would give a span-11 labeling of P_5□C_n. Contradiction.
- This settles n ≡ 2, 6, 10 (mod 12).

**All n with 12 ∤ n: proof level.** Suppose f uses labels in [0, 11].
1. **Label 0 is used.** By source Proposition 5, λ(C) ≥ 11, so f must use 0.
2. **Adjacent {0,10} or {1,11}.** KHS Lemma 3 (m ≥ 3, pp. 288–289, l.387) and the inversion remark after it exclude adjacent g-labels {0, 10} and {1, 11}.
3. **Adjacent {0,11}.** Two routes:
   - KHS Lemma 2 (m ≥ 5, p. 287, l.371) excludes it.
   - Independently of Lemma 2's abbreviated proof, KHS Lemma 1 (p. 284, l.217) can be applied at statement level to four consecutive rows containing the pair. It forces those rows to be horizontal expansions of the 6-column patterns A or B, so g has row period 6. Then f(x + 6) = f(x), contradicting Lemma B.
4. **Lemma 5 setup.** So all adjacent differences in g are at most 9. Take the three rows centred on a 0 of g. They form a labeling of P_3□C_n satisfying hypotheses 1–3 of KHS Lemma 5 (p. 291, l.538).
5. **Lemma 5 classification.** The proof of Lemma 5 (pp. 291–292, l.545–562, Table 6) normalises under KHS's equivalences: inversion, j ↦ −j, top/bottom reversal and translation. Of the six neighbourhood cases, (1), (2), (4) and (5) are contradictions. Verbatim: "In cases (3) and (6), we have the identities f(i,j)=f(i,j+12) and f(i,j)=f(i,j+4) respectively … As a consequence n is 4 or 12".
   - The printed Table 6 rows equal 8 − 3i + 7j (case 3) and 8 − 5i − 3j (case 6) mod 12.
   - Both are valid strip labelings.
   - Their row periods are 12 and 4 under every equivalence (`bridge_check` (b), (d)).
6. **Closing.** Equivalences preserve row periods, so some row of g, which is a shift of f, has period 4 or 12.
   - Period 4 contradicts Lemma B.
   - Period 12 gives f(x + gcd(12, n)) = f(x). If 12 ∤ n, then gcd(12, n) ∈ {1, 2, 3, 4, 6}, which contradicts Lemma B.
   - Hence 12 | n.

With source Theorem 10 this gives Conjecture 11. The case-3 pull-back is exactly r376's c ± 5x family, since 7 ≡ −5. So r376's independent certificate corroborates the KHS classification on this instance.

**What is genuinely ours:** Lemma A (a standard locally-injective-homomorphism argument, five lines) and the three-line gcd/Lemma B closing step. Everything else is published, and it predates the conjecture by nine years. Under the batch rule "never count … routine corollary", this does not earn credit. The tiny r376 certificate also shows that no deep new obstruction is needed.

**Method precedent: Shao–Vesel 2015** (full body read; publicly served HTML, `http/springer-shaovesel2015-abs.txt`).
- Their Theorem 1, after Klavžar–Vesel 2003: C_n□C_m admits a k-L(3,2,1)-labeling iff the window digraph D_{n,k} has a closed walk of length m.
- Their Theorem 4 proof: "D_{4,11} with 96 vertices … found only cycles of length 12", hence λ(T_{4,m}) = 11 iff 12 | m, and 12 otherwise for large m.
- This is r376's method, with the same numbers, on a sibling square-grid quotient. It is not itself a bridge to C_n(1,3), because no torus T_{4,m} maps onto C_n(1,3) for n ≥ 142. It does strengthen the routine-adaptation objection for the whole method family.

## Provenance and coverage table

| Work | Coverage this lane | Scope vs t = 3 target | Disposition |
|---|---|---|---|
| Holub–Kopřiva arXiv 2601.12574v2 | r382 retained PDF/extraction (sha `5c57e3…`/`0b6444…`); read pp. 2–11 and references | Exact source. Conj. 11 is open in v2. KHS and SV2015 are not cited. | SOURCE PASS (reused); DMGT HOLD |
| **Kim–Hwang–Song, KJM 25 (2017) 279–301** | **Full PDF** via doi.org → KoreaScience (`http/kjm2017-pdf.body` sha `697331…`; text `0a929f…`). Read pp. 279–294 in full; Appendix tables skimmed. | Thm 1(4), Lemmas 1, 2, 3, 5 (proof) and 6. | **Load-bearing prior bridge** |
| **Shao–Vesel, CEJOR 23 (2015) 659–673** (online 2014-10-19) | **Full text** served publicly on the Springer article page (`http/springer-shaovesel2015-abs.body` sha `952a0a…`). Sections 1–3.2 read through Thm 5. | Transfer digraph D_{n,k}; T_{4,m}: 11 iff 12 \| m. Also cites [8] for λ(P_m□P_n) = 11 for m, n ≥ 4. | Method precedent; not a bridge |
| [4] Čada–Ekstein–Holub–Togni arXiv 1207.4219v2 | r382 retained full text; read definitions, Lemma 3, Prop. 2, §4, Table 8 | rl_3(D(1,3)) = 11, infinite line only. No classification of optimal labelings and no cyclic periods. | Not a bridge (minimum span only) |
| [13] Korže–Shao–Vesel 2022, author supplement | r382 retained; read the D(1,t) table and D(1,3) constructions | D(1,3), k = 3: 11, listed as "previously known". Constructions are linear b(i) = a·i mod m for k ≥ 7 only. No period classification. | Not a bridge (supplement only; full DAM article not read) |
| [1] Bianco–Calamoneri, TCS 2026 (Zbl 1583.05144) | zbMATH review only; arXiv author listing has no preprint | C_n(1,2) only | Body not read; not needed for EXCLUDE |
| [8] Chia–Kuo–Liao–Yang–Yeh, TJM 2011 | Body not read (ProjectEuclid route parked). Cited content via KHS p. 280 and SV2015: λ(P_m□P_n), the P_2□C_n characterisation, 4 \| n sufficiency for cylinders. | Grids and cylinders; no C_n(1,3) | Not needed for EXCLUDE |
| Klavžar–Vesel 2003 (DAM); Shao–Vesel 2013 (ILP/SAT, products of paths and cycles) | Not read; known only from citations in SV2015 | General rotagraph transfer algorithm | Method family only |
| zbMATH `"L(3,2,1)"` search | 20 records (`evidence/zbmath-l321.list.json`); review texts read where licensed | Surfaced KHS and SV2015. Holub–Kopřiva is indexed only as arXiv. | Discovery |
| arXiv API (3 queries) | circulant ∧ labeling (stemmed, noisy); au:Calamoneri; au:Vesel ∨ au:Korze | No successor to the source; no arXiv versions of [1] or [13] | Discovery; not an absence proof |
| Crossref (4 requests; one returned 404) | Source title; DMGT prefix by author; SV2015 and AKCE-2024 DOIs | AKCE 2024 is Zhang, "Optimal L(3,2,1)-labeling of trees", which is irrelevant. The KJM DOI is not registered at Crossref (404), so it was resolved via doi.org. | Metadata only |

The full request ledger, with UTC, status, sha and challenge markers, is in `evidence/fetch-ledger.json`: 12 requests, 11 returned 200, 1 returned 404, and there were 0 challenges.

## Family note (observation only; no sibling solving)

The KHS bridge is specific to t = 3. For 372628 (C_n(1,5), span 13/14) and source Conjecture 20 (C_n(1,4), span 15/16), the pull-back gives no obstruction, because cylinders already have λ ≤ 12. Their status is not changed by this lane. Shao–Vesel 2015 / Klavžar–Vesel 2003 is a published precedent for their method, which is relevant to the root's family-credit decision but is not an exclusion of either sibling.

## Limitations and failures (preserved)

- KHS's case analyses (Lemma 1 Appendix A; Lemma 5 Table 6; Lemma 2 "similar method") are terse table summaries. I did not audit them independently. The bridge cites the published proof claims, and the endpoint's truth is independently established by r376.
- The proof-level step uses a statement inside a lemma's proof, not a lemma's statement. If the root treats that as non-routine, only n ≡ 2 (mod 4) is excluded at statement level, and the fallback is PARK for n ≡ 4, 8 (mod 12).
- Not read: the [1], [8] and [13] full articles; Klavžar–Vesel 2003; Shao–Vesel 2013; the DMGT published version; the current registry head; citing literature after May 2026. No web search was performed in this lane.
- Errors:
  - Crossref returned 404 for the KJM DOI. This is a registry absence, not access control. Resolution went through the canonical doi.org.
  - One `grep` regex hit a complexity limit (cosmetic) and was re-run with a simpler pattern.
  - The arXiv stemmed query returned mostly unrelated papers.
- KoreaScience also offered a signed PDF URL; only the plain public PDF link was used.
- **Guard deviation (preserved).** A single verifier negative test ran read-only on a scratch copy in a temp directory, with one appended byte to review.md. It ran with `python3 -B -I` but **without** `helper_guard.py`, contrary to the rule. It exited 1 (FAIL) as expected, and the scratch copy was deleted. No lane file was affected. All other helper runs used the guard.
- Retained third-party bodies (the KJM PDF under CC BY-NC, the Springer HTML) are local research copies only and must not be republished.

## Remaining acceptance gates (only if the root rejects EXCLUDE)

1. The root, or an independent reviewer, confirms or refutes the KHS Lemma 5 periodicity claim at pp. 291–292 (Table 6, cases (3) and (6)).
2. An authenticated DMGT body comparison.
3. Current-registry coverage through an authorised route.
4. The [8] body, for any earlier C_n(1,3)-type statement.
5. A family-credit decision against Shao–Vesel 2015.

**Recheck triggers:**
- a published or arXiv erratum to KHS 2017;
- DMGT publication with changed Conjecture 11 text;
- an authorised registry route becoming available.

## Files

- `review.md`: this file.
- `input-bindings.json`: flat refs to 72 originals.
- `logs/`: the intake pre-hash and every guarded run's stdout/stderr. The two `.json` files are `validate_intake.json` and `bridge_check.json`.
- `http/`: 12 request bodies with `.meta.json`, plus 3 text extractions.
- `evidence/`: the fetch ledger, arXiv/zbMATH listings and `coverage.json`.
- `tools/`: `validate_intake.py`, `fetch.py`, `atom_list.py`, `zb_list.py`, `html_text.py`, `bridge_check.py`, `bind_inputs.py`, `make_manifest.py` and `g.sh`.
- `manifest.json`: exact set of every lane file except `manifest.json` and `verification-receipt.json`.
- `verify.py` (lane root) exits nonzero on any manifest or binding mismatch, re-checks the intake manifest and the r376/r382 originals, and writes `verification-receipt.json`.
- The manifest-generation run and the final verifier run print to the terminal only. The verifier's result is recorded in the receipt, so no unmanifested log files exist.

All helpers ran through `helper_guard.py` (sha `825ee0d4…`) with fixed limits of 512 MiB / CPU 210 s / wall 230 s, never raised. Peak RSS was 24 MiB and the longest wall time 2.8 s.
