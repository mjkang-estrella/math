# expanded-corpus-r204 (Claude lane): summary

Reservation: 20 IDs between 349829 and 404028 (reserve8; `reservation.json`). The exact raw corpus lines, with one-based line numbers and chunk, raw and statement sha256 hashes, are in `raw/*.jsonl` and `extracted.json`, produced by `scripts/extract.py`.

The campaign-history grep (`history-matches.txt`, scoped to new-discoveries-batch2) found no prior handling of any reserved ID; all hits are numeric coincidences. The neighbouring item 349656 (exact slow k-NIM) was only parked in r181.

Lane rules were followed throughout:
* no Lean, lake or solver runs;
* every computation was a single `bash -c 'ulimit -v 2000000; timeout 100 python3 -I …'` process, one per tool call, in the foreground;
* no writes outside this lane, and no git.

## Candidates (ranked; no credit claimed)

| rank | ID | result | certificate / Lean cost | main credit risk |
|---|---|---|---|---|
| 1 | **350721** | Alexandersson–Kebede Conjecture 5.2.1 (AJC 2023 VoR form) is **false for k = 3 and every n ≥ 8**. The normalised coefficient of x_{1,n−4,n−2,n−1} y_{rest} is −1. The conjecture holds for n ≤ 7. Exactly 8 permutations contribute (proof in `CANDIDATE-350721.md`). | Instance n = 8: 8 explicit permutations plus a characterisation lemma; moderate Lean cost | Significance moderate (a "further ideas" conjecture); the MathDB wording is trivially false at k = 1, so the record must be judged against the VoR statement |
| 2 | **360653 / 361128** | The GM strategies are **not** a Nash equilibrium of ℓ-player exact slow NIM(n, n−1) for any n ≥ 3, ℓ ≥ 3. The uniform witness x⁰ = (((n−2)ℓ+1)^{n−1}, (n−1)ℓ−1) admits a first-move deviation that turns a loss into a win. The proof uses block invariants, and the claim was checked by computer for n ≤ 9, ℓ ≤ 12. A convention-free instance is (5,5,6). With GMMV23, the profile is an equilibrium iff ℓ = 2. | Instance (n, ℓ) = (3,3), x⁰ = (4,4,5): two explicit plays of length 6 and 5; very low Lean cost | Concluding-remark conjecture with a tiny counterexample; the two records are one statement; the DAM VoR of 361128 is unread |
| 3 | **351888** | Petruševski–Škrekovski conj:3 is false: the Shannon triangle (7,7,8) of type (2,1,1) has χ'_S ≥ 4 under every reading of S (half-page parity proof). Under the intended reading the smallest counterexample is (4,5,5). An exact characterisation for Shannon triangles was computed for bouquets ≤ 22. | Finite; low cost (parity argument or a 58k-case decide) | Same object family as the source's printed (4,4,3) obstruction, so it may be judged a variant; the source's two definitions of S conflict; the JGT VoR is unread |

Each candidate file gives the exact source statement and every version read, a complete ordinary proof, the certificate files, a bounded prior-art screen, honest risks, and a Lean statement-correspondence plan with draft sources marked UNCOMPILED.

## Other dispositions

| ID | outcome | basis |
|---|---|---|
| 349829 | known: proved in source | Jin–Gu–Zhang (LAA 2021) prove the Lin–Liu–Lu conjecture (TeX §2) |
| 349831 | known: refuted in source | Bulgakov–Kozachinskiy–Vyalyi give an infinite series of counterexamples to Hirschorn (TeX line 315) |
| 350025 | known | Sun–Zhao, and bijectively Lin–Wang–Zhao (the source) |
| 381721 | known / trivially false | As written, this is Luo's 2018 theorem. Under the intended "prime-length" reading it fails at r = 2 via K_{a,b} |
| 351536 | refuted by a published bridge (zero credit) | W_4 has Δ = 4 and L(W_4) (8 vertices) is non-WR (KSSU 2011), so by SMT2019 (cited by the source) it is not 3-semi-transitive. Confirmed by brute force over all 40,320 orders |
| 351162 | literally false; degenerate, not promoted | n = 6, k = 2: m = 5 (stars), m = 10 (K5 ∪ K1); n = 6, k = 3: every m ≤ 10; also trivially false for m < n−k |
| 404028, 350925, 356829, 352733 | parked (famous, deep, complexity, analytic) | quick dispositions per the brief |
| 353896, 354915, 355026, 355038, 355948, 352460 | parked | no planar generator / niche structure search not run / supremum over infinite classes / analytic tensor norms / heavy Grothendieck machinery (open per web search) / maxima unknown |

## Searches and access

* **arXiv** (abs pages, e-prints, TeX read):
  * the 18 arXiv-sourced records, with all versions: 2109.04099 v1, v2, v3 and 2105.08455 v3;
  * citing and nearby works: 1102.3980, 2509.03339 (abs), 2206.11236, 2402.16251, 2407.21755, 2304.06498, 2311.13511.
* **Versions of record:** the AJC 86(3) PDF was read. Crossref (2 queries) located the DAM 2024 VoR of 2312.08382. The JGT VoR of 2109.04099 is unread; a dlib.si URL returned an unrelated paper.
* **Web searches** (WebSearch, standard unless noted):
  * Alexandersson–Kebede follow-ups (×3, one extended);
  * slow NIM GM Nash (×4, one extended);
  * the Petruševski S-colouring and its JGT version (×2);
  * word-representable line graphs (×2);
  * the Grothendieck reverse order (×1);
  * forest-path partition (×1).
* **Registries** (`outputs/registry-screen.json`):
  * Lean Pool HEAD 01db1d70 (tree and projects.yml reused from r202, re-hashed);
  * Omega HEAD 21d47954 (D5 and Reg refetched recursively; Problems unchanged);
  * OpenAI/math HEAD 4eaee875;
  * 7 GitHub repository searches (limit 8), with no 403 or 429.

  No prior Lean proof or refutation of any candidate was found.
* All receipts, with URL, status and sha256, are in `outputs/fetch-receipts.json`. No denials; no TLS overrides.

## Reproduction

All scripts are in `scripts/` and all outputs in `outputs/` and `logs/`. The key commands, each a single capped `python3 -I` run:
* `nim_certificate.py`, `nim_family.py 9 12`, `nim_scan.py lit 14 3,4 3,4,5,6,7`;
* `signed_rlm2.py 8`, `signed_rlm3.py 9`, `signed_rlm_cert.py 8 1,4,6,7 2,3,5,8`, `signed_rlm_family.py 10|11|12`;
* `sedge_tri.py deg|sub|subnl 20`, `sedge_tri_char.py subnl 22`, `sedge_show.py 7 7 8`;
* `semitrans.py W4`, `propconn.py 6 2|3`.

Remaining for root:
1. Lean endpoints, beginning with the cheapest (NIM instance), then the strongest (350721 at n = 8, k = 3).
2. Independent reviews.
3. Reading the DAM and JGT versions of record.
