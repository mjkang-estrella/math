# SUMMARY — pi-core-containment-source-hypothesis-r341 (MathDB 393907)

Target: MathDB 393907 — "Every simultaneous (p,q)-core partition is contained in the maximal
(p,q)-core kappa_pq", alleged source OWR 2006/15, p. 19 (ems.press/journals/owr/articles/1265).
Solo lane, no children; root-only orchestration respected.

## Gate sequence executed

1. **Integrity before content (PASS).** Ran root-mathdb-breadth-intake-r340/verify.py (verify
   mode) under the pinned helper guard: PASS — 27 hash-bindings rehashed against originals,
   frozen r339 child manifest (22 payloads) verified, 26 upstream actual hashes. Confirmed the
   DECISION.md observation: the alleged extract-level 393907 source directory is NOT in the
   r339 manifest (sources/ has only 392617, 392840, 393754, 394209, 394494). Source/novelty
   were therefore unqualified; all primaries retrieved fresh this session.
2. **Dedup after binding (PASS).** root-mathdb-accepted-exclusions-r304: manifest PASS;
   393907 appears in neither accepted-exclusions.json (33 record IDs) nor
   historical-dispositions.json (75 rows); no core-partition topics. Flat references only —
   no historical trees copied.
3. **Primary-first hard gate.** Retrieved and read actual proof bodies:
   - **OWR 2006/15 p. 913 (PDF p. 19) — literal question confirmed** (Olsson's abstract
     "On block identities and block inclusions", pp. 912-913): "There is a unique partition
     κpq of the maximum number (p²−1)(q²−1)/24, which is a p-core and a q-core. It is still an
     open question whether the Young diagram of any other partition which is a p-core and a
     q-core is contained in that of κpq." MathDB's transcription matches literally.
   - **Olsson-Stanton** (author preprint v7, UMN; published Aequationes Math. 74 (2007)
     90-110): Theorem 4.1 = unique max-size core κ_{s,t}; **Proposition 4.5 proves containment
     only for t = s+1**; **Remark 4.11 poses the general question** (the OWR question itself).
     Remark 4.10: β-set set-inclusion does NOT imply diagram containment (the exact trap the
     brief warned about). So O-S did NOT prove the general claim.
   - **Vandehey, arXiv:0809.2134 (2008), Theorem 2.4 "Maximal Theorem" + Sections 4-5:**
     first complete proof in full coprime generality via (s,t)-closure/delta-sets; explicit
     conclusion: every (s,t)-core beta-set satisfies β ≺ β^{s,t} (partition-wise, i.e.
     rowwise), with β^{s,t} the (s,t)-closure of {st−s−t} = beta-set of κ_{s,t}.
   - **Fayers, "The t-core of an s-core", JCTA 118 (2011) 1525-1539, Theorem 5.1
     (+ complete proof, Proposition 5.5):** "Suppose s and t are coprime positive integers,
     and λ is an (s,t)-core. Then [λ] ⊆ [κ_{s,t}]." Independent peer-reviewed proof via the
     affine symmetric group action on alcoves; explicitly "answers a question of Olsson and
     Stanton [OS, Remark 4.11]".
   - Successor confirmations: Aggarwal arXiv:1408.0550 ("answered in the affirmative first by
     Vandehey and later by Fayers independently"); Thiel-Williams arXiv:1508.05293 Thm 1.3
     remark; the brief's cited arXiv:2610.35322 (Aydemir 2026) concerns distinct-parts cores
     only — irrelevant to the target.
4. **Convention cross-check (capped checker, helper guard, PASS).** The explicit maximal
   beta-set {(st−s−t) − as − bt > 0} converts to exactly the κ recorded by the frozen r339
   enumeration for all 15 control pairs, with size (s²−1)(t²−1)/24
   (sources/crosscheck-maximal-beta-set.json). This validates that the published κ_{s,t},
   the MathDB κ_pq, and the frozen finite computation are the same object under the same
   conventions (s-core = no hook divisible by s; β(λ) = {λ_i + ℓ(λ) − i}).

## Disposition: RETIRED — publicly resolved (body-confirmed), credit 0

The MathDB claim is a proven public theorem with the exact quantifiers and the exact
containment order:

- **Theorem (Fayers 2011, JCTA 118, 1525-1539, Thm 5.1; Vandehey 2008, arXiv:0809.2134, Thm
  2.4).** For coprime positive integers s, t (wlog s ≥ 2), every simultaneous (s,t)-core λ
  satisfies [λ] ⊆ [κ_{s,t}], where κ_{s,t} is the unique (s,t)-core of maximal size
  (s²−1)(t²−1)/24 (Olsson-Stanton Thm 4.1). Rowwise: λ_i ≤ (κ_{s,t})_i for all i.
- **Full scope coverage:** min(p,q) ≥ 2 by the theorems; p = 1 or q = 1 is trivial (the only
  1-core is the empty partition — every nonempty partition has a hook-1 corner cell — so
  κ = ∅ uniquely and containment is trivial); p = q = 1 trivial.
- **Chronology:** question 2005/2006 → t=s+1 proved by O-S (Prop 4.5) → full coprime proof
  Vandehey (Sep 2008) → peer-reviewed independent proof Fayers (2011) → standard citation
  thereafter. An empty MathDB solution array is not evidence of openness.

Applicability bridge (retirement is literal, not by size-maximality substitution): MathDB's
κ_pq = O-S/Fayers κ_{s,t} (same beta-set closure, same size formula, cross-checked on 15
pairs); MathDB's "λ_i ≤ (κ_pq)_i for all i" = Ferrers diagram inclusion = Vandehey's
partition-wise order = Fayers' [λ] ⊆ [κ_{s,t}]. No β-set-set-inclusion or path-pointwise-order
shortcut is needed; the retained proofs establish diagram containment directly.

## Deliverables

- `disposition.json` — gate levels: source PRIMARY_BODY_RETAINED; hypothesis
  PUBLICLY_RESOLVED_BODY_CONFIRMED; disposition retired_public_resolution; credit 0.
- `sources/` — 6 retained PDFs with exact URL/UTC/SHA256/size in `sources/provenance.json`,
  including recorded failures (Copenhagen mirror HTTP 000 ×2; Springer published version
  paywalled, not inspected; MathDB network untouched).
- `proof-bodies/` — verbatim extracts: OWR question (p.913), O-S Thm 4.1/Prop 4.5/Remarks
  4.10-4.12, Vandehey Thm 2.4 + abstract, Fayers Thm 5.1 + full Proposition 5.5 proof,
  successor confirmations.
- `work/crosscheck_maximal_betaset.py` + `sources/crosscheck-maximal-beta-set.json` — capped
  convention cross-check (guard-observed; peak RSS ~9 MiB, wall <1 s).
- `manifest.json` + `verify.py` — SHA256+size manifest over ALL payloads (verifier included),
  excluding only manifest.json and verification-receipt.json by exact relative path;
  independent verifier rehashes upstream originals (flat references), retained sources against
  provenance, and the exact payload set; exits NONZERO on any mismatch.
- No Lean, no manuscript, no extended compute, no substitute target. Counts unchanged:
  9 additional / 39 total / next 40.

## Candid notes

- The published-version body of Olsson-Stanton was not inspected (paywall); the author
  preprint v7 was retained and its numbering matches all published-version citations
  ([OS, Remark 4.11]) found in Fayers and Thiel-Williams.
- Fayers' theorem is stated with s ≥ 2 (his standing assumption); the p=1/q=1 edge cases are
  handled here directly, not by citation.
- Vandehey's proof is an arXiv preprint (B.S. thesis); the retirement rests on the
  peer-reviewed Fayers proof, with Vandehey recorded as the first full proof.
