# CHECKPOINT — crown-vnumber-formal-pi-r6

UTC markers are local-session wall times; see file mtimes.

## 2026-11-06 (session start)

- Bootstrap executed FIRST as exact command; receipt `bootstrap-receipt.json`
  immutable (affinity [0,1], CPU 10s, AS 512MiB, 4 reads).
- Frozen inputs: **429/429 OK** before math reads → `frozen-verify-before.json`.
- Root integration r5 read: 6 baseline strict exit0; CrownVClass2 EXIT1
  (6 errors, sha 605e49dd…); no new module; no summary/results/manifest.
- Copied 6 baseline sources from completed r5 `src/` only; hashes match root
  record exactly (verified above).
- Created SUMMARY.md, CHECKPOINT.md, results/369163.json (PARTIAL).

## Runner repair plan (concrete defects from r5 root integration)

1. DEVGUARD_S=130 never used → implement actual sub-140s development guard:
   hard group kill at DEVGUARD below 140 plus outer hard cap that reaps
   descendants (kill process group, waitpid leader and children).
2. max(0.05,…) sleep permits deadline overshoot → compute remaining budget,
   no positive-floor slack past the cap.
3. cpu_sample=0 constant → record getrusage(RUSAGE_CHILDREN) before/after
   delta per run; label measured vs unavailable honestly.
4. Runner performs file reads before own caps → install affinity+rlimits at
   runner start (Python -I -B) before any source read.
5. Final sweep must guarantee leader wait + descendant reap; never pipe
   failure exit through tail (receipt preserves true exit; summary print
   allowed after preservation).

## Build ledger (r6)

| module | sha256(8) | receipt | exit |
|---|---|---|---|
| (none yet in r6) | | | |

## Next

1. Repair runner; demonstrate wrapper test with true receipt.
2. Read r5 last Class2 log + probe2 trace; fix the six errors using actual
   recursor case signature; verify byte changes; single rebuild.
3. Then substantive: component-count equivalence theorem, full classification,
   algebra chain per SUMMARY unpaid bridges.

## 2026-11-06 (bridge compiled)

- Runner repaired (dev-guard 130 wired, no positive-floor overshoot, guaranteed
  leader waitpid + group reap, live /proc CPU sample + getrusage delta, self
  caps before reads, no tail-piping). Wrapper demonstrated: CrownVGraph exit0
  receipt 1793958003095112034; fault-probes exit1 receipts preserved.
- All six baseline modules rebuilt exit0 in r6 (receipts 1793958439-444687...).
- CrownVClass2 rewritten: sameC_ins_split fixed via probed `tail` case shape
  (3 binders: path, edge, ih; endpoint is the new c); probe3/4 receipts kept.
- **CrownVClass2 EXIT0** receipt 1793960981533881867, sha ad5138dd....
  New kernel theorems: comp_eq, sameC_last, sameC_snd_mem, sameC_H_to_s,
  comp_H_closed, sameC_ins_split, pickElem/pickElem_mem,
  **vcut_ccnt_left, vcut_ccnt_right, vcut_ccnt_iff** — the path-form
  cut-vertex definition is now kernel-equivalent to
  `ccnt (insert t s) < ccnt s` for `t ∉ s`. The r4/r5 comment-only obligation
  is discharged with `NeZero n` side condition (n ≥ 1; classification uses
  n ≥ 4).
- Next: full cut-set classification (families are Cutsets; converse), then
  algebra chain.

## HANDBACK (2026-11-06, after bridge compile)

State: PARTIAL, honest. Frozen 429/429 before AND after
(frozen-verify-before/after.json). No sorry/admit/axiom/unsafe in src/
(CrownVClass2 uses only Classical.choice via pickElem/finiteness; count
verified in results). All builds via check.sh; every claim above has a
receipt in receipt/ with true exit.

### Concrete next steps (mathematics worked out, not yet formalized)

1. Classification => (the endpoint gate). With S = univ \ T, A = Xside n ∩ S,
   B = Yside n ∩ S:
   - A = ∅ (T ⊇ X): any t = b_j ∈ T ∩ Y has H = S ∪ {b_j} ⊆ Y ∪ {b_j}, which
     contains no X point, so no two distinct b's are H-connected (b-b
     non-edges, no a) => VCut fails => T ∩ Y = ∅ => T = Xside n (family
     fullX). Mirror: B = ∅ => T = Yside n.
   - A = {i} singleton: for t = b_j ∈ T ∩ Y one shows no witness pair exists
     (a-pairs need two surviving a's; a_i-b_k pairs are S-connected when
     k ≠ i; a_i,b_i not H-connected since b_i meets no H neighbor), forcing
     T ∩ Y = ∅ => T = Xside ∖ {a_i} (family delX i). Mirror delY.
   - |A| ≥ 2 and |B| ≥ 2: t = a_k ∈ T ∖ X? analysis forces T ∩ X, T ∩ Y
     complements of exactly two indices each, equal: T = univ ∖ {a_i,a_j,b_i,b_j}
     (family mix i j). The witnesses are the two b_i,b_j (S-unconnected since
     only edges a_i-b_j, a_j-b_i exist inside the 4-set) joined through t.
2. Classification <= (optional for the endpoint): each famCut is a Cutset for
   4 ≤ n. Needs helper exists_two_ne (hn : 3 ≤ n) (i : Fin n) :
   ∃ j k, j ≠ k ∧ j ≠ i ∧ k ≠ i (case on i.val ∈ {0,1,2} vs ≥3, omega on
   Fin.val); witnesses per family: fullX b_j,b_k ∉{i} via a_i; delX b-pair
   via a_i (b-pairs are never S-connected in {a_i} ∪ Y); mix b_i,b_j via t
   itself. fullY/delY mirror by hand (or a vswap transfer lemma).
3. Algebra on the actual J (CrownVAlg) and Pc (compMinors! not a family list):
   separator/reduction lemma, then per family prime the colon exclusions for
   homogeneous degrees 0..3 (char-2 care on the full-side cubic: two
   primitive nonassociate quadrics), quartic witnesses, VIs assembly.
4. Endpoint audit per the inherited spec; zero acceptance claims in this lane.

Budget note: r6 spent its window on runner repair + the blocked Class2 + the
new component-count bridge; classification/algebra are untouched new modules.
