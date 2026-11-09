# abelian-square-execution-pi-r1 — execution handback (task 330695)

**Zero accepted credit; campaign count unchanged at 52/60 beyond 39 prior. No candidate
nominated. No Lean endpoint claimed. No shared file, ledger, git, publication, upload,
external message or browser/account action.** All 351 frozen r253 inputs verify before
and after (`receipts/frozen-before.json`, `receipts/frozen-after.json`: 351/351 ok).

## 1. Source gate — PASS (details: `source-gate.md`)

- Journal body recovered: TCS 2017 DOI 10.1016/j.tcs.2017.02.012 =
  arXiv:1701.00948 (Fici–Mignosi–Shallit revision of 1506.03562); **Conjecture 27 read
  in the actual body**, verbatim as the MathDB statement. ScienceDirect PDF 403 once
  (recorded, not retried); body taken from the author camera version, conjecture
  numbering and text confirmed.
- Both known versions + printed tables/examples read (Thue–Morse Table 1, Fibonacci
  Table 2, Examples 15/18; §5 distinguishes the Parikh-class variant, Conjecture 28 —
  confirming the literal distinct-STRING counting used here).
- Triki 1907.05369 full proof: induction covers only last-letter repetition; gap
  re-confirmed; not a resolution.
- All 8 citing works 2018–2026 screened: no proof/refutation of Conjecture 27.
  Registry heads equal r253 values (openai 4eaee875…, omega 5ea4a916…, pool 01db1d70…);
  Omega `abab` body is a lower-bound equality result, a different question.

## 2. Exact checker (validated)

`scripts/abecount.py`: distinct abelian-square factors counted on literal strings.
Method A (prefix-count) vs method B (brute force): 300-random plus **all 2^n words for
n ≤ 9** cross-checked, 0 mismatches; n=20 maxima re-verified with method A.

## 3. Exact binary maxima — complete coverage, n ≤ 20

`scripts/exhaustive_bin.py`; invariance under complement/reversal; canon = unique orbit
minimum, idempotent ⇒ every binary word counted exactly (orbit census recorded, e.g.
n=20: 1,048,576 words, 262,656 orbits; CPU 3.8 s, RSS ≤ 12 MiB).

| n | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 | 20 |
|---|-|-|-|-|-|-|-|--|--|--|--|--|--|--|--|--|--|--|--|
| max | 1 | 1 | 2 | 3 | 4 | 5 | 7 | 9 | 11 | 13 | 15 | 17 | 21 | 23 | 26 | 30 | 34 | 38 | **43** |

Unique n=20 maximizer `00101000100100001100` (43), independently re-verified.

## 4. k-ary diagnostics — no finite obstruction found (n ≤ 20)

- Exact exhaustion: ternary n ≤ 13 and quaternary n ≤ 11 maxima are **identical** to the
  binary maxima at every n (17 at n=13 ternary; 13 at n=11 quaternary).
- n=20 bounded searches (hill-climbing, logged restarts, NOT exhaustive): ternary best
  43 = binary max (3 seeds; one seed rediscovers the binary maximizer as a ternary
  word); quaternary 42; quinary 43. **No k-ary word inspected exceeds the exact binary
  maximum at any n ≤ 20** ⇒ the conjecture survives all diagnostics here; no witness
  obstruction exists to formalize.
- Resource record: every call ≤ 35 s CPU / 2 CPUs, peak RSS 33 MiB, single-threaded,
  no background processes; failures and fixes in `logs/COMMANDS.txt`.

## 5. Precise Pi Lean endpoint plan (NOT executed — no obstruction exists)

A literal endpoint for 330695 requires one of:

1. **Refutation route** (only if a finite obstruction is later found at some n): a
   witness word w over alphabet k with the **exact maximum over ALL k^n words** proved,
   plus a complete binary upper-bound certificate. The k^n maximum for n ≤ 20 is
   obtainable by the same orbit-enumeration decidable check (`Finite.toFinset` style
   brute force is 2^20-decidable but the k^n space for k ≥ 3, n = 20 is 3^20 ≈ 3.5e9 —
   requires the orbit/quota reduction or a SAT certificate; see 3b).
2. **Proof route** (conjecture true): no known complete induction (Triki's gap is the
   only public attempt). A candidate lemma — suffix-profile extension preserving the
   distinct-square set — has no proved compression to binary; formalizing it is a
   research-grade endpoint, out of diagnostic scope here.
3. If either is obtained: definitions bridge (word = List α, factor = substring,
   distinct = nodup over literals — never Parikh classes), `#print axioms` limited to
   propext/Classical.choice/Quot.sound, Lean 4.34.1 + mathlib d13f23 pinned, no
   sorry/admit/native_decide. **No formalization was started** since no obstruction or
   proof candidate survives the diagnostics.

## 6. Deliverables

`source-gate.md`; `results/330695-results.json` (ID-keyed); `results/*.json` scans;
`scripts/{frozen_check,abecount,exhaustive_bin,kary}.py`; `logs/` (all runs, times,
peaks, failed attempts); `receipts/` (frozen before/after, `HASHES.json` manifest of 56
lane files, `receipts/http/` fetch receipts incl. the 403s). Frozen inputs verified
351/351 before and after; no acceptance or count changes made.
