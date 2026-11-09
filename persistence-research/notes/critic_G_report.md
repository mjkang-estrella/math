# Critic G — hostile review of `notes/pure_math.md`

**Reviewer:** G (adversarial). **Method:** every claimed computation re-derived from scratch in
`src/critic_G_checks.py` (stdlib + `src/persistence.py` imported **unmodified** as the reference
DP; full log in `src/critic_G_checks_output.txt`). Nothing below relies on the document's own
certificates.

**Verdict in one line:** the mathematics survives — Theorem C (the centerpiece) has **zero
counterexamples on every range I could test** — but the document contains one real indexing
**[ERROR]** in its Theorem B worked example, one incomplete derivation (the {3,3} deficit
boundary), one broken certificate trail (§3/§6 artifacts do not exist), and three cosmetic slips.

---

## 1. Theorem A (zero-trap)

**1.1 [OK] `10 | m ⟺ a ≥ 1 and c ≥ 1` is airtight.**
For `m = 2^a3^b5^c7^d`: `v₂(m) = a` and `v₅(m) = c` because 3, 5, 7 are odd and none is
divisible by 5; `10 | m ⟺ v₂ ≥ 1 ∧ v₅ ≥ 1`. Both directions verified exhaustively for all
`(a,b,c,d)` with `a ≤ 4, b ≤ 3, c ≤ 4, d ≤ 3` (v₂/v₅ computed by trial division, asserted equal to
`(a,c)` in every case; zero counterexamples). Also verified: `10 | m ⟹ P(m) = 1` for all
multiples of 10 below 20 000, and `P(m) ≥ 2 ⟹ a·c = 0` over all 7-smooth `m < 10⁶`. The proof
in the document is correct as written.

**1.2 [GAP] (cosmetic) "lies in exactly one of two families" is false in the overlap `a = c = 0`.**
`m = 3^b·7^d` is simultaneously in the even family (`a = 0`) and the five family (`c = 0`).
Harmless: the two descriptions then give the *same* digit multiset
(`F(0,b) ∪ {7^d} = {3?} ∪ {9^⌊b/2⌋} ∪ {7^d} = F₅(b,0,d)`), so nothing downstream breaks.
Corrected statement: "…lies in at least one of two families (both, if `a = c = 0`; the two
descriptions then coincide)."

---

## 2. Theorem B (threshold cascade) and §3

**2.1 [OK] The formulas (B1)/(B2) and the τ-table.** I re-derived (B1) independently: from
`P(mᵢ) ≥ 11 − i` and 7-smoothness, `mᵢ ≥ τ_{11−i}`; from `mᵢ₊₁ = Π(mᵢ) ≤ 9^{dc(mᵢ)}` and
`mᵢ₊₁ ≥ τ_{10−i}`, `dc(mᵢ) ≥ ⌈log₉ τ_{10−i}⌉`. (B2) is AM–GM on the digits of `mᵢ` with
`Π(digits) = mᵢ₊₁ ≥ τ_{10−i}`. Both correct. I then **re-certified the τ-table by an independent
exhaustive sweep** of all 7-smooth `m < τ₁₀` (exact `P` on every point):

```
τ₁=10, τ₂=25, τ₃=49, τ₄=378, τ₅=2688, τ₆=27648, τ₇=338688,
τ₈=4478976, τ₉=438939648, τ₁₀=4996238671872
```

`τ₉ = 438939648` ✓ and `τ₁₀ = 2¹⁹·3⁴·7⁶ = 4996238671872` ✓ both match the document;
max `P` strictly below `τ₁₀` is **9** (attained at `τ₉`), and `P(τ₁₀) = 10` — so `τ₁₀` is
minimal exactly as claimed. `9¹³ = 2541865828329 < τ₁₀ ≤ 9¹⁴` ✓, `⌈log₉ τ₁₀⌉ = 14` ✓.
Corrected cascade (i : `⌈log₉ τ_{10−i}⌉`): 0→**14**, 1→10, 2→7, 3→6, 4→5, 5→4, 6→3, 7→2, 8→2, 9→2.

**2.2 [ERROR] The worked example is off by one chain index.** The document states
"`dc(m₁) ≥ ⌈log₉ τ₁₀⌉ = 14`" and "if `D₁ = 14` then `s(m₁) ≥ 114` … the total deficit … over
the 14 digits of **m₁** is at most 12." Per the document's *own* (B1), the bound with `τ₁₀`
belongs to **i = 0**, i.e. to `m₀`:

> **Corrected statement:** `dc(m₀) ≥ ⌈log₉ τ₁₀⌉ = 14`; and if `D₀ = dc(m₀) = 14` then
> `s(m₀) ≥ 14·τ₁₀^{1/14} > 113`, hence `s(m₀) ≥ 114` of a maximum 126, deficit ≤ 12.

*Why the printed claim fails:* `P(m₁) ≥ 10` gives only `Π(m₁) = m₂ ≥ τ₉ = 438939648`, whence
`dc(m₁) ≥ ⌈log₉ τ₉⌉ = 10` — not 14. (The magnitude route `m₁ ≥ τ₁₀` gives only `dc(m₁) ≥ 13`.)
The document's own parenthetical ("a persistence-11 smooth number has at least 14 digits; *its*
digit product must already be a persistence-10 smooth number") confirms the intended referent is
`m₀`; the `m₁`/`D₁` subscripts are a systematic mislabel (both occurrences). The mathematics
survives verbatim after relabeling. Note also the honest caveat: (B1)'s *first* part at `i = 0`
(`m₀ ≥ τ₁₁`) is unusable numerically since `τ₁₁` is exactly the object whose existence is open —
the document wisely only cites `τ₁₀, τ₉, …`.

**2.3 [ERROR] (minor, numeric) `14·τ₁₀^{1/14} = 113.02…`, not 113.05.**
Exact value `113.0248597661551950114…` (Decimal). The conclusion is unaffected
(`113.025 > 113 ⟹ s ≥ 114`; verified `τ₁₀ > (113/14)^14`), but the printed constant is wrong by
0.025. No rounding of τ₁₀ produces 113.05 — it is a plain slip.

**2.4 [GAP] "at most one digit ≤ 3" does not follow from deficit ≤ 12 alone.**
Deficits per digit: 7→2, 6→3, 4→5, ≤3→6+. Seven 7s → 14 > 12 ✓, five 6s → 15 ✓, three 4s → 15 ✓
— but **two 3s → deficit exactly 12 ≤ 12**, so the deficit bound permits `{3,3,9¹²}`. An
exhaustive check confirms `{3,3}` is the *only* profile with ≥ 2 digits ≤ 3 and deficit ≤ 12.
It *is* excluded — but only by the product constraint the sentence omits:
`Π(m₀) = m₁ ≥ τ₁₀ = 4 996 238 671 872` while `Π({3,3,9¹²}) = 9¹² = 282 429 536 481 < τ₁₀`.
> **Corrected statement:** "at most one digit ≤ 3 — the single boundary profile `{3,3,9¹²}`
> allowed by the deficit bound is killed by `Π(m₀) ≥ τ₁₀`." The final conclusion (≤ 1 digit ≤ 3)
> is true; the derivation as printed has a hole. (Theorem D's 𝓕ᵢ correctly uses *both*
> constraints, `∏F ≥ τ_{10−i}` and `|F| = Dᵢ`.)

**2.5 [GAP] (cosmetic) §3's sweep size.** "(≈ 12,700 points for k = 10)": the exact number of
lattice points `(a,b,c,d)` with `2^a3^b5^c7^d < τ₁₀` is **18,050** (my enumeration). 12,700 is
the 4-D simplex *volume* `L⁴/(4!∏ln p)` — an underestimate of the actual count. Cosmetic; the
sweep verdict itself re-verified (see 2.1).

**2.6 [OK] Deficit arithmetic otherwise.** `14·τ₁₀^{1/14} > 113 ⟹ s ≥ 114 ⟹ Σ(9−d) ≤ 126−114 = 12`
✓; "at most six 7s / four 6s / two 4s" all verified (2.4); maximum 14-digit digit sum 126 ✓;
`9¹³ ≈ 2.54×10¹²` ✓. (Theorem D's "dc(F-size) = Dᵢ" is garbled notation for `|F| = Dᵢ` — nit.)

---

## 3. Theorem C — the centerpiece (exhaustively attacked)

**3.1 [OK] C.1 (minimal preimage) is airtight.** The chain in the document's proof is right and I
verify each link: for `n′ < n*` with `Π(n′) = m₀`, `P(n′) = 1 + P(Π(n′)) = 1 + P(m₀)` and
`P(n*) = 1 + P(Π(n*)) = 1 + P(m₀)`, so `P(n′) = P(n*) ≥ 12`, contradicting `n* = min{n : P(n) ≥ 12}`;
hence `n*` is *the* minimal preimage of `m₀`. Since `P(m₀) ≥ 11 ⟹ m₀ ≥ τ₁₁ ≥ 10`, `Π(n′) = m₀ ≥ 10`
forces `n′ ≥ 10` and F1 applies; preimages contain no 0 (`Π ≠ 0`) and no 1 (deleting a 1
preserves Π and strictly lowers the value); fewer digits ⟹ smaller number (`< 10^{L−1}` vs
`≥ 10^{L−1}`); equal length ⟹ sorted arrangement is smallest; equal length ⟹ lex-smaller sorted
multiset is smaller. No gap found.

**3.2 [OK] C.2 case table — product and length, `a ≤ 60, b ≤ 40` (the brief's test).**
For every `(a,b)` in range: `∏F(a,b) = 2^a·3^b` (**0 mismatches**) and `|F(a,b)| = len23(a,b)`
from `src/persistence.py`'s DP (**0 mismatches**). Bonus finding: `len23(a,b) = ⌈a/3 + b/2⌉`
holds at **every** tested pair — the LP bound (`α/3 + β/2 ≤ 1` per digit, so
`L ≥ ⌈a/3 + b/2⌉`) is always *achieved* by the table's construction. This proves the length
claim in one line and shows the document's lengths are exactly optimal.

**3.3 [OK] C.2(iii) min-lex — full brute force, `a ≤ 12, b ≤ 8` (the brief's test).**
I enumerated **all** factorizations of `2^a3^b` into digits {2,3,4,6,8,9} for all 117 pairs,
computed the min-length set and its lex-minimum, and compared with the table:
**0 mismatches.** Targeted probes from the brief:

| (a,b) | value | min-length multisets (all) | lex-min | table | match |
|---|---|---|---|---|---|
| (2,1) | 12 | {2,6}, {3,4} | (2,6) | (2,6) | ✓ (lengths equal; {2,6} ≺ {3,4}) |
| (7,0) | 128 | {2,8,8}, {4,4,8} | (2,8,8) | (2,8,8) | ✓ ({2,8,8} ≺ {4,4,8}) |
| (5,1) | 96 | {2,6,8}, {3,4,8}, {4,4,6} | (2,6,8) | (2,6,8) | ✓; `len23(5,1)=3` (DP + brute) |
| (4,1) | 48 | {6,8} | (6,8) | (6,8) | ✓ |
| (1,1),(2,0),(1,0),(0,1) | 6,4,2,3 | singletons | — | — | ✓ |

**3.4 [OK] C.2 min-lex at the certificate's full range, `a ≤ 240, b ≤ 160`.**
Independent method: DFS over nondecreasing digit sequences of exactly `len23(a,b)` digits with
*exact* pruning (`len23(ra,rb) > r` or `ra+rb < r` ⟹ no completion), first leaf = lex-min.
Compared against the closed form on all **38,801** pairs: **0 mismatches** (0.7 s). This
reproduces the verdict of `results/minlex_certificate.md` by a different algorithm.

**3.5 [OK] C.2(d) record-setter consistency.** `F(19,4) = {2, 8⁶, 9²}` (19 ≡ 1 mod 3, 4 ≡ 0 mod 2);
`{7⁶} ∪ F(19,4) = {2,7⁶,8⁶,9²}` = exactly the digits of 277777788888899 ✓;
`Π(277777788888899) = 2¹⁹·3⁴·7⁶` ✓; `len(m₀) = 6 + len23(19,4) = 15` ✓. Note (19,4) admits
*five* min-length multisets — `(2,8⁶,9²) ≺ (3,6,8⁶,9), (4,4,8⁵,9²), (4,6²,8⁵,9), (6⁴,8⁵)` — and
the table correctly picks the lex-min.

**3.6 [OK] "≤ 2 digits outside {7,8,9}" for small `a,b` too.** Worst case is `a ≡ 2, b ≡ 1`
(exactly `{2,6}`); every other class has ≤ 1 small digit; `(0,0)` has none. Verified across the
whole tested ranges — including `a = 0` (`{3}`/`{9^k}`), `a=1,b=0` `{2}`, `a=2,b=0` `{4}`,
`a=1,b=1` `{6}`, `a=2,b=1` `{2,6}`, `a=4,b=1` `{6,8}`, `a=5,b=1` `{2,6,8}` — all as the brief
requested. No small-case exception exists.

**3.7 [OK] C.3 five family.** Brute-forced all `(b ≤ 8, c ≤ 4, d ≤ 4)`: digits of the minimal
preimage of `3^b5^c7^d` are exactly `{3 (b odd)} ∪ 5^c ∪ 7^d ∪ 9^⌊b/2⌋` (**0 mismatches**).
5s and 7s are forced digits; no even digit can appear (m₀ has no factor 2); `3^b` needs
`⌈b/2⌉` digits from {3,9}, unique at min length; ≤ one 3 ✓.

**3.8 [OK] Consequence.** With C.1–C.3 the minimal counterexample is parametrized by `(a,b,d)` /
`(b,c,d)` with digits in {7,8,9} up to ≤ 2 exceptions — as claimed.

---

## 4. Theorem E and the final-gap section

**4.1 [OK] Senge–Straus direction and statement are correct.** The chain: `2^n` has exactly one
nonzero binary digit (always); if `2^n` had ≤ C nonzero decimal digits for infinitely many n,
its base-10 digit sum would be ≤ 9C and its base-2 digit sum = 1 — both "below a fixed bound" —
contradicting Senge–Straus for the multiplicatively independent pair (10, 2). This matches the
**verbatim survey quote** in `notes/literature.md` (line 72), which states S–S in precisely the
digit-sum form the document uses: *"the number of integers, the sum of whose digits in each of
the bases a and b lies below a fixed bound, is finite if, and only if, a and b are
multiplicatively independent."* The nonzero-count reading (≤ C nonzero digits in both bases)
is also fine: bounded count ⟹ bounded digit sum, so the contradiction goes through under either
formulation. The document is also right that S–S gives **no** zero-forcing (upper-bound)
statement — that is correctly identified as the open gap.

**4.2 Precision notes (not errors).** (i) Per the same literature.md quote, S–S's proof "rests
on the Thue–Siegel–Roth theorem and, hence, is **ineffective**"; the effective version is
**Stewart's** (Baker linear forms). `theory.md` §8's parenthetical "(effective, via Baker's
theory)" should therefore attach to Stewart alone; `pure_math.md`'s collective
"Senge–Straus/Stewart machinery" is acceptable but could be sharper. (ii) The digit-sum gloss
is one step compressed (count ≤ C ⟹ sum ≤ 9C, so the S–S bound must be taken at 9C) — valid,
worth a footnote.

**4.3 [OK] Theorem E's machinery matches the verified literature.** The displayed shape
`2^h·(10^{a₀} + 18·Σ cᵢ·10^{aᵢ}) + τ_h = 3^u·7^w` is exactly the BCGN equation shape quoted
verbatim in literature.md (line 45). "A member n … is 7-smooth iff `n = 2^A·3^B·7^D`" is correct
for these families: the fixed multiset `{7^d} ∪ F(a,b) ∪ 1^j` contains no 0 and no 5, so
`5 ∤ n`, and a 7-smooth n has no prime factor outside {2,3,7}. (★)'s equivalence with
"every 7-smooth has P ≤ 10" is theory.md Corollary 1.1; the `a·c = 0` side-condition is
automatic for `P ≥ 11` by Theorem A, so the two formulations of (★) agree.

---

## 5. Cross-document consistency

**5.1 [OK] `theory.md` Lemma 4 vs Theorem C's `{2,6}` case.** Lemma 4.4's forbidden pairs are
{2,3}, {2,4}, {3,4}, {3,6}, {4,6} — **{2,6} is not forbidden** (it survives as the lex-min of
{2,6}/{3,4}), and Lemma 4.3's "at most one 2/3/4/6" is respected by every class of the C.2
table (a≡2,b≡1 has one 2 and one 6; all others ≤ 1 small digit). The C.2 table and Lemma 4 are
mutually consistent — indeed the table's multisets satisfy every Lemma-4 constraint
(no 0/1, sorted, ≤ one each of 2,3,4,6, no forbidden pair). Lemma 4's replacement facts were
also re-checked: {2,2}→4, {3,3}→9 (shorter), {4,4}→{2,8}, {6,6}→{4,9}, {3,4}→{2,6},
{3,6}→{2,9}, {4,6}→{3,8}, {2,9}→ kept over {3,6}, {2,8} kept over {4,4} — all correct.

**5.2 [OK] `results/*.md` agree with my independent sweep.** `results/redteam_results.md`'s
frontier table — 4996238671872 = (19,4,0,6), len 15, P 10; 937638166841712 = (4,20,0,5), len 17,
P 10; 438939648 = (12,7,0,2), len 10, P 9 — matches my τ-sweep exactly, and
`Π(937638166841712) = 438939648` ✓ (both P = 10 smooths map to τ₉).

**5.3 [ERROR] §3 and §6 cite artifacts that do not exist.** `results/threshold_certificates.json`
(§3, "subagent E") and `results/fonga_verification.md` (§6, "subagent F") are **absent** from
`results/`; "subagent E"/"subagent F" appear nowhere in the repository outside pure_math.md
itself (README's team is lead + A, B, C, D). Only `results/minlex_certificate.md` exists — and
it was written *after* pure_math.md (13:39 vs 13:03), so at writing time §5's citation was also
unbacked. The document therefore presents three "certificate-level verifications" of which two
have no artifact and one was retroactively created.
*Minimal corrected statement:* either commit the two missing artifacts or re-point §3/§6 to the
checks in `src/critic_G_checks.py` (which re-derive both claims — see 2.1 and §6 below — so the
*mathematics* is not in doubt, only the provenance).

**5.4 [OK] `results/minlex_certificate.md` itself.** Its verdict (0 length mismatches; 0
lex mismatches on `a ≤ 240, b ≤ 160`; brute spot check `a ≤ 12, b ≤ 8`) is independently
reproduced here (3.3/3.4). Its constraint argument is sound (c₂ ≤ 2, c₃ ≤ 1, c₄ ≤ 2, c₆ ≤ 3,
¬(c₂ ∧ c₄): each violation admits a shorter or equal-length-lex-smaller replacement). One
cosmetic slip inside it: "38,880 nontrivial pairs" — the true count is **38,800**
(241·161 − 1; 38,801 including (0,0)).

---

## 6. Bonus: §6 (Fonga) verified **in full**, beyond the document's `j ≤ 40`

* All arrangements of `{4,4,7} ∪ {1^j}` for `j ≤ 60` (≈1.9×10⁶ numbers, distinct-permutation
  generation): **max v₂ = 7, attained at 111744 = 2⁷·3²·97** (v₂ = 7) — matches the cited
  Fonga Thm 4.1 exactly.
* **Complete proof for all j** (stronger than the doc's `j ≤ 40`): `v₂(n) ≥ 8 ⟺ 256 | n`.
  For `n` with ≥ 8 digits (j ≥ 5) this depends only on the last-8-digit suffix S, which must be
  a sub-multiset of `{4,4,7,1^j}` (≤ 2 fours, ≤ 1 seven). Enumerating **every** such 8-digit
  suffix for every j (constraint classes stabilize at j = 8; checked to j = 200): **none is
  divisible by 256**; and no ≤ 7-digit member (j ≤ 4) is divisible by 256. Hence
  `v₂ ≤ 7` over the *entire* infinite family, with equality at 111744. The document's claim in
  §6 is true; only its artifact is missing (5.3).

---

## Summary of defects (with minimal fixes)

| # | Severity | Location | Defect | Fix |
|---|---|---|---|---|
| 1 | **[ERROR]** | Thm B example | `dc(m₁) ≥ ⌈log₉ τ₁₀⌉ = 14` and `D₁ = 14 → s(m₁) ≥ 114, deficit of m₁ ≤ 12` | Relabel to `m₀`/`D₀`: `dc(m₀) ≥ 14`; `s(m₀) ≥ 114`. True i=1 bound is `dc(m₁) ≥ ⌈log₉ τ₉⌉ = 10` |
| 2 | **[ERROR]** | Thm B example | `= 113.05` | `= 113.0249` (conclusion `s ≥ 114` unchanged) |
| 3 | **[GAP]** | Thm B | "at most one digit ≤ 3" from deficit ≤ 12 alone | `{3,3,9¹²}` has deficit 12; exclude it via `Π(m₀) = m₁ ≥ τ₁₀ > 9¹²` |
| 4 | **[ERROR]** | §3, §6 | `threshold_certificates.json`, `fonga_verification.md` absent; "subagent E/F" nowhere else | Commit artifacts or repoint to `src/critic_G_checks.py` |
| 5 | [GAP] | Thm A | "exactly one of two families" | "at least one (both iff a = c = 0; descriptions then coincide)" |
| 6 | [GAP] | §3 | "≈ 12,700 points" | exact count 18,050 (12,700 is the simplex volume) |
| 7 | (nit) | Thm D | "dc(F-size) = D_i" | "\|F\| = D_i" |
| 8 | (nit) | Thm E / theory.md §8 | effectiveness attribution | S–S 1973 ineffective (Ridout); effective = Stewart 1980 (Baker) |

**What I could not break:** Theorem A (both directions), Theorem B's formulas and τ-table
(independently re-swept), the entire Theorem C case table — product, length, and lex-minimality
on `a ≤ 12/b ≤ 8` (full brute force), `a ≤ 60/b ≤ 40` (DP), and `a ≤ 240/b ≤ 160` (exact-pruned
DFS, 0/38,801 mismatches) — the record-setter instance, the five family, the Senge–Straus
implication, the BCGN/Fonga citations against literature.md's verbatim quotes, and the Fonga
`v₂ ≤ 7` family claim (now proved for **all** j). Theorem C is, as of this review, the
best-checked object in the repo.

*Artifacts: `src/critic_G_checks.py` (all checks), `src/critic_G_checks_output.txt` (full log).
`src/persistence.py` used read-only, unmodified.*
