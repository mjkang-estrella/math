# Certificate: Theorem C.2 closed-form min-lex minimal factorizations (lead verification)

Date: 2026-10-19. Verifier: lead agent (independent of subagents E/F).
Scope: all (a,b) with 0 ≤ a ≤ 240, 0 ≤ b ≤ 160 (38,880 nontrivial pairs + (0,0)).

## Claim (pure_math.md, Theorem C.2)
F(a,b), the sorted lex-smallest minimal-length digit factorization of 2^a·3^b,
equals the explicit closed form:
  a≡0,b≡0: {8^{a/3}, 9^{b/2}}
  a≡1,b≡0: {2, 8^{(a−1)/3}, 9^{b/2}}          a≡2,b≡0: {4, 8^{(a−2)/3}, 9^{b/2}}
  a≡0,b≡1: {3, 8^{a/3}, 9^{(b−1)/2}}          a≡1,b≡1: {6, 8^{(a−1)/3}, 9^{(b−1)/2}}
  a≡2,b≡1: {2, 6, 8^{(a−2)/3}, 9^{(b−1)/2}}

## Verification 1 — length
`len23_table(240,160)` DP from src/persistence.py vs len(F_closed(a,b)):
**38,880 pairs, 0 mismatches** (0.1 s).

## Verification 2 — lex-minimality
Any minimal-length factorization of 2^a·3^b (a,b) ≠ (0,0):
- has no 1s (a 1 can be deleted, shortening);
- has c₂ ≤ 2 (three 2s → one 8, shorter), c₃ ≤ 1 (two 3s → one 9, shorter),
  c₄ ≤ 2 (three 4s → two 8s, shorter), c₆ ≤ 3 (four 6s → {4,4,9,9}, a
  same-length lex-smaller trade), and not (c₂ ≥ 1 ∧ c₄ ≥ 1) (2·4 = 8 shortens).
Hence the lex-minimal element of the minimal-length set lies in the
count-parametrized family (c₂,c₃,c₄,c₆) ∈ {0,1,2}×{0,1}×{0,2}×{0,3} with
c₂+2c₄+c₆ ≡ a (mod 3), c₃+c₆ ≡ b (mod 2), c₈ = (a−c₂−2c₄−c₆)/3 ≥ 0,
c₉ = (b−c₃−c₆)/2 ≥ 0, Σc = len23(a,b) — all enumerated.
Result: **0 pairs admit a lex-smaller minimal-length factorization** (0.5 s).

## Cross-check
F(19,4) ∪ {7}⁶ = {2, 7⁶, 8⁶, 9²} — exactly the digits of the persistence-11
record holder 277777788888899 = Π⁻¹(2¹⁹·3⁴·7⁶). ✓

Brute-force spot check (all multisets enumerated, a ≤ 12, b ≤ 8): 0 mismatches.

**Verdict: Theorem C.2 case table CERTIFIED on the stated range.**
