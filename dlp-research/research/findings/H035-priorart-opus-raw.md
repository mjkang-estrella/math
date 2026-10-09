# H035 review: prior art and competent baselines for hash fusion (read-only)

**Verdict.** The algebra holds, and fusing the hash into the curve arithmetic does save M+A/key against the H034/H019 comparator, which pays a separate field multiply per key to hash. But that comparator is not a competent baseline. Standard ECDLP practice uses bits of the canonical coordinate as the table index and pays no hash multiply. Against that, the saving is **zero**. What fusion buys is a collision guarantee that does not depend on how the points are distributed, at no extra arithmetic per key. Main ECDLP improvement: **NONE**.

I read `H034-matched-memory-cost-screen.md`, `H019-xonly-baseline-screen.md`, `H033-primary-audit-corrections.md`, the existing `H035-shared-hash-fusion-screen.md`, and protocol lines 128–140. I edited nothing and ran no code. The only shell work was downloading PDFs into `/tmp/h035lit.gQNd` and running `pdftotext` on them.

## 1. My own derivations (not from the literature)

- **The proposal checks out.** w± = θλ± and K± = κw±² + C = η·x(P_i±P_j) + ζ. My counts match yours: fused (5b−3)M + 2bS + 7bA + I against separate (7b−3)M + 2bS + 8bA + I. The square-only isomorphism formula X_sum = slope² − X_i − X_j + 3ζ also checks (the new curve has a₂ = −3ζ).
- **The 7A count is not minimal; 6A per pair is reachable.** Store a shifted coordinate X = ηx + r (θ-scaled Y as before) and use X − 3r as the key instead of X. Then K = κw² − (X_i + X_j) = η·x_sum − 2r. With r = −ζ/2, that is exactly the frozen protocol's ηx + ζ. When κ = −1, use −K = w² + s instead. That is the same hash with multiplier −η, which is still uniform, so key equality is preserved.
  - Per-pair cost: d, two numerators, s, two outputs. That is the raw unhashed 6A kernel exactly.
  - Saving against the separate hash becomes M+A/key. The extra cost against the raw kernel is zero per side key.
  - Only centers pay one extra A, for their own key and for the +3r in full additions. That is lower order under H019's block schedule.
  - The same fold applies to the square-only variant (key = X + a₂).
  - Please check this independently.
- **Generic ν.** A fully random ν costs M per key in the e=1 branch. If ν is a small integer, multiplying by it costs much less than a general M. Bernstein–Lange–Schwabe (BLS) price exactly this kind of small-constant multiply, but only on their platform; it is not a general rate.
- **Square-only multipliers when p ≡ 1 mod 4.** I hand-checked Astra's counterexample (p=5, H=2, δ=2 gives 12/20 = 3/5). My sketch: Burgess-type character-sum bounds might give 1/H·(1+o(1)) when H ≈ √p. I have not verified this and nothing above depends on it.
- **Equivalence with the frozen protocol.** The exact-uniform fused key, with or without the shift fold, equals the protocol's (ηx+ζ mod p) mod Hc. The bucket function can therefore be identical and only the arithmetic changes. The square-only variant uses a different multiplier distribution, so it would not be protocol-identical.

## 2. Literature, and what each source shows

- **Thorup, "High Speed Hashing for Integers and Strings," arXiv:1504.06804.** I read the text.
  - §2.2, pp. 3–5: the Carter–Wegman family ((ax+b) mod p) mod m, a≠0, with Pr < 1/m strictly. The H034 comparator is exactly this family.
  - §2.3, pp. 6–7: Dietzfelbinger et al.'s multiply-shift is 2-approximately universal, and is "an order of magnitude" faster than the Carter–Wegman version.
  - §3.3, pp. 12–13: multiply-add-shift is strongly universal.
  - §3.4–3.5, pp. 13–15: vector multiply-shift is strongly universal, with collision probability exactly 1/2^ℓ. Pair-multiply-shift halves the number of multiplications.
  - §4: reducing to a range that is not a power of two costs extra.
- **Pătraşcu–Thorup, "The Power of Simple Tabulation Hashing," arXiv:1011.5200v2,** introduction around p. 2. Simple tabulation is 3-independent, its tables fit in cache, and bins are understood to be a power of two.
- **Joye–Tymen, CHES 2001, LNCS 2162 pp. 377–390.** Author copy `JT01edpa.pdf`.
  - Corollary 1 and Algorithm 1, pp. 4–5: scalar multiplication on a random isomorphic curve via (x,y) ↦ (u²x, u³y).
  - Proposition 2, p. 11, citing Menezes: the general admissible change of variables (u, r, s, t), with the a₂′ relation.
  - So computing in a randomly chosen isomorphic model is published prior art, as a side-channel countermeasure. The only part I cannot place in prior art is using that randomness as the hash seed. **That is not evidence of novelty.**
- **Bernstein–Lange–Schwabe, "On the correct use of the negation map in the Pollard rho method,"** author version 2011-01-02 from cr.yp.to.
  - pp. 12–13: because representations are redundant, they canonicalize. They compute s = 76439·y mod (2¹²⁸−3), a *fixed* multiplier folded into the required reduction. They extract bits of s as the table index and to define distinguished points; there is no universal hash.
  - p. 14: canonicalization costs 24.75 of 306.08 arithmetic instructions, against 43.75 per multiplication. They report that Bos et al. used Montgomery reduction for canonicalization.
  - This is the closest prior art: a key built from bits of a scaled canonical representative, with the multiplier folded into work that has to be done anyway. It is not randomized.

## 3. Does a cheaper word hash already beat the named comparator?

- **Yes.** Raw canonical bits (cost 0), multiply-shift, vector or pair multiply-shift (d or d/2 word multiplies on the 256-bit canonical key), and tabulation (c lookups) all avoid the field multiply.
  - Vector multiply-shift with power-of-two buckets even gives exactly 1/2^ℓ, which matches the guarantee H034 relies on independently of the point distribution.
  - Comparing these against field M or A is a hardware question. It cannot be settled in the field-M ledger.
- **In operation count, the shift-folded fused key weakly beats every separate word hash.** It costs nothing extra beyond the raw kernel; any separate hash costs more than zero.
  - Canonical reduction is common to all of them, because exact equality needs it.
  - Montgomery form is harmless: it is the same hash with multiplier ηR.
  - The protocol's Hc is a power of two, so bucket reduction is a mask.
- **Consequence for H034, by deduction.** Both arms pay the M+A hash, so the stronger baseline lowers g for both. In the gate [(1−f)b−a]·gB > aΔ + fzh, the candidate's margin scales with gB while Δ and fzh do not change. So this common-mode improvement *tightens* the candidate gate. It does not help the candidate.

## 4. Scope and the next decisive paper test

- **Scope.** Fusion is a shared arithmetic and analysis convenience that every comparator can adopt (H019, the candidate, rho-style tables). It gives no speed advantage over standard canonical-bits practice and is not specific to any attack.
- **Next test (paper only).**
  1. Independently confirm the 6A shift-fold algebra and its center and setup charges.
  2. Recompute the H034 gate with gB stripped of M+A on both arms, under three key options: (a) raw canonical bits, (b) the fused folded key, (c) vector multiply-shift with symbolic word prices.
  3. Report whether the candidate's margin survives (b) as the competent comparator. This is about interpreting the ledger only; the frozen source and protocol stay unchanged.

## Access limits

- IACR ePrint returned a Cloudflare 403, so I used author copies. The BLS copy is a January 2011 version and may differ from the PKC text.
- I did not read the original Carter–Wegman 1979 or Dietzfelbinger 1996/1997 papers; their statements above come via Thorup's notes.
- I did not read Silverman. I derived the general-Weierstrass addition formula myself; Joye–Tymen supply only the change of variables.
- I did not touch or duplicate the Fable source-cost audit.

Sources:
- [Thorup arXiv:1504.06804](https://arxiv.org/abs/1504.06804)
- [Pătraşcu–Thorup arXiv:1011.5200](https://arxiv.org/abs/1011.5200)
- [Joye–Tymen author copy](https://marcjoye.github.io/papers/JT01edpa.pdf), [CryptoDB record](https://www.iacr.org/cryptodb/data/paper.php?pubkey=667)
- [BLS author copy](https://cr.yp.to/elliptic/negation-20110102.pdf), [ePrint 2011/003](https://eprint.iacr.org/2011/003) (403)
