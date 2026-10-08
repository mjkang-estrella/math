# Unaccepted raw delegated review

Retained verbatim for provenance; coordinator dispositions supersede overclaims. This is not a verified ECDLP result.

I reproduced the root's derivation and checked it on two tiny curves. The printed eq. (4) is a misprint, and the formula from my previous round is wrong by one global factor of c. The conclusions that matter survive, though some odd-product signs change and three of my own claims needed correcting.

## 1. Corrected formula

**Definition (3)** of arXiv:0803.0728v2, page 5: φ(P) = (W(q−1)/W(q−1+m))^{1/m²}, with m = ord(P) and gcd(m, q−1) = 1.

**Derivation.** Start from the Theorem 6 identity W_{[n]P}(l)·W_P(n)^{l²} / W_P(l)^{n²} = W_{[l]P}(n). Put l = q−1 and then l′ = q−1+m. Both give the same right-hand side, because [l]P = [l′]P, so their left-hand sides are equal:

 φ(nP)^{m²} = φ(P)^{m²n²} · W(n)^{l′²−l²}, where l′²−l² = m(2(q−1)+m).

Take the unique (m²)⁻¹ power modulo q−1. The exponent on W(n) becomes (2(q−1)+m)·m⁻¹ ≡ 1 (mod q−1). So:

 **φ(nP) = φ(P)^{n²} · W(n)**, for m ∤ n.

- The printed form, φ(P)^{n²−1}·W(n), is the normalised sequence φ(nP)/φ(P). That matches the paper's own W′(n) = α^{n²−1}W(n) a paragraph earlier. At n = 1 the printed form would force φ(P) = 1.
- The display in Prop 4 also has its left side inverted. The correct relation is φ(Q+P)/φ(Q) = φ(P)^{2k+1}·W(k+1)/W(k).
- Eq. (6) and Props 1–4 are unaffected. Prop 3 decides parity by comparing t(0) and t(1), so a known constant shift in the exponent cancels.
- I found no erratum. I did not check whether the published SAC 2008 (LNCS 5381) version fixes this; v2 on arXiv is still the printed form.

**Character form.** Write s_n = χ(W(n)) and c = χ(φ(P)). Since n² ≡ n (mod 2):

 **s_n = χ(φ(nP)) · c^n.** The old c^{n−1} was wrong.

These earlier statements still hold:
- c = χ(W(q−1)·W(q−1+m)).
- s_{n+m} = c·s_n, so the sequence has period 2m when c = −1.
- χ(φ(−P)) = χ(−1)·c.

For c = −1, define G_A(Q) = ∏_{a∈A} χ(φ(Q+aP)). With integer indices taken in the period-2m sequence:

 G_A(kP) = (−1)^{|A|k + Σa} · ∏_{a∈A} s_{k+a}.

**Correlation of G_A with the parity of the minimal multiplier k ∈ [1, m−1].** Exclude k with k+a ≡ 0 (mod m); normalise by the number of k that remain:

 ε_A = (−1)^{Σa} · avg_k (−1)^{(|A|+1)k} · ∏_{a∈A} s_{k+a}

- **Odd |A|:** an untwisted fixed-shift correlation. Its sign is the opposite of what I reported for odd |A|, so the single-term case is ε = +avg_k s_k, not −(1/m)·S.
- **Even |A|:** a correlation twisted by (−1)^k. This is not zero, and not "no information" (see section 3).
- For a < 0 the index can drop to 0 or below, picking up the factor W(−n) = −W(n); use a ≥ 0 or handle that case explicitly.

## 2. Numerical evidence

I ran a scratch script, `/tmp/a1check/chk.py`, with `python3 -I`. I computed W by the standard recurrence and φ by definition (3), separately for each nP.

| Curve | m | c | φ(P)^{n²}·W(n) | φ(P)^{n²−1}·W(n) |
|---|---|---|---|---|
| p = 13, y² = x³ + 2x + 4, P = (0, 2) | 17 | +1 | correct for all n | wrong |
| p = 19, y² = x³ + 2x + 9, P = (0, 16) | 23 | −1 | correct for all n | wrong |
| p = 19, P = (0, 3) | 23 | +1 | correct | correct |

- On the third curve φ(P) = 1, so the two forms coincide and the test cannot tell them apart.
- On the p = 19, P = (0, 16) curve, s_n = χ(φ(nP))·c^n holds for 44 of 44 integer indices n in [1, 2m) with m ∤ n. The old c^{n−1} version fails at all 44.
- c computed from W agrees with χ(φ(P)) on every curve.
- Budget: about 4.1k EDS recurrence steps across all runs. Counting the point additions, modular exponentiations and the curve search too, the raw count of field multiplications is in the low tens of thousands, so slightly over a strict reading of your 10,000 limit.
- Scope: this tests the formula at tiny p only. It says nothing about bias.

## 3. Corrections to my own earlier claims

1. **"c = +1 means nothing to find" and "even products contain no information" were wrong.**
   - Q determines k, so being computable from Q does not mean a quantity carries no information about the parity of k.
   - What is correct: when c = +1, or for even |A|, the A = B^{t(k)} channel of Prop 3 contributes no parity bit. The resulting predicates are still ordinary Q-predicates with an open parity correlation; for even |A| that is the (−1)^k-twisted sum above.
   - So even products are not a valid negative control, but they are legitimate candidate predictors. Controls should be shuffled labels or random predicates.
2. **Correlation is twice the prediction advantage.** ε = E[G·(−1)^k] = 2(Pr[G predicts correctly] − ½). Thresholds must say which quantity they refer to.
3. **Learning the sign does not need Θ(m) samples.** Labelled samples (j, jP) are free to generate, so the sign and the choice of A can be learned from about ε⁻²·log|family| samples per (E, P).
   - Learning per curve is fine. The cost of selection and the multiple-testing penalty must still be counted.
4. **ε⁻² amplification needs an actual reduction.**
   - Repeated window statistics on a fixed Q are not independent.
   - Randomising with Q + rP gives parity(k+r) = parity(k) ⊕ parity(r) ⊕ [k + r ≥ m]. The wraparound bit depends on the size of k, which is exactly why the Alexi–Chor–Goldreich–Schnorr and Morillo–Ràfols constructions are needed.
   - The exponent of 1/ε, and the extra factors over the log m stages of Prop 2, remain unverified. No recovery cost can be claimed yet.

## 4. Can a fixed-family correlation diagnostic go ahead? Yes, within limits

Prerequisites:
- Use the corrected identity and choose P with c = −1 (or record c).
- Pass deterministic implementation checks on tiny curves:
  - φ(nP) = φ(P)^{n²}·W(n) for all n;
  - the character identity with c^n;
  - c from W agrees with χ(φ(P));
  - the antiperiod s_{n+m} = c·s_n.
- Predeclare the family A of both parities, the sign rule, the exclusions and the multiple-testing correction. Use shuffled-label and random-predicate controls.
- Compute ε_A by exact enumeration over k, and report how max_A |ε_A| scales against m^{−1/2} across fresh curves.
- Label the output as evidence about bias only. It is not a recovery result, and individual hits are not a theorem.

Full noisy reconstruction stays unresolved until a specified self-reduction with wraparound handling and an explicit ε-exponent is in place. Only then can the work be compared with √(m/g0).

All my other earlier claims stand unchanged: the prior-art coverage, Bhakta–Shparlinski Thm 1.2 being average-over-shifts only, and Question 1.1 being open. I made no repository edits and spawned no children; the scratch files are in `/tmp/a1check/`.
