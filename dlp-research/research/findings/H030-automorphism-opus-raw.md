# H030 automorphism initial report — raw, not accepted wholesale

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h030-automorphism-operations-opus-20261008-r1`
Provider/model: claudeAgent / claude-opus-5-5
Completed 2026-10-08; mathematical/source reconciliation pending. No proposed calculation authorized by this raw report.

# H030: automorphism-aware search on j=0 curves — research report

**Bottom line:** No candidate survives. Verified improvement over the order-6 baseline is still **NONE**, and the generic √q reference and exponent 1/2 are unchanged. I offer one detailed mechanism (A), one that a short algebraic bound rejects (B), and one structural scoping result (C). C limits where any further j=0 saving could come from.

**What I did:** I worked read-only. I edited nothing, committed nothing, ran no experiments, delegated nothing and did not touch the toolchain. I did not open any other H030 proposals. To avoid repeating earlier work I checked H001-delayed-canonicalization-gate, H001-opus-critic-raw, H003-orbit-invariant-development, H014-coset-backend-cards, H014-preflight-opus-raw, H027-symmetry-repair-and-genus-interface, H029-arithmetic-screen and H002-lift-math-review-raw. None of them covers the quotient-line maps below. H003 and H014 cover multiplicative and coset walks in general. H027 covers order-6 symmetrisation through pairings.

## Baseline (primary source read)

The source is the Bos–Costello–Miele PKC 2014 slides; I read all 13. They use BN254, a j=0 curve with an order-6 automorphism group:
- **Per step:** a regular iteration costs 6m, and the automorphism overhead is 1m, for computing βx and selecting the minimum x with odd y.
- **Predicted speed-up:** 0.857√6.
- **Measured speed-up:** 0.790√6, using r=1024 and fruitless cycles handled by an extra table plus detect-and-escape.

So the competent order-6 baseline is about 7.6 field operations per ideal √(πn/12) step. The only constant-factor headroom left in this setting is 1/0.790 ≈ 1.27×. No constant-factor idea here changes the exponent.

## A. Multiplicative rho on the quotient line u = x³ — rejected on paper, one symbolic check left

**Exact public operation.**
- E: y² = x³ + b, with p ≡ 1 (mod 3). This is secp256k1's shape, with b = 7.
- u = x³ = y² − b is an exact invariant of the order-6 automorphism group, and P¹ with coordinate u is exactly E divided by that group. Milnor, *On Lattès Maps*, Thm 3.1 and Rem. 3.2, gives the n=6 semiconjugacy by ℘³ or (℘′)², and §3 gives degree |a|².
- Endomorphisms commute with the automorphisms, so each one descends to a rational map on u. I checked these two by hand:
  - **√-3 map:** x′ = −(x³+4b)/(3x²), y′ = y(x³−8b)/(−3√-3·x³). I verified the image lies on E by expanding with t = x³. On u this gives u′ = −(u+4b)³/(27u²) = u·R³, with R = −(u+4b)/(3u).
  - **Doubling:** u′ = u(u−8b)³/(64(u+b)³), so R = (u−8b)/(4(u+b)).
  - **Exceptions:** none on a prime-order group. u = 0 would mean 3-torsion and u + b = 0 would mean 2-torsion.
- **Walk:** u ↦ φ_{μ(h(u))}(u). There is no canonicalisation, no y coordinate and no table of jump points.
- **Starts:** each walk starts at s_i = a_i + b_i·k, i.e. the point a_iG + b_iQ.
- **Multiplier bookkeeping:** the multipliers commute, so each walk needs only two integer counters, m = 2^α·s^β with s² ≡ −3 (mod n).
- **Recovery:** a u-collision gives m_i·s_i ≡ ζ·m_j·s_j for one of six ζ. Then k = (ζ·m_j·a_j − m_i·a_i)/(m_i·b_i − ζ·m_j·b_j), and each of the 6 candidates is verified.

**Possible gain sources.**
1. No 1m canonicalisation.
2. A provable absence of short fruitless cycles. A cycle needs the product M of its multipliers to satisfy M ≡ ζ mod 𝔫, so n ≤ (√N(M) + 1)². With multipliers {√-3, 2} that forces cycle length ≥ ~128 at 256 bits; with norm-7 multipliers added, ≥ ~91.
3. A one-coordinate state and compact distinguished-point records.

**Paid costs, counting S = m as Bos–Costello–Miele do.** Both cheap maps cost exactly the baseline's 7 operations: 3M for the batched inversion, 1M for R, 1S+1M for R³ and 1M for u·R³. The constants 28 and 56 are just additions for b = 7. In this representation every step costs at least 7, because the hash needs an affine u. Norm-7 maps have deg R = 2 and need roughly 8–9 operations. Up to units, only two non-unit multipliers reach 7 operations: √-3 and 2.

**Why it fails.** The walk only mixes well with many multipliers. With step probabilities p_i, the in-degree argument gives an exact collision-time penalty of 1/√(1 − Σp_i²) under a random hash. That costs √2 with r = 2, about 9.9 operations, and about 8.7–9.0 even with the norm-7 maps optimally weighted. To beat the measured 7.6 you would need about 7 or more equally weighted maps at 7 operations each, and only two exist.

**Unsupported assumption:** that some family of at least 7 multipliers costs ≤ 7 operations each.

**Cheapest decisive falsifier:** derive the exact norm-7 u-map, by Vélu or the kernel polynomial on a toy prime-order j=0 curve. Count its operations and minimise Σp_i·c_i / √(1 − Σp_i²). Reject if the result is ≥ 7.6. My estimate is that it fails by at least 15%, so no experiment is justified.

## B. A larger quotient from ⟨μ6, √-3⟩ — rejected

Ordinary curves over F_p have at most 6 automorphisms (Bos–Costello–Miele list max = 6), so j=0 is already the top case. A larger cheap group would need a non-unit μ of small multiplicative order m mod n. If μ^m ≡ ζ, then n ≤ (N(μ)^{m/2} + 1)². For μ = √-3 at 256 bits this forces m ≥ 162. A canonical label by orbit enumeration costs about 7m operations for at most a √m gain, a loss for every m ≥ 2.

- **Unsupported assumption:** that no cheaper orbit invariant than enumeration exists.
- **Falsifier:** compute the order of √-3 mod n for secp256k1. This is a few seconds of computation; I did not run it.

## C. Scoping lemma: additive steps must canonicalise

Suppose a step has the form P ↦ αP + T, with α an endomorphism and T fixed. It descends to the order-6 quotient only if (ζ − 1)·T = O. For order 6, 1 − ζ is a unit; for order 3, 1 − ω has 3-torsion kernel, which a prime-order group lacks. Either way T = O.

So a canonicalisation-free walk must be purely multiplicative, and that is A, which fails. Additive walks keep the roughly 1m selector plus cycle handling, the known baseline. The rest of the 27% gap is micro-optimisation, not a mechanism. Adding √-3 or doubling steps to the (x,y) additive walk costs about 8–9 operations and gains nothing, since r = 1024 already mixes well.

## Applicability and caveats

- **secp256k1:** A and B apply exactly to the standard parameters (p ≡ 1 mod 3, b = 7, n ≡ 1 mod 3, s = √-3 mod n exists). Nothing here transfers to curves whose only automorphisms are ±1.
- **Not counted as gains:** GLV only speeds up the per-walk start scalar multiplications, which are setup, not steady search. The sixfold quotient, negation and j=0 itself are baseline.
- **Not checked numerically:** the Brent–Pollard-type penalty is the exact in-degree computation under a random hash, not a measurement. Fixed-multiplier walks can mix worse than that.
- **Prior art:** I found no primary source for a "u-line multiplicative rho". That is a search result, not a novelty claim.

## Next step that could change the conclusion

The norm-7 u-map operation count from A, plus the order of √-3 mod n from B. Both are short symbolic or arithmetic checks, and I expect both to confirm rejection. No further H030 experiment is justified from this lens.

Sources:
- [Bos–Costello–Miele, PKC 2014 slides](https://www.iacr.org/workshops/pkc2014/slides/4-2-EC-HEC-security-analysis.pdf) — read in full
- [Milnor, On Lattès Maps](https://arxiv.org/abs/math/0402147) — §§1–3 read
- [Bos–Kleinjung–Lenstra, negation map in Pollard rho](https://infoscience.epfl.ch/record/164553) — abstract and search summary only
- [Fan–Wang–Cheng, rho with point halving (DCC)](https://link.springer.com/doi/10.1007/s10623-011-9599-5) — paywalled; abstract summary only
