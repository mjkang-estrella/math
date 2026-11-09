# expanded-corpus-r232 (Claude lane): summary

Outcome: **no credit-eligible candidate.** I reviewed all 20 reserved records against their primary sources. 12 are excluded and 8 are parked. Zero campaign credit and no self-acceptance.

Per-ID details, provenance and receipts are in `results.json` (20 entries). Exact statements with chunk/line/hash provenance are in `extracted.json` and `raw/*.jsonl`. Registry receipts are in `outputs/registry-screen.json`. Deviations from the run discipline are listed in `logs/environment-notes.txt`.

## Most notable finding: 353231 (already public)

The exact rowmotion orbit search found a counterexample to Elizalde–Plante–Roby–Sagan Conjecture 5.4(b). This is the MathDB mesicity conjecture for the fence β = (k−1, k, …, k, k−1).

- **Where it fails:** at F̆(3¹¹), with n = 32.
- **The orbit:** a rowmotion orbit of length 237 with Σ|I| = 3810 ≠ 16·237. Its mirror orbit has Σ|I| = 3774.
- **Consistency with the authors:** there are no violations for any a+t ≤ 12, which matches their verified range. The first failure is in the layer a+t = 14.
- **Independent check:** a toggle-based reimplementation confirmed it, and that implementation also checks the EPRS definition ρ(I) = P − upset(max I).

However, the public repository `Aurantium-47/fence-rowmotion-counterexample` already publishes the same 32-element fence and 237-state orbit with a Lean formalization. It was created on 2026-10-13, and its HEAD is bef0bd6c ("Document kernel verification"). **Excluded: prior public Lean refutation.**

## Sustained routes (parked)

- **382066 (strongly chordal ⇒ flag-accurate graphic arrangement, MRT Conj. 6.20).**
  - I reformulated it exactly as a contraction-sequence condition on chordal quotients with prescribed perfect-elimination-ordering exponents.
  - Exhaustive search over **all** connected strongly chordal graphs through n = 10 found no failure: 1, 2, 5, 15, 57, 263, 1497 and 10278 graphs for n = 2…9, then every clique-extension of the 10278 graphs on 9 vertices.
  - Source controls behave correctly: the Prop. 6.10 graphs are detected as non-flag-accurate and the 3-sun as flag-accurate.
  - A Lean endpoint would need Terao freeness theory, so this is a poor Lean fit either way.
- **353252 (weighted Laplacian spread, x + y − 2xy/n ≥ 1).** Local search at n = 5, 6 always converges to exactly 1, attained by the SE(s) family. A counterexample would be cheap in Lean (rational Rayleigh quotients), but none exists in the searched region.
- **353446 (Ismail–Kim–Stanton).** The printed index range 0 ≤ l < K/2 makes residue 0 nonpositive, contradicting b₀ = 1, so the literal text is a misprint. I recovered the intended rule from data: write m ≡ ±j·a with j ≤ (K−1)/2; then b_m ≤ 0 iff j is odd. No violation for K ≤ 15 with n ≤ 14, or for K ≤ 41 with n ≤ 8.
- **353267 (Amit–Ashurst).** This is open even in class 2. I enumerated all 128 two-variable word maps on UT(4,2) (order 64, class 3). The minimum positive fiber is exactly 64 = |G|, so the bound is attained but not violated.

## Quick dispositions

| ID | Disposition |
|---|---|
| 353175 | Proved by Jeong (DK Conjecture 7.1). |
| 353456 | Proved in the source (Theorem 4.1). |
| 353211 | Proved in the source (§5.1). |
| 353541 | Proved by Yuen (arXiv:2301.02517, EJC 2024). |
| 382085 | Proved by Yao (JCTA 2024) and Ding–Sun (arXiv:2403.11608). |
| 382086 | Literal (ii) strictness threshold is an endpoint misprint: all 135 failures lie in [(3k+2)(3k+3)/2, (3k+3)(3k+4)/2). The corrected form holds for N ≤ 1500, k ≤ 8. |
| 382049 | The 3-sun refutes it via the source's own Theorem 3.2 and the classical result K(chordal) = dually chordal. It is the only one of the 58 connected chordal graphs on 6 vertices that fails. Trivial classical failure, zero credit. |
| 361703 | Refuted in arXiv:2402.01272. |
| 382212 | The strong conjecture implies the weak one, so it is refuted by implication. |
| 376393 | Proved in the source. |
| 353583 | Refuted on the Omega registry. |
| 361291 | Ill-posed asymptotic O-term. |
| 370134 | Generic-realisation rigidity; parked deep. |
| 371090 | Famous; parked. |
| 353510 | Deep; parked. |

## Prior-art screening performed

- **Primary sources:** arXiv abs pages for all 19 sources (versions recorded in `outputs/versions.json`), plus full bodies of 17 PDFs and 4 HTML versions of primary or citing works (see `sources/`). Only the cited sections were read, as listed in `results.json`.
- **Web searches:** citing-work and refutation searches for 353231, 353267, 353456, 353541, 353252, 353446, 382085/6 and 382066.
- **Registry heads:**
  - Lean Pool HEAD 01db1d70: projects.yml grepped for IDs, arXiv IDs and keywords; no relevant hit.
  - Omega HEAD 3b5f65d4 and OpenAI/math HEAD 4eaee875: recorded, but their trees were not refetched because there was no candidate.
- **GitHub repository searches (6):** the only hit is the fence repository above.
