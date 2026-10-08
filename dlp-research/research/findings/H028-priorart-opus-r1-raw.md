# H028 primary-source audit r1 — raw delivery

2026-10-08. Retained verbatim below. Root correction: GWZ was already read in H019 and its published PDF mirror remains accessible; new independent r2 has been assigned that source. Narrow search is not novelty evidence. Cell constants are historical illustrative values, not validated rates. No new complete-work gain.

Task ID: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h028-coefficient-keys-priorart-opus-20261008-r1

I couldn't find any prior use of the signed-h key in BSGS to save squarings, or the ≤3(q−1) bound under another name, but that is only a search result, not an absence claim. The ingredients are all established. Nothing I read rules out the constant-factor target. It does, however, limit the target to BSGS-type leaf outputs and give it a fairly low ceiling.

Nothing in the repo was touched and I ran no experiments. I only downloaded public PDFs into `/tmp/h028pa_dl/` and read the H027 copy of Rück that was already in `/tmp/h027rev/`.

## Sources actually read

| Source | Exact passages | SHA256 |
|---|---|---|
| Rück, Math. Comp. 68 (1999) 805–806 | p.806: group law on `S × k^{2g−1}` using the 2-cocycle `(s1,s2) ↦ (a0,…)(h)`; "(D,0)…(D,0) (p-times) is equal to (0,φ(D))"; doubling evaluates φ | `/tmp/h027rev/ruck.pdf` e86922d5… (matches the H027 record) |
| DLMF §23.10(i), eq. 23.10.2 ([dlmf.nist.gov/23.10](https://dlmf.nist.gov/23.10)) | `ζ(u+v)=ζ(u)+ζ(v)+½(ζ''(u)−ζ''(v))/(ζ'(u)−ζ'(v))` | html, not hashed |
| Bernstein–Lange–Schwabe, negation-map rho, [cr.yp.to/elliptic/negation-20110102.pdf](https://cr.yp.to/elliptic/negation-20110102.pdf) | §3 "Eliminating inversions" (pp.6–7): affine add = 1I+2M+1S+6sub; with Montgomery batching each addition ≈ 5M+1S. Cell §"Overall performance" (pp.14–15): M=43.75 and S=31.75 instructions, 6 subtractions=10.00, canonicalization 24.75; 306 lower bound vs 362 actual cycles | 78b066e7… |
| Bernstein–Lange, Two grumpy giants and a baby, [cr.yp.to/elliptic/grumpy-20120709.pdf](https://cr.yp.to/elliptic/grumpy-20120709.pdf) | §1 cost-metric caveats (pp.1–2); "The V formula" (pp.6–7): collision rate is governed by Σ_y #F⁻¹(y)² | be518a66… |
| Galbraith, *Mathematics of Public Key Cryptography* Ch.14 (author PDF) | Example 14.4.5: negation classes and lexicographic canonical representatives | ab59d801… |

**Not read (only search-snippet level):**
- Galbraith–Wang–Zhang, AMC 11(3) 2017 (ePrint 2015/605). This is the most relevant optimized x-coordinate BSGS baseline: its Algorithm 3 is "interleaved BSGS … using x-coordinates" and it notes "X−Y efficiently when computing X+Y". ePrint returned 403 and AIMS is paywalled; I did not try to get around either.
- Bos–Costello–Miele (ePrint) was also blocked.

None of their claims are accepted here.

## What is established (the parts are not new)

1. **h is Rück's construction.** Rück's 2-cocycle extension `S × k` is the same algebraic object as the h addition law `h(P+Q)=hP+hQ−λ`. When q≠p the extension splits and h is the unique splitting. This follows H027's attribution.
2. **h is a finite-field analogue of the Weierstrass ζ function.** This step is my derivation, not a quote. Take x=℘ and y=℘'/2. Since ζ'=−℘, the ζ correction term in DLMF 23.10.2 becomes (y_u−y_v)/(x_u−x_v)=λ, so −h obeys the ζ addition law.
3. **Closed form for h.** For q≠p, summing the cocycle over Q gives `h(P) = (1/q) Σ_T λ̃(P,T)`, with λ̃ = 0 on vertical and identity pairs. This is an elementary coboundary calculation of my own; I did not find a source for it.
4. **Signed-key canonicalization** is Galbraith's standard negation-class representative (Ex. 14.4.5).
5. **The second-moment framework is classical.** Brent–Pollard's V formula, as given in the grumpy-giants paper, uses the same fibre quantity Σ#F⁻¹(y)². The difference is the direction: in rho a larger value helps, but here it counts false matches. H028's version is exact (it relies on the paid randomization), not heuristic.
6. **The proof technique is a standard degree argument.** The H028 per-difference bound can be restated this way:
   - λ_T(Q)=(y−y_T)/(x−x_T) has simple poles at O and at −T, is regular at T (tangent value), and has degree 2.
   - So each value v is taken at most twice, which is exactly "≤2 ordered pairs per T".
   - That a degree-d function has fibres of size ≤d is textbook material (e.g. Silverman AEC II.2.6), which I did not re-read in this session.
   - For comparison, x keys give exactly M2=2N (only P,−P), i.e. ρ=1 and no false matches.

## What remains unestablished

- **The key itself:** using split-cocycle h keys in BSGS/collision search to replace λ² with λ on leaf outputs.
- **The bound:** the specific ≤3(q−1) residual-quadratic bound for h fibres, and the exact discriminant identity.

I found neither in what I read or in three web searches, but that search was narrow and the two key papers were unreadable. **Do not claim novelty** until Galbraith–Wang–Zhang and Bos–Costello–Miele have been read in full.

## Applicability limits and baselines

- **The saving only exists on terminal leaf outputs.** Rho and kangaroo steps need y₃ = λ(x₁−x₃)−y₁, which needs x₃ and therefore λ². For the memory-light negation rho baseline (≈5M+1S per step), h therefore saves no arithmetic. The target is confined to center±offset BSGS (H019) and inherits BSGS's O(√q) memory.
- **No leaf-arithmetic baseline that beats h turned up.** One x-variant I checked: precompute y_J², then use d⁻² and y_C·y_J. That costs 3M+1S per pair, versus 2M+2S for the standard kernel and 2M for h, so it only helps if S>M. Galbraith–Wang–Zhang's actual counts remain an unread baseline that could change this.
- **Illustrative ceiling, using Bernstein–Lange–Schwabe's Cell constants** (not a measurement for our setting): s≈0.726, a≈0.038.
  - Plugged into the H028 gate, the zero-overhead upper bound on the saving is (s−1.5a)/(2.5+s+3a) ≈ 0.669/3.34 ≈ **20%**.
  - The 10% gate holds only if `0.1·L + c + ΔL ≤ 0.335`, so even with c=ΔL=0 it needs L ≤ 3.35 M-equivalents of table traffic per key.
  - Once √q-sized tables fall out of cache, random-access lookups can plausibly exceed that, which would make the 10% target unreachable regardless of h. Whether that happens needs a real measurement.
  - In implementations where S=M (Bos et al. count squarings as multiplications in their 6M), the headroom is larger.
- **Costs the x baseline does not pay:** canonicalization (c), the false-match refinements (E ≤ 4IJ/q), the extra random-s setup, and the setup Miller chains. Bernstein–Lange also warn that multiplication counts alone don't capture overhead, memory or vectorization costs; that reinforces the existing gate.

## Bottom line

No overlooked baseline invalidates the target in what I read. The open risks are:
1. the unread x-coordinate BSGS costs in Galbraith–Wang–Zhang;
2. the restriction to BSGS leaves, since rho gets no saving;
3. a ceiling of roughly 20% from the arithmetic alone, which table traffic could erase.

Supported complete-work improvement is still NONE. The diagnostic's finding that setup loses all 12 cases is unaffected by this audit.
