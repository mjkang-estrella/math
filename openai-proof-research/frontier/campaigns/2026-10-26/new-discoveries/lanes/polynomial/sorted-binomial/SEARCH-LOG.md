# MathDB 371324 screening checkpoint — 2026-10-26

Status: **unresolved here; zero discoveries claimed**. Paused for an independently assigned proof review. No proof or Lean module has been produced.

Primary source: Owen John Levens, *Polynomials Arising from Sorted Binomial Coefficients*, arXiv:2511.03082v1 (5 November 2025), https://arxiv.org/abs/2511.03082. Only v1 was listed at retrieval. Fresh live MathDB snapshot has status open, with no solutions or comments. Search for the exact title, identifier, Pascalian common roots, and truncated-binomial common-root variants found no later resolution of this exact conjecture; absence of search hits is not evidence of novelty.

## Exact source statement and known cases

With ascending powers, the source's reciprocal/reversed polynomial is

    P_n(z) = sum_{j=0}^n binom(n,floor(j/2)) z^j.

This is not R_n, which reverses those coefficients. Source Conjecture 4.4 (printed p.13) asks whether P_n and P_(n-k) have no common root other than -1 when both indices are odd, for every 1 <= k <= n. P_0=1 introduces no exception. Proposition 3.2 already proves adjacent coprimality, and Corollary 4.3 proves gap two. Theorem 6.2 proves that, for odd n>=3, P_n=(1+z)q_n(z^2), with q_n(z^2) irreducible over Q.

Consequently odd–odd coprimality is immediate from irreducibility and distinct degrees. Mixed-parity coprimality is also an elementary consequence of that published irreducibility: a common root forces the even irreducible polynomial q_odd(z^2) to divide P_even. It then divides P_even(-z) as well. Writing P_(2m)=(1+z)q_(2m)(z^2)+binom(2m,m)z^(2m), subtraction forces q_odd(z^2) to divide q_(2m)(z^2), and then to divide the nonzero monomial binom(2m,m)z^(2m), a contradiction. These short known-ingredient corollaries are **not counted as substantive new discoveries**. The essential remaining task is even–even coprimality beyond gap two.

Source-fidelity caution: Lemma 6.1 as stated over arbitrary domains is false without unit/sign qualifications: q(z)=z-1 is irreducible over Q and q(z^2) factors, despite nonsquare constant coefficient -1. The positive-coefficient application in Theorem 6.2 can be repaired using rational-unit normalization and the signs of the constant and leading coefficients. This is not used as a typo-based counterexample to Conjecture 4.4.

## Exact computations

`screen.py` constructs the actual integer polynomials and uses FLINT integer-polynomial gcds, permitting exactly the known degree-one gcd for two odd indices. Complete run through n=250: 31,375 pairs, no nontrivial common factor. The completed bounded extension through n=1000 is logged in `screen-1000.jsonl`: all 500,500 pairs were checked, with no nontrivial factor (265.97 seconds).

`factor.py` factors every even-index polynomial through n=400 over Z. All 200 were irreducible. This finite computation neither proves Conjecture 6.3 nor the common-root conjecture.

The two-step recursion gives a useful but currently insufficient reduction. Set w=z+1/z and T_m=P_(2m)(z)/z^(2m). Then

    T_m = w^2 T_(m-1) + (1-z) Cat_(m-1) [m w+2m-1].

Thus a common root at indices 2m<2n forces a degree 2(n-m)-1 polynomial in w to vanish. For gap two it is linear with its resulting z on the unit circle, reproducing the source proof. For larger gaps, the remainder has genuinely nonreal w roots giving z inside the unit disk; the source annular root bound alone does not rule these out. No missing inequality has been assumed.

## Provenance

- Primary PDF SHA256 `d4f34b6335a9a830db23cd18fc97ba9d7b7316cf0a661638bd3a088ebfbd76de`.
- Extracted primary text SHA256 `b20bad3c55d6a4f1315c6b7e01dd831d857f15a37cd9c88fe067677f59d7bfaa`.
- Live MathDB JSON SHA256 `39b0c2694f2ec1c4f76c39e66e5f6a0e89fd12a7107ea01a27e579163b4aa841`.

A related primary source was inspected: Peikai Qi, *Partial results on common roots of positive derivatives of geometric sums*, dated 24 October 2026, https://peikaiqi.github.io/math/Partial%20results%20on%20common%20roots.pdf. It proves coprimality for several truncated-binomial parameter regions, including Scherbak's fixed-top-index conjecture. These are different polynomials/parameter paths; no bridge to the remaining even–even Pascalian case has been established.
