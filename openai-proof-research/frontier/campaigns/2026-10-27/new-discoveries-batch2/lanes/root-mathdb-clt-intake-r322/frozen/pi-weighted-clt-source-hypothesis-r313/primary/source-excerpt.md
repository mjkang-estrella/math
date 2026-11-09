# Primary source excerpt — arXiv:2505.03210v3 (transcribed from retrieval)

Retrieval: https://arxiv.org/abs/2505.03210 (abs page) and https://arxiv.org/html/2505.03210v3
(LaTeXML full text), fetched 2026-10-30 via fetch_content (responseIds mvvjeh8otv9yaf,
mvvjeqk3fzl81s raw; mvvjfd2tt2wqkv readable). No 403/429/challenge encountered. Lawful
primary arXiv HTTP. Version v3, 23 Jan 2026; journal ref: Mathematische Annalen (2026),
vol. 294, Paper No. 18, 46 pp; DOI 10.1007/s00208-026-03311-0.

Verbatim Conjecture 1.1 (Section 1.2.2, as rendered by LaTeXML; whitespace normalized):

  "Assume that X_1,...,X_N are independent and identically distributed centered random
  variables, satisfying E X_1 = 0, E X_1^2 = 1, E X_1^3 = 0 and E|X_1|^5 < +inf. Then,
  there exists some C_0^infty([0,1]) weighting function wbar(x) with int_0^1 wbar(x) dx = 1,
  such that for Abar_N = sum_{n=0}^{N-1} wbar(n/N) > 0 and some universal constant C_3 > 0,

    sup_{x in R} | P( (1/sqrt(Abar_N)) sum_{n=1}^{N-1} sqrt(wbar(n/N)) X_n <= x ) - G(x) |
        <= C_3 E|X_1|^5 / N^{3/2},

  provided the corrected normal distribution G(x) defined as

    G(x) = (1/sqrt(2pi)) int_{-inf}^x exp(-t^2/2) dt
           - (E|X_1|^4 - 3)/(8 sqrt(2pi) N) (x^3 - 3x) exp(-x^2/2)."

Surrounding context (verbatim fragments):
- Theorem 1.8 (proved, via [Kla09, Theorem 1]): log-concave unconditional density, rate
  C_2/N with C_2 possibly depending on p,q; sup_{0<p,q<=M} C_2 < inf.
- Pre-conjecture remark: "...under the assumption that the fifth moment is finite, by
  introducing a corrected normal distribution, it can be shown that the weights that
  achieve the weighted central limit theorem at a rate of O(N^{-3/2}) are of almost full
  normalized Lebesgue measure s_{N-1} on S^{N-1}, see [Bob20, Theorem 5.1.1].
  Unfortunately, we do not know whether our weights derived from (1.1) or some other
  variants ... with the C_0^infty([0,1]) property as well as the normalization property
  belongs to such almost full measure sets. One feasible approach is to verify certain
  arithmetic properties of the weights, such as those described in [KS12, (iii)] (or the
  assumptions within Conjecture 1.1 below). This approach requires further exploration
  and is of significant interest. Here, based on [KS12, Theorem 1.1] in the measure
  sense, we leave the following conjecture:"
- Weight exemplar (1.1): w_{p,q}(x) = (int_0^1 exp(-s^{-p}(1-s)^{-q}) ds)^{-1}
  exp(-x^{-p}(1-x)^{-q}) on (0,1), 0 outside; "It is observed that w_{p,q}(x) in
  C_0^infty([0,1])" — i.e. C_0^infty here means smooth and flat at the endpoints
  (w(0)=w(1)=0 to infinite order), as the source's own exemplar shows.

Key references per the source bibliography:
- [Kla09] B. Klartag, PTRF 145 (2009), 1-33.
- [KS12] B. Klartag, S. Sodin, Theory Probab. Appl. 56 (2012), 403-419.
- [Bob20] S. Bobkov, "Edgeworth corrections in randomized central limit theorems",
  Geometric Aspects of Functional Analysis, LNM 2256, Springer (2020), 71-97.

Fidelity check vs MathDB record 368302 (inputs/mathdb-368302.json, sha256
40694539e793c30973f5d3f5364a50ee311f8546a027054257a5ea9e8e230093): the record's
statement matches the source's Conjecture 1.1 in hypotheses, weight class,
normalization, index endpoints (sum n=1..N-1 vs Abar_N over n=0..N-1), the corrected
normal with coefficient (E|X_1|^4-3)/(8 sqrt(2pi) N), the rate C_3 E|X_1|^5 / N^{3/2},
and the quantifier order (exists wbar; exists universal C_3; for all iid centered X with
the four moment conditions; all N; sup over x). The record is a faithful transcription.
