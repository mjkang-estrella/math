# H026 EDS cards: deduplication and transcription correction

2026-10-08. Supersedes H026-representation-grok-raw.md where claims conflict.
NEW native Astra read-only review (/root/h007_additive_relations), root integration.
No experiment or formal theorem added; no complete-work improvement.

The order-translate point function and normalized sequence are different:
with gamma=phi(G),

`phi(nG)=gamma^(n²) W_G(n)`,
`h_n=phi(nG)/gamma=gamma^(n²−1) W_G(n)`.

The n²−1 exponent is correct for h_n, not for the point function with the given
definition. Astra checked Lauter–Stange's primary HTML and retained Liao–Zhang
publisher text; this convention issue was already recorded in H003/H023.
https://arxiv.org/html/0803.0728v2
https://tches.iacr.org/index.php/TCHES/article/download/13106/12653

Substitution gives W(q+1)W(2)/W(q+2)=gamma^(2q) and
W(2)W(kq+1)/W(kq+2)=gamma^(2kq). Replacing unknown EDS ratios with their phi
masks reproduces the identity; it supplies no independent public right-hand side
for recovery via L^k. The cited O(log³p) is time under the source's naive field
arithmetic, not that many field operations.

The raw doubling-genealogy card has a consequential transcription defect. Ward
actually gives

`h_(k−2l) h_k = h_(k−l+1)h_(k−l−1) h_l² − h_(l+1)h_(l−1) h_(k−l)²`,
`h_(k−2l−1) h_(k+1) = h_(k−l+1)h_(k−l−1) h_(l+1)² − h_(l+2)h_l h_(k−l)²`.

The raw text replaced h_l² and h_(l+1)² by h_(2l) and h_(2l+1). Publisher support
C_l=h_l² does not require the alleged distinct even-index terms. Withdraw that
genealogy obstruction. Support count alone also cannot assign a full-list cost
per support for every lazy schedule. The accepted H022 literal schedule has
c_g=3+s/2, c_b=5.25+s and rectangular-prefix expected arithmetic
(2sqrt(2)/3)*sqrt(c_g*c_b*q), for s=S/M. Its scoped comparison with H019 remains;
no general lazy-support lower bound follows. H023 neighbor refinement means a
scalar multiplication per false hit is not mandatory either.

For the absolute-character card, H003 already treats the same sequence. With
c=chi(gamma), H=[2^-1 mod q]G and v(n)=chi(2y(nH)),
`chi(W_G(n))=c^n*v(n)` on integer indices. Keep the parity twist before reducing
point indices mod q. The accepted bounds imply, for the mean over1,...,q−1,

`|mu| ≤ 6sqrt(p)/(q−1)` if c=1,
`|mu| ≤ 6sqrt(p)(2+ln q)/(q−1)` if c=−1.

Thus q≈p gives at most q^(-1/2+o(1)) global bias. This is not a different-sequence
escape from H003. Furthermore a global mean alone does not imply unknown-index
short-window concentration or reliable repeated parity recovery. The raw
1/mu² window cost lacks the required dependence/error analysis.

Do not run the proposed small mean/window test: it supplies no distinct gate
beyond accepted H003. Preserve the restrictions: growing windows, adaptive
predicates, non-character features and other EDS constructions are not closed.
Reference accepted findings H003-eds-literature-reconciliation.md,
H003-eds-character-collapse.md and the H022/H023 schedule and refinement records.
Current supported ordinary complexity square-root; verified improvement NONE.
