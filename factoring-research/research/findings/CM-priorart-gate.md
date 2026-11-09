# CM anomalous-curve source gate

2026-10-08. **Known special-purpose mechanism; no new candidate selected.**
Verified COMPLETE classical factoring complexity improvement: **NONE**.
This is a bounded primary-source check, not an independent audit of these
papers or a new mathematical lower bound. It runs alongside the remaining
W002 reviews and does not change their frozen brief.

## Question and project deduplication

Could selecting anomalous curves remove the large scalar length in ECM and
provide a distinct cheap route to factoring from N alone? Before pursuing
this, the coordinator reread W001-algebra Card A. That card uses translated
CM cubics and composite-index Hasse coefficients; its missing extractor and
H007's closure remain unchanged. The scalar-N construction considered here
uses division polynomials and class polynomials, a different computation.
Difference from that card does not establish novelty.

## What the primary sources support

[Cheng's 2002 ePrint abstract](https://eprint.iacr.org/2002/109) describes the
special families 4p-1=d b^2 with d in {3,11,19,43,67,163}. Only the abstract
and metadata were readable; the PDF returned HTTP 403 locally. The later
generalized manuscript surfaced in search, but its CiteSeer PDF returned 404.
Neither full Cheng proof is claimed read.

[Sedlacek et al., 2019](https://crocs.fi.muni.cz/_media/publications/pdf/2019-secrypt-sedlacek.pdf),
sections 2–4 and the opening of section 5, already describe scalar N,
symbolic j in (Z/NZ)[X]/(H_-D), division-polynomial evaluation, and gcd
extraction. Algorithm 1 explicitly takes D as auxiliary input with
4p-1=D s^2. Section 4.3 labels independence across components heuristic;
the near-unit success estimate is not adopted as a uniform theorem here.
The opening of section 5 discusses searching D and direct modular class
polynomials. Its internally inconsistent wording about dependence on D
is not used as a complexity bound. PDF pages 3 and 5 were visually checked;
later experiments and density estimates were not audited or imported.

[Aikawa–Nuida–Shirase, 2019](https://www.jstage.jst.go.jp/article/transfun/E102.A/1/E102.A_74/_article/-char/en)
also advertises arbitrary-degree class polynomials and extensions involving
4p=t^2+Dv^2 and smooth p+1-t. This was an abstract/metadata check only;
both browser PDF attempts failed. It supplies a deduplication lead, not a
verified success or cost theorem for our input law.

[Enge, arXiv:cs/0601104v2](https://arxiv.org/pdf/cs/0601104v2), section 1,
separates floating-point approximation cost from exact polynomial recovery.
Theorem 1.1 costs O(h(log^2 h+log b) M(b)) at b-bit precision; Theorem 1.2
bounds logarithmic height by O(sqrt(|D|) log^2 |D|). Corollary 1.3 explicitly
retains a rounding heuristic for the near-linear-in-|D| construction.
Here b is precision, not our input bit length. Section 1's theorem statements
and discussion on PDF pages 1–3 were read; page 2 was visually checked.
This is not a lower bound for computing
only a modular residue or another representation.

[Sutherland, arXiv:0903.2785v4](https://arxiv.org/pdf/0903.2785v4), Theorem 1,
gives a Las Vegas modular class-polynomial construction under GRH, with
expected time O(|D| log^5 |D| (log log |D|)^4) and space
O(sqrt(|D|)(log |D|+log P) log log |D|). P is any positive target modulus.
Its introduction and overview explain that online CRT saves storage while
still computing enough auxiliary residues for reconstruction. Read pages
1–4; page 2 was visually checked. Section 7's complete proof was not audited.
This is an upper bound for an existing construction, not an unavoidable
cost of all possible CM methods.

## Coordinator conclusion and reopening criterion

The source check answers the immediate novelty question negatively: choosing
scalar N and keeping j symbolic are already published mechanisms. No new
complete factoring bound follows merely by substituting this scalar into
W002 C's comparison.

Our N-only task still needs a constructed, paid discriminant selection or
coverage rule; the costs of all tested discriminants and their actual
representations; and proper-factor success including nonunit operations and
unsuccessful branches. Neither a supplied favorable D nor an unproved useful
mass can be inserted as free input. This is a missing-algorithm assessment,
not a proof that such a selection rule cannot exist.

Do not launch a numerical sweep of known special-family successes. Reopen
only with a concrete changed selection/representation mechanism that states
what it saves after setup, recovery and success probabilities are charged.
No H032 brief, implementation, mathematical experiment or Lean change is
selected by this source gate. The remaining W002 reviews keep priority.

## Evidence

Full downloaded primary bytes and reading aids are in
[CM-priorart-sources](CM-priorart-sources/). The initial
[retrieval record](CM-priorart-sources/retrieval.json) preserves successful
downloads and failures; the [Sutherland record](CM-priorart-sources/retrieval-sutherland.json)
records the later addition. Enge's downloaded PDF identifies v2 on its first
page. Browser-only abstract reads and PDF failures are described above;
no failed response is represented as a full-text audit. The accompanying
[manifest](CM-priorart-delivery.sha256) identifies the note, originals,
reading aids and four viewed page images. No source was altered.
