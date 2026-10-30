# Proposed sharp 3×3 permanental Koteljanskii ratio

Parent proposal, 26 October 2026. **Credit 0**: complete mathematical proof, exact algebra checks, a fresh strict Lean replay
(53 declarations, six modules), and a rendered three-page draft manuscript.
Independent source/math/formal/novelty/manuscript review and the final
extracted packet remain pending.

## Exact unresolved source question and limits of attribution

Skandera–Soskin, *Permanental Inequalities for Totally Positive Matrices*,
Electronic Journal of Combinatorics 32(1) (2025), #P1.14,
DOI 10.37236/13098, Proposition **11**, Eq. (49), p. **13**, proves bounds
1/2 and 2 for the ratio below and explicitly says they are believed not tight;
the reported experimental values are 2/3 and 121/114. The actual published
16-page PDF was fetched, and p.13 was rendered and visually read.
The arXiv v1 source labels the result Proposition **3.6**; the FPSAC2025
companion gives the same weak bounds and observations after Eq. (3.15).
The author's slides explicitly ask for tight permanental Koteljanskii bounds.

MathDB **363360** points to this source paper, but its literal question is the
different, all-n **permanental Sihong polynomial** conjecture (published
Conjecture 13 / arXiv Conjecture 4.2). **This proposal does not solve that
MathDB conjecture.** It addresses the source's distinct, explicitly unresolved
sharp-bound question for the 3×3 Koteljanskii ratio. Eligibility under the
campaign standard must be independently assessed, just as for other outcomes
whose exact source question differs from the database pointer. No database
post/status change or external posting is authorized or performed.

## Proposed theorem

For every real **totally positive** 3×3 matrix A (all minors strictly positive),
let

    R(A) = per(A_{12,12}) per(A_{23,23}) / (per(A) a_22).

Then

    2/3 < R(A) < 9/8.

Both constants are optimal over the full totally positive class: the
infimum is 2/3 and the supremum is 9/8. Neither is attained within the
strict class. This is ONE proposed combined sharp-range theorem, not
separate credits for lower/upper bounds, witnesses, or algebra helpers.

## 1. Invariant positive row/column normalization

Every entry is positive. Set

    B_ij = a_ij a_11 / (a_i1 a_1j).

This is positive row/column diagonal scaling, so it preserves strict total
positivity. Every product in the numerator and denominator defining R has
row multiplicities (1,2,1) and column multiplicities (1,2,1). Thus the same
positive scaling factor cancels and R(B)=R(A). We can write

    B = [[1,1,1], [1,x,y], [1,z,w]].

The positive minors in rows/columns 12 give x>1. The minors in rows 12,
columns 23 and rows 23, columns 12 give y>x and z>x, respectively. Put

    b=y−x>0,  c=z−x>0,
    d=w−x−b−c−bc/(x−1).

Direct expansion gives

    det B = (x−1)d,

so d>0. Conversely these positive parameters with x>1 describe totally
positive normalized matrices: the nine 2×2 minors, in lexicographic row/column
order, are

    x−1,  x+b−1,  b,
    x+c−1,  w−1,  w−x−c,
    c,  w−x−b,  xw−(x+b)(x+c).

Here w=x+b+c+bc/(x−1)+d, so each is positive; for example the last equals
x d + bc/(x−1)>0. All entries and the full determinant are positive as well.
The forward argument only needs four relevant minors, but the theorem's
hypothesis is the literal full total-positivity condition.

## 2. Exact positive certificates for both universal bounds

Write

    N=(1+x)(xw+yz),
    D=x(xw+yz+w+y+z+x)>0.

These are exactly the numerator and denominator of R(B), since the
3×3 permanent has all six permutation terms. With y=x+b and z=x+c,

    N−D = bc−2x².

Substituting w=x+b+c+bc/(x−1)+d yields the exact identities

    (x−1)(3N−2D)
      = 2x²(x−1)² + 2x(x+1)(x−1)(b+c)
        + (2x²+3(x−1))bc + x(x+1)(x−1)d,

    (x−1)(9D−8N)
      = 2x³(x−1) + 20x²(x−1) + 2x(x+1)(x−1)(b+c)
        + 2(x−2)²bc + x(x+1)(x−1)d.

Every summand is nonnegative for x>1,b,c,d>0, with strictly positive terms
on each right side. Dividing by the positive factors proves
3N>2D and 9D>8N, hence the claimed strict bounds for every totally positive A.

## 3. Sharpness within the strictly positive class

For t>0 use

    U(t) = [[1,1,1], [1,2,t+2], [1,t+2,t²+2t+3]].

This has x=2,b=c=t,d=1, so it is strictly totally positive by the preceding
minor calculation. Its determinant is exactly 1, and

    R(U(t))=(9t²+24t+30)/(8t²+24t+38) → 9/8  as t→∞.

For ε>0 use

    L(ε) = [[1,1,1], [1,1+ε,1+2ε], [1,1+2ε,1+5ε]].

It has x=1+ε,b=c=d=ε, determinant ε², and every minor is strictly
positive. As ε→0+, all entries tend to 1, so the ratio tends to 4/6=2/3.
These families rule out every larger universal lower bound and every
smaller universal upper bound. Thus the two constants are optimal.

## Prior-work honesty: the upper endpoint witness is NOT new

The non-strict TNN/PSD boundary matrix

    [[1,1,0],[1,2,1],[0,1,1]]

already has R=9/8; it appears explicitly in Sra, arXiv:2609.39979v1,
Introduction. The counterexample value, and the failure of R≤1, receive
**no novelty credit**. The reported value 121/114 in Skandera–Soskin is an
experimental observation, not a conjectured upper bound to be refuted.
The prospective contribution here is the **universal sharp upper bound**
9/8, together with the universal sharp lower bound 2/3, for every strict TP
matrix. The TP approximation families and the small t=7 example are
supporting sharpness evidence, not separate discoveries.

Sra's Theorem 1.1 concerns symmetrizable **inverse M-matrices**, a distinct
class on which R≤1 holds; it does not assert a bound for all TP matrices.
The author-hosted May2026 Barrett–Johnson companion, §6, was read: it uses
the TP example [[8,2,1],[2,1,2],[1,2,8]] with R=144/137 to disprove R≤1,
but does not state the proposed sharp-range theorem in that section.
The 2026 Pan–Skandera–Wang paper concerns disjoint consecutive/parity
principal blocks and the different Sihong conjecture. No resolution of the
present sharp range was found in the inspected material. This is only a
preliminary bounded screen; full independent comparison is still required.

## Exact checks already run

`check_algebra.py` uses independent SymPy determinant and all-permutation
permanent expansions to verify both certificate identities, the normalized
determinant, all nineteen nonempty minors of both sharpness families, both
limits, and 1000 seeded rational TP matrices (all minors checked exactly).
`algebra-check.json` records the result. These checks support the hand proof;
they do not replace a full Lean source endpoint or independent novelty review.

## Acceptance update

Integrated as outcome14 in candidates/permanental3 after independentfivegatePASS,
cosmeticminor-ordercorrection and fresh extracted53-declaration strict replay.
The source Sihong MathDB363360question remains unresolved. Exact archive/hash
and bounded prior-art qualifications are in the campaign ledger/packet receipt.
This lane receives no separate additional credit.
