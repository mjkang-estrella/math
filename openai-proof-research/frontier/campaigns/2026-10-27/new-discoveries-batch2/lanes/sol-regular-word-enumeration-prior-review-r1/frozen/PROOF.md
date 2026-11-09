# Full literal enumeration; novelty and credit not certified

Target: Downing–Hartung–Lucido–Williams, *Pattern Avoidance for Fibonacci Sequences using k-Regular Words*, arXiv:2312.16052v4, p17, Conjecture1, Eq(24), https://arxiv.org/pdf/2312.16052v4. Patterns are classical subsequences, not consecutive patterns. For every integer r>=1 and n>=0 both classes Av_n^r(123,121) and Av_n^r(132,212) have cardinality

    sum(j=0..n) binom(n,j)/(n-j+1) binom(n+(r-1)j-1,n-j).

For n=0 interpret the value as1. For n>0 the j=0 term is0. Ordinary binomial conventions suffice for all remaining terms. The two classes are not identified by a square symmetry; both require proof.

## Route A: insert the smallest letter, decreasing suffix

In a word avoiding121, all occurrences of the smallest letter1 are consecutive: a non1 between two1s would create121. Delete the block1^r and decrement other letters. This gives a unique parent in the same avoidance class. Conversely, insert a new smallest-letter block into a parent (after incrementing its letters). No new121 is created: occurrences of1 cannot surround another letter, while a121 whose equal letters exceed1 cannot use1 as its larger middle letter. A new123 must start with1. Thus insertion is allowed exactly when the suffix to its right is weakly decreasing.

Let s be the length of the maximal weakly decreasing suffix, with s=0 for the empty word. The allowed gaps have right suffix lengths t=0,1,...,s. For t=0 the new suffix length is s+r. For t>0 the increasing jump from1 to the first letter to its right prevents extension to the left, so the new suffix length is exactly t. Hence each parent labeled s has exactly one child with each label

    1,2,...,s,s+r.                              (S)

This includes the empty root s=0, whose sole child has label r. Deletion/insertion are inverse and account for every word once.

## Route B: insert the largest letter, separating cuts

In a word avoiding212, every occurrence of the largest letter m belongs to a single contiguous block m^r: a smaller intervening letter would give212. Delete that block to get the unique parent. When inserting a fresh largest letter into a parent, no212 arises, by the dual argument to Route A. A new132 must use the fresh largest letter as its middle element. Thus a gap is allowed exactly when every letter to its left is >= every letter to its right. Call such gaps separating cuts, and include both boundary cuts.

Write the k separating cuts in left-to-right order, numbered0,...,k-1; set s=k-1. Insert m^r at cut j. If j=0, all r new cuts before/inside the initial block and the k cuts after it are separating. There are k+r in total, and the new label is s+r. If j>0, the new cut0 is separating; every other cut before or inside the new block has a smaller old letter on its left and m on its right, so is not separating. Exactly the k-j old separating cuts at or after cut j survive after the new block, with no formerly nonseparating cut repaired. Thus the new label is (1+k-j)-1=k-j. As j ranges1,...,k-1 these labels are precisely1,...,s, once each. Again we get (S), including the empty root (one cut, s=0).

This proves equality of the two full classes via their identical labeled generating trees. It also gives a recursive bijection: preserve the child label at every generation; sibling labels are distinct.

## Exact generating function and coefficient extraction

Let F(z,u) count either tree by number of letters n and label s. Set A(z)=F(z,1). Coefficients in z are polynomials in u, since s<=rn. Rule(S) gives the formal identity

    F = 1 + z*u/(1-u)*(A-F) + z*u^r*F,
    (1-u+zu-zu^r+zu^(r+1))*F = 1-u+zu*A.       (K)

The kernel has a unique root U(z) in 1+z Q[[z]], by the formal implicit-function theorem (its u derivative at z=0,u=1 is -1). Substitution is valid because every z coefficient of F is polynomial in u. Equation(K) gives U-1=zUA. Substituting this into the kernel equation gives A=1+zU^r A, while U=(1-zA)^(-1). Therefore

    A=1+zA/(1-zA)^r.

Put W=zA. Then W=z*(1+W/(1-W)^r). The formal Lagrange inversion theorem yields

    [z^n] A = 1/(n+1) [t^n](1+t/(1-t)^r)^(n+1)
             = sum(j=1..n) binom(n+1,j)/(n+1)
                              *binom(n+(r-1)j-1,n-j)

for n>=1. Since binom(n+1,j)/(n+1)=binom(n,j)/(n-j+1), this is literally Eq(24). The empty case is immediate. This is an ordinary-mathematical full resolution, conditional on no novel prior claim: no numerical test supplies any universal step.

## Limits and prior credit

Lagrange inversion, kernel extraction, and generating-tree enumeration are classical. The numerical sequence/formula for r2 is explicitly old: OEIS A109081 credits Paul D. Hanna, 19 June2009, and David Callan's 2007 tree equation W=z+zW/(1-W)^2. That is not yet a same-object bridge to BOTH regular-word classes for ALL r. The source itself cites Kuba–Panholzer2012 (actual body clearance outstanding at drafting). No acceptance, literature priority, Lean certificate, or separate credit for each class/parameter/helper is claimed. Independent source/prior-art/substantive review is necessary.
