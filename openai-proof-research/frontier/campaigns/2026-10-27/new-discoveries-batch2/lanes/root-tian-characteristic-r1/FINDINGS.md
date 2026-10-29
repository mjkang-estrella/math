# Tian: characteristic filtration, not a completed source proof

29 October 2026 UTC. Counts unchanged: 3 additional, 33 total; credit 0.

Read the literal Conjecture 3 and Lemma 2 on pp.2–3 of the cached primary
0910.1571v1 PDF text, plus the complete sol-tian-label-isolation-r2 report.
Source asks that every labeling of an isolated one-variable tree is isolated
among arbitrary labeled expressions, with no size bound. Keep that scope.
The primary PDF bears a 2009 arXiv stamp and a 2018 internal date; no new
version claim is inferred. Current targeted web searches returned the same
source and old Wehrung discussion, not a resolution; this is not a complete
registry or novelty clearance. The existing access limits remain.

## 1. Nonvanishing and extreme labels in small characteristic

For any labeled tree T, write P_T for its polynomial over F_p. In characteristic
2, partial differentiation at a node F(A,B)=A^2+B^3 gives

    partial_j P_T = P_B^2 partial_j P_B.

Following right children therefore shows all partial derivatives vanish except
the one for the label at the rightmost leaf; that derivative is the product
of the squares of the successive right-child polynomials. This product is
nonzero. To justify this without circularity, simultaneously induct on size:
each child polynomial and its indicated derivative are nonzero; their product
is nonzero in the polynomial-ring domain, hence the parent derivative, and
therefore the parent polynomial, are nonzero. The base variable has derivative
1. Repeated labels cause no exception: all left-branch derivatives vanish.

In characteristic 3 the corresponding identity is

    partial_j P_T = -P_A partial_j P_A.

The same simultaneous induction identifies the leftmost leaf label and proves
nonvanishing. Thus an identity of labeled expressions necessarily preserves
the rightmost label modulo 2 and the leftmost label modulo 3. These elementary
facts are uncredited helpers, not full label recovery.

## 2. Exact polynomial contents of individual diagonal gradients

Use independent leaf variables before restricting to the diagonal x. For leaf
i let L_i,R_i count left/right edges from the root. The chain rule over Z gives

    w_i = 2^(L_i) 3^(R_i) v_i,

where v_i is a product of subtree polynomials: power one for a left step and
power two for a right step. Every subtree polynomial is nonzero modulo both
2 and 3 by section 1. Hence the least 2-adic valuation of a nonzero coefficient
of w_i is exactly L_i, and its analogous 3-adic content is exactly R_i.
This is an all-order statement, with no isolation assumption.

## 3. A sufficient all-order criterion still UNPROVED

For every tree and fixed L, consider the list of reductions

    bar(w_i / 2^L) in F_2[x], over leaves with L_i=L.                 (C)

If these lists are linearly independent, there is no nonzero relation
sum c_i w_i=0 with c_i in {-1,0,1}: select the minimum L_i among nonzero
c_i, divide by 2^L, and reduce modulo 2. Terms from larger L_i vanish;
the remaining nonempty subset would contradict (C).

Consequently (C) for every isolated tree implies the full source conjecture.
Indeed diagonal specialization first forces an arbitrary competing expression
to have the same tree. If two labelings differ, differentiate their common
polynomial with respect to a label on a differing position and restrict to
the diagonal. The coefficients c_i are exactly -1,0,1, with some nonzero.
This contradicts the preceding deduction. No bound on competing tree size,
number of labels or repeated labels was introduced.

Criterion (C) for all trees is stronger than needed. It is NOT established
by this report. A failure of (C) would only refute this sufficient method,
not Tian, and not necessarily even integer gradient independence.
An analogous sufficient criterion groups by R_i over F_3; it is untested here.

## 4. Exact diagnostic and a failed shortcut

check.py implements F_2 polynomials as integer bitsets, with XOR addition and
carryless multiplication. It recursively calculates p_T and the normalized
gradients without dividing any integer polynomial numerically:

    h_left = bar(p_A) h_A; h_right = bar(p_B)^2 h_B.

Gaussian elimination over F_2 finds no dependence in (C) for all 23,714 ordered
full binary trees with 1 through 11 leaves. This is bounded evidence only.
The script enforces 512 MiB address space and 40 CPU seconds. No Lean or
full proof is inferred from the enumeration.

The tempting distinct-leading-degrees argument is FALSE already on

    T=F(F(x,F(x,x)), F(F(x,x),x)).

At zero-based leaf positions 2 and 4, both left-depth-one normalized gradients
have degree 17 modulo 2. Their exact bitsets are 0x33500 and 0x33c00; their
sum is 0x900, not zero. Thus even this small tree requires a genuine
polynomial-independence argument, rather than distinct leading exponents.
Isolation of this diagnostic tree is not asserted or needed for this failed
unrestricted shortcut.

## Remaining gap

Prove (C) for arbitrary isolated trees (or all trees), or find a counterexample
and a replacement full-scope separation argument. Shared polynomial factors
can invalidate naive coefficient support/degree reasoning; the previous
all-order substitution obstruction remains in force. Nothing here establishes
a full ordinary source theorem, novelty, a formal endpoint or acceptance.
