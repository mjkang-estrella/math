# Full target unresolved: stronger all-order reduction and exact obstruction

Research: 29 October 2026 UTC / 28 October America/Los_Angeles. Credit 0.
No acceptance authority. No full ordinary candidate, PROOF.md, or Lean endpoint.

## Source contract and public evidence

Roger Tian, *Identities of the Function f(x,y)=x²+y³*, arXiv:0910.1571v1,
actual PDF pp.2–3, Lemma 2 and Conjecture 3:
https://arxiv.org/pdf/0910.1571v1 . MathDB319089.
Let T be any finite ordered full binary tree, internal operation F(a,b)=a²+b³.
Write p_T for evaluation with every leaf x. Assume p_S=p_T implies S=T for
EVERY one-variable expression S, without leaf/depth bounds. For every n≥1
and every labeling of T's leaves by x_1,...,x_n, including repeated labels,
the resulting polynomial must uniquely determine the entire labeled
expression among arbitrary expressions. This is the full retained target.

Actual primary PDF and HTML were re-fetched and agree byte-for-byte with
r10's archived source. Read Conjecture 3 and Lemma 2, Propositions 6/7/9,
12, 22, 27, 30, 33, Corollaries 24/31/34, and the final Assumptions 35–41,
Lemmas 39/40 and Diophantine discussion. The later arguments concern special
shapes, core/development restrictions and lexicographically minimal branches.
Their hypotheses do not cover arbitrary isolated T. The final discussion
explicitly leaves its more restricted reconstruction goal unachieved.
Lemma 2 assumes global isolation of every one-variable tree. Replacing a
variable by F(x,x) changes T to an expanded tree; isolation of T does not
establish isolation of that expansion. This logical gap is not repaired here.
Source dependencies below are only these explicit contracts; no catalogue
summary or unexamined upstream theorem is treated as a proof.

Live targeted searches found the source, its companion and Wehrung's lecture,
not a full Conjecture 3 proof. The actual downloaded Wehrung lecture is dated
22 December 2017, despite the search engine's much later crawl/publication
label. It discusses the larger Friedman problem for the reversed operation
x³+y² and reports its then-open status; it is neither a current status
certificate nor an exact resolution of Conjecture 3.
Recent complete registry receipts/trees in sol-fresh-analysis-discovery-r7
were inspected/reused as instructed, not fetched again. No target-specific
proof path appeared in the bounded predecessor screen. Path absence is not
full-text clearance. Current MathDB proof/reply bodies remain unread because
of the predecessor's403; no request to mathdb.com or api.github.com was made.
No new novelty clearance, worldwide priority, or acceptance claim follows.
Khanh quadratic and Tian's LTE companion remain excluded and were not revisited.

## Independent verification of the reduction; binary colors suffice

With independent leaf variables z_i, set
w_i(x)=(∂P_T/∂z_i)(x,...,x), and W_T=span_Q{w_i}.
For T=F(A,B), a=p_A,b=p_B, the exact leaf list is

    (2a w_i^A)_i , (3b² w_j^B)_j,
    W_T = 2a W_A + 3b² W_B.

If this list is linearly independent, equality of two labeled polynomials,
differentiated in each x_j and then restricted to the diagonal, gives
Σ_i(1_{c(i)=j}-1_{d(i)=j})w_i=0. Thus c=d. Isolation of T first forces an
arbitrary competing expression to have tree T by setting every variable x.
This proves the complete source conclusion conditional on independence for
every isolated T. The missing independence assertion is NOT proved here.

There is an exact weaker reformulation worth retaining. It suffices to
separate all binary labelings of each isolated T. An identity with different
n-color labelings can be mapped to a binary identity by sending a color j
that differs at some position to u and every other color to v. The two masks
still differ at that position. Conversely n=2 is among the source cases.
Thus a binary-mask collision for an isolated tree is an exact counterexample;
it is not enough to find a rational gradient dependence. No such collision
was found or asserted. Absence of {-1,0,1} relations among w_i is sufficient,
and is weaker than rational independence; even that absence remains open.

## Adding order-at-zero repairs the old seven-leaf obstruction

Every leaf derivative of a polynomial of order m and degree d has support
inside [m-1,d-1]. Indeed each source monomial has nonnegative coefficient;
differentiating a leaf and then restricting to the diagonal lowers its
total degree by exactly one, or removes it. This works with repeated degrees
and arbitrary finite trees, not only monic trees.

At a root, write

    m=ord a, n=ord b, d=deg a, e=deg b,
    g=gcd(a,b²), h0=ord g, h1=deg g.

A potential equality aU=b²V with U∈W_A,V∈W_B forces

    U=(b²/g)H, V=(a/g)H                         (1)

for H∈Q[x], because a/g and b²/g are coprime. If H≠0 then

    ord H ≥ L=max(0,m-1-2n+h0,n-1-m+h0),
    deg H ≤ R=min(d-1-2e+h1,e-1-d+h1).          (2)

Consequently L>R proves the actual-space intersection zero, conditional
on no additional hypotheses. With independent child lists it proves root
independence. This is a sufficient envelope test, not a characterization.

For q=F(x,x), A=F(q,q), B=F(q,x), T0=F(A,B), the predecessor had
(d,e,h1)=(9,6,4), which defeated the degree-only test. Here
(m,n,h0)=(4,3,4), giving L=2>0=R. Thus the order bound alone repairs that
example. All internal nodes of T0 satisfy (2), giving an ordinary proof
of independence without its previously computed determinant. This does not
establish source isolation of T0 and earns no finite-case credit.

An all-order consequence: if a,b have no common nonzero complex root, g is
a monomial and h0=h1=h. For a nonzero H, (2) would require

    max(m-2n,n-m) ≤ min(d-2e,e-d).              (3)

But the left side is at least -n/2 and the right side at most -e/2. If B
is nonleaf, its positive polynomial has at least two different powers, so
n<e, a contradiction. If B is a leaf, n=e=1: for integer m≥1 the left side
is ≥0 and for integer d≥1 the right side is ≤-1. Again contradiction.
Thus coprimality away from zero always separates the actual gradient
spaces. A minimal tree with dependent gradients must have children whose
polynomials share a NONZERO root. This narrows the all-order obstruction;
it is not a proof that such a minimal tree exists.

## Uniform substitution preserves gradient independence: all-order proof

For trees S,U, let S[U] mean replacing EVERY leaf of S by a copy of U.
Assume the diagonal gradient lists for S and U are Q-independent. Then
that for S[U] is independent as well.

Proof. Put u=p_U of degree D. The chain rule gives the leaf list

    w_i^S(u(x)) w_j^U(x), for all i,j.          (4)

Every w_j^U has degree <D. The elements 1,x,...,x^{D-1} are independent
over Q(u): after clearing denominators, a relation Σ_{k<D}f_k(u)x^k=0
would have a unique largest degree D deg(f_k)+k among its nonzero terms.
Thus it cannot vanish. A rationally independent list of vectors in the
rational span of these monomials remains independent over Q(u), by a
nonzero rational coefficient minor. Therefore the w_j^U are Q(u)-independent.
A rational relation among (4), grouped by j, forces
Σ_i c_ij w_i^S(u)=0 for each j. Substitution of the nonconstant u is
injective on Q[x], so independence for S forces all c_ij=0. QED.

This proof is ordinary and all-order. It does NOT prove that isolation
itself is preserved by uniform substitution, and that claim is not used.
It also does not handle different inner trees at different outer leaves.

## The improved envelope still fails on an infinite family

Let U_k=B^(k) be Tian's right comb: U_0=x, U_{k+1}=F(x,U_k).
For k≥1, ord u_k=2 and deg u_k=D=3^k. Its gradients are independent by
induction: the left column is2x, while the right columns have order≥2.
Let T_k=T0[U_k], with root children A[U_k], B[U_k]. These have

    m=8, n=6, d=9D, e=6D,
    g=u_k^4, h0=8, h1=4D, L=5, R=D-1.        (5)

The gcd identity follows from gcd(a,b²)=x^4 and Bézout after composition.
For every k≥2, L≤R, so the improved criterion fails. More strongly the
FULL support envelopes really intersect: set H=x^5 in(1). Then

    ord U=9, deg U=8D+5 ≤9D-1,
    ord V=5, deg V=5D+5 ≤6D-1,
    a(u_k)U=b(u_k)²V.

These polynomials obey both child envelopes. Yet their ACTUAL gradient
spaces have zero intersection, by the substitution theorem and the proven
independence of T0 and U_k. Thus neither degree nor degree-plus-order
plus exact gcd can support an unrestricted induction. The 21-leaf k=2
case is an exact checked representative of the all-order construction,
not the mathematical basis of an extrapolation. Source isolation of T_k
has not been established: this is a genuine obstruction to a stronger
unrestricted method, not an isolated-tree counterexample or an eligibility
claim. A refined argument using the isolated hypothesis remains possible.

A further obstruction to a shortcut: common nonzero roots do not imply
uniform common substitution. Put C=F(F(q,x),x), a comb. Exactly

    gcd(q,p_C)=q, ord p_C=3.

C is not h(q) for a polynomial h: h(0)=0 would make its order even.
In fact they have no common polynomial right component of degree>1: such a
component of q would have degree3, since deg q=3 is prime, hence would be
an affine transform of q, reducing to the excluded h(q) representation.
Both q,C are isolated by source Propositions6/7; F(q,C) itself is isolated
by Proposition9 and isolation of C. Thus isolation does not prohibit common
nonzero roots, and common roots do not force the common-composition case
covered above. This pair is NOT a gradient dependence: its degree disparity
already lets the envelope test separate it. It precisely defeats the proposed
classification shortcut, with all original hypotheses present.

## Polarization, positivity, and the unresolved step

For a binary mask c, expand R_{T,c}(x,t)=P_T(x+t c_1,...,x+t c_l).
Write its coefficients r_0,r_1,r_2,... . At a root, if child series are A,B,
R=A²+B³. In particular

    r0=a0²+b0³,
    r1=2a0 a1+3b0² b1,
    r2=a1²+2a0 a2+3b0² b2+3b0 b1².

For every k, the exact recurrence is convolution of two left coefficient
lists plus convolution of three right lists. Since u=x+t,v=x is an invertible
linear change of binary variables, equality of these series is equivalent
to equality of the full binary polynomials. This preserves all-order
polarization information but supplies no theorem that the coefficient lists
separate every two masks. At first order we recover the gradient criterion;
higher coefficients involve cross-products. Positive coefficients before
subtracting two masks do not preclude signed cancellation afterward.
No argument here justifies discarding the mixed products or inferring
independence solely from positive coefficients.

Weighted Euler supplies a useful consistency identity, not a separation
proof: if λ_i is the product of2 for each left edge and3 for each right edge
on leaf i's path, then Σ_i x w_i/λ_i=p_T. Assigning leaf i weight1/λ_i
makes every monomial have weighted degree1, proving the identity. In
particular p_T/x∈W_T; it must not be assumed that these spaces omit such
natural internal-node combinations.

Exact remaining bridge: prove no binary collision for EVERY isolated tree,
or prove no nonzero actual intersection aW_A∩b²W_B for every isolated root
(with independent children, which are also isolated). The coprime-away-from-
zero case and uniform common substitutions are now controlled. The case
of overlapping nonzero factors with unequal leaf substitutions remains
uncontrolled. Isolation of a parent implies isolation of each subtree by
replacement and equality of evaluations, but it gives no immediate bound
on those common factors or on signed derivative combinations. Any proposed
proof must fill that gap rather than repeat a rank survey or replace the
source's global hypothesis in Lemma2.

## Validation and limits

Run `python check.py` here, offline. It hard-caps address space512MiB,
CPU40 seconds and BLAS threads1 before importing SymPy. It checks the base
root inequalities and all internal nodes, weighted Euler, the k2 gcd and
explicit envelope-intersection identity, all21 substitution-chain columns,
one fixed inner-comb minor, a prescribed binary mask's first three jets
against direct bivariate expansion, and the common-root/no-composition
example. No random/exhaustive tree enumeration, unbounded search, floating
point, or repeated bounded-rank survey was performed. The first Euler check
initially compared Poly domains QQ versus ZZ; it was corrected to test the
zero polynomial difference. Final execution passes. These diagnostics
validate identities only; the ordinary all-order arguments above carry the
stated helper results. No source conjecture, counterexample, eligibility,
Lean theorem, paper, review, packet or discovery credit is nominated.
