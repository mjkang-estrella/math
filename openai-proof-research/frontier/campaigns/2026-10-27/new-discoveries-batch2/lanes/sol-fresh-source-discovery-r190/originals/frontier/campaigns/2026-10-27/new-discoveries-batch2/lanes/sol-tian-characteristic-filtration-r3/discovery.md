# Tian Conjecture 3 remains unresolved

Research date: 29 October 2026 UTC / 28 October America/Los_Angeles.
Credit 0; counts remain 3/30 additional and 33/60 total. No acceptance authority.
No full source proof, counterexample, PROOF.md, Lean investment or paper.

## Literal source and bounded public-proof screen

Roger Tian, *Identities of the Function f(x,y)=x²+y³*,
https://arxiv.org/pdf/0910.1571v1 , PDF pp.2–3, Lemma 2 and Conjecture 3.
MathDB319089. Read the cached actual PDF text and the refreshed primary HTML
https://arxiv.org/html/0910.1571v1 (200, 2026-10-29T05:58:00Z; byte-identical
to predecessor; exact hash in retrievals.json). The PDF arXiv stamp is
8 October 2009; its internal title date is 12 June 2018. Neither the refreshed
HTML nor a search crawl date establishes a new proof/publication chronology.

The retained claim is: for EVERY finite ordered full binary tree T whose
all-x polynomial p_T is isolated among ALL one-variable expressions, EVERY
labeling of T by x_1,...,x_n, for EVERY n>=1, is isolated among ALL expressions
in these variables. Repetitions and unused labels are allowed. No size,
parameter, subtree, degree or domain restriction is introduced. Equality
on the real domain is polynomial equality. Source Lemma 2 uses global
one-variable injectivity, not just isolation of this T. Its expansion of a
chosen color to F(x,x) cannot supply the missing local-to-global implication.
Source Propositions 6/7/9 and Remark 8 are special reconstruction results;
their actual nearby bodies were read and do not assert arbitrary isolated-T
label recovery. Predecessor all-order gcd/substitution deductions are helpers,
not source resolutions. No public theorem is used as a black box in this lane.

Before new mathematical work, inspected/reused the specifically authorized
complete registry trees/head receipts in sol-fresh-analysis-discovery-r7,
retrieved 2026-10-29T04:39:40–44Z. registry-screen.json records their URLs,
hashes, exact commits, dates, completeness flags and target-path matches.
Heads: Omega 67b4fae085cf19003a33f8027410c383b49e5046,
count-ex-machina dbf673741a54c7dc9d88a6aec0e8148a538f4a3a,
OpenAI math 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a.
No matching Tian/Friedman polynomial target was identified in these path
lists or the inspected count registry. Substring matches such as Hermitian,
Egyptian, unrelated Tian graph theorems and another Friedman are not relevant
proofs. This is explicitly DATED PATH coverage, not current full-text clearance.
No post-04:39 head claim or GitHub API refresh is made. Recent rate limits
were respected. MathDB's inherited 403 leaves current solution/reply bodies
unread; no request to that host was made. Live targeted searches on this
research date located the source and old discussions, not a resolution;
absence from results is not novelty evidence. No novelty clearance is claimed.

## Independent verification of root deductions FIRST

Give the leaves distinct indeterminates z_i and set
w_i=(partial P_T/partial z_i)(x,...,x). If L_i,R_i count left/right edges,
chain rule gives exactly

    w_i = 2^L_i 3^R_i v_i,

where every left edge contributes its child polynomial once to v_i and every
right edge its child polynomial twice. This formula is in Z[x], not a
numerical quotient. Nonvanishing modulo 2 and 3 needs an induction, rather
than an assumption about positive coefficients surviving reduction.

For any labeling, in characteristic 2, differentiation at F(A,B) discards
the left branch and gives B² partial_j B. Simultaneously induct that B and
the derivative for its rightmost label are nonzero. Their product in a
polynomial-ring domain is nonzero, proving both the parent's indicated
derivative and its polynomial nonzero. All derivatives for other labels
are zero. Repeated labels create no exception: only the rightmost branch
survives. In characteristic 3 use -A partial_j A and the leftmost branch.
The base leaf has indicated derivative 1 and nonzero polynomial. Thus every
subtree polynomial is nonzero in both characteristics, so every v_i is.
This proves the exact coefficient-content valuations v_2(content w_i)=L_i
and v_3(content w_i)=R_i. Nonzero derivatives also show that a labeled
identity must preserve the two extreme labels, but not all interior labels.

For C, choose a nonempty {-1,0,1} relation among w_i, select its smallest L,
divide by 2^L in Z[x] and reduce modulo 2. Terms of larger L disappear and
all the other nonzero coefficients reduce to 1. Fixed-L independence would
contradict this. If two labelings of an isolated T were equal, diagonal
specialization first identifies their trees; differentiation in a color
that differs at a leaf yields precisely such a nonzero signed relation.
This verifies the full-scope implication claimed by root. It does NOT
prove C. The symmetric fixed-R independence criterion over F_3 also suffices:
a nonzero signed coefficient remains nonzero modulo 3 after the minimum-R
reduction. Neither independence assertion is assumed here.

The independent executable uses literal multivariate differentiation, not
root's bitset recurrence, to check the six-leaf witness, exact contents and
both extreme-label derivatives. It reproduces root's two degree-17 h columns
whose sum is x^11+x^8 (hex 0x900). Root's 23,714-tree result is inherited bounded
evidence and was neither extended nor re-counted.

## An exact all-order Hasse filtration, with its missing bridge explicit

Work now over F_2. Set p_T=P_T(x,...,x) in F_2[x]. For each leaf define K_i
by the following recursion, with its left-depth L_i:

    leaf: K=1;
    left child: K_i(T)=K_i(A)^2;
    right child: K_i(T)=p_B^2 K_i(B).

All K_i are nonzero. If only z_i is replaced by x+t, then

    P_T(x,...,x+t,...,x)-p_T
      is divisible by t^(2^L_i),
    [t^(2^L_i)] P_T(...,x+t,...) = K_i.                 (H)

Proof by induction: a left difference squares, doubling its initial t-order
and squaring its coefficient. For a right difference delta, the change in
a cube is b² delta+b delta²+delta³; its initial coefficient is b² times
the child's, because b is nonzero and delta has positive t-order. This proves
(H) and nonvanishing, without any independence assumption.

More generally take two binary masks c,d and let m be the minimum L_i among
positions where they differ. Put R_c=P_T(x+t c_i). Then

    t^(2^m) divides R_c-R_d,
    [t^(2^m)](R_c-R_d)=sum_{i: L_i=m, c_i!=d_i} K_i.    (J)

Here the first coefficient MAY vanish. To prove (J), recurse on differences
of the two child series. At a left edge the difference squares. At a right
edge factor the cube difference; the second factor has constant term p_B².
Lower orders agree, so only that constant can contribute at the first
possible discrepancy order. Two child contributions add. Repeating gives
exactly the displayed sum; equal positions contribute zero. This argument
also covers lower-depth leaves whose labels agree in both masks, even when
the common label is x+t: all child series still specialize to p_child at t=0.

Thus fixed-left-depth F_2 independence of the K_i is ANOTHER sufficient
all-order criterion for the full source conjecture. It distinguishes binary
masks by (J). Binary separation suffices for arbitrary labels: map a color
that differs at some position to u and all other colors to v. Distinct
labelings remain distinct at that position. A binary polynomial identity
is equivalently tested after u=x+t,v=x, an invertible linear substitution.
Isolation of T then removes arbitrary competing shapes as above.

This is a conditional reduction, NOT a genuinely adequate completed
replacement separation argument. Independence of K for arbitrary isolated
T remains unproved. It must not be inferred from individual nonvanishing,
positive integer coefficients, or the name 'Hasse derivative'.

The analogous F_3 filtration has first possible order 3^R_i and signatures

    leaf: J=1;
    left child: J_i(T)=2 p_A J_i(A);
    right child: J_i(T)=J_i(B)^3.

For two binary masks, the first possible discrepancy coefficient is the
sum of (c_i-d_i)J_i over the minimum-R positions. Cubing is Frobenius and
(c_i-d_i)^3=c_i-d_i in F_3; squaring differences have initial multiplier
2p_A. This proves the analogous formula by the same induction. Fixed-R
independence would again suffice, but is unproved. No finite F_3 rank
survey was substituted for that bridge.

## Exact obstacles: the Hasse route does not restore the easy proof

Put q=x²+x³, B=q²+x³, and use root's six-leaf tree

    T=F(F(x,F(x,x)),F(F(x,x),x)).

Its zero-based leaves 2 and 4 both have L=1. Over F_2,

    K_2=x^4 q^4=x^16+x^12,
    K_4=x^4 B²=x^16+x^12+x^10,
    K_2+K_4=x^10 !=0.

Both degrees are 16. Consequently distinct-leading-degree separation is
false for the Hasse signatures too. The two masks differing exactly at
these two positions agree at all L=0 leaves; their t² discrepancy is x^10,
as independently checked by literal bivariate expansion. This is neither
a K dependence nor a counterexample to C or Tian.

There is a precise connection at L=1: if h_i=bar(w_i/2), then

    d h_i/dx = K_i.                                    (D1)

Indeed the unique left edge contributes an unsquared factor a; all the
right-edge factors above and below it are squared. Write the product of
right-child polynomials above that edge as U and below as V. Then
h_i=a U² V², while a'=V² by the rightmost derivative formula. Hence
h_i'=U² V^4. The recursion defining K gives exactly U² V^4.
This verifies (D1) at all orders and shows K independence at L=1 implies
C there. The converse is not supplied: differentiation has a kernel.

The tempting generalization D^[2^L-1] h_i=K_i, using Hasse derivatives
in x, is FALSE. On the same tree, leaf 0 has L=2 and

    h_0=x^10+x^9+x^8+x^7+x^3,  K_0=1,
    D^[3] h_0=x^4+1 !=1.

This follows directly from D^[3]x^j=binom(j,3)x^(j-3), reduced modulo 2.
Thus repeatedly differentiating normalized gradients cannot silently
identify the two filtrations. Extra product-rule terms need control.

## Strongest remaining objection and status

No all-order independence theorem for h_i or K_i on arbitrary isolated T
has been established. Neither fixed-depth leading degrees, content valuations,
extreme-label differentiation, nor the Hasse first-discrepancy formula proves
that a nonempty signature sum cannot vanish. Failing any sufficient criterion
would still not refute the full source; an actual labeled polynomial identity
on an isolated T is required. Isolation imposes no proved restriction here
that eliminates the overlapping-factor obstruction in r2. The earlier
infinite substituted envelope failures and the non-composition common-root
example remain in force. No stronger hypothesis replaces the source target.

Run `python check.py` in this lane. It enforces 512 MiB address space,
40 CPU seconds and BLAS/OMP/MKL threads 1 before SymPy import. All targeted
checks pass. No rank survey, floating-point argument, numerical proof, Lean,
public upload, git operation, browser tab, child or other-lane edit occurred.
