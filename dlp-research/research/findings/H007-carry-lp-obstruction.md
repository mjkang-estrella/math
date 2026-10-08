# H007 CARRY-LP-v1: composed fractional witness defeats early pruning

Verdict: reject the frozen v1 as an improvement candidate. Its exact circuit is
correct and exact infeasibility pruning is sound, but expected search has
Omega(n) LP nodes for uniform full-range scalars. No LP experiment is needed.
This is reviewed paper evidence, not a Lean theorem or a general bound on
carry methods, stronger relaxations, integer programming or coordinate attacks.

Specification: ../hypotheses/H007-carry-lp-v1.md. Proposer native Astra
/root/h007_lattice_carries; independent adversary /root/h007_additive_relations;
root checked the composed assignments, flag products, scalar range and node bound.
No implementation, numerical scratch, experiment or new assumed axiom.

## Exact circuit and relaxed products

Total affine gadgets and gate counts check out. Every true execution satisfies
all envelopes and rounded carry bounds. The issue is too many false executions.
Put M=p-1,t=M/2. All wire intervals below are the frozen syntactic intervals,
not new intervals inferred from a fractional witness.

A full-field product at values x,y in[1,M-1] has McCormick bounds
lo=max(0,M(x+y-M)), hi=M*min(x,y).
For ANY canonical output z, choose W=max(z,lo), c=(W-z)/p.
Since hi>=M and lo<=M²-2M, this gives lo<=W<=hi,0<=c<=p-2.
Boolean output z=1/2 also works under its correctly rounded carry bounds.
For a square at x in[1/2,M-1/2], outputt works similarly:
lo=max(0,2Mx-M²), hi=Mx, withhi>=t andlo<=M²-M<t+p(p-2).

Boolean-times-field products instead have carry forced0. At operands(1/2,t)
their ordinary envelope is[0,t], which remains permissive enough below.
Boolean-times-Boolean at(1/2,1/2) allows any output in[0,1/2].

## Entering a two-bit suffix

Take an exact prefix with next alternatives D0 andU0=D0+G both finite,
with unequal x and unequal y coordinates. Set the next bit to1/2.
Its selector interpolates the known coordinates exactly, giving R=(x,y,0),
x in[1/2,M-1/2], y in[1,M-1/2]. The coordinates remain symbolic after
forward simplification because the two alternatives differ. Finite points in
the odd-order subgroup have nonzero y.

## Double to (t,t,1/2)

Assign d=min(2y,M-1), with carry(2y-d)/p in[0,1].
Thus d in[1,M-1]. Every subsequent Fermat-inverse accumulator can be t.
Set a=x² outputt by the square construction. Then use:

| Wire | Value | Affine carry or product rule |
|---|---|---|
| h=3a+A | t | (M+A)/p |
| lambda=h*v | t | W=t,c=0 |
| q=lambda² | t | W=t,c=0 |
| xstar=q-2x | t | -2x/p |
| delta=x-xstar | t | (x-M)/p |
| lambda*delta | t | W=t,c=0 |
| ystar=lambda*delta-y | t | -y/p |
| z=d*v | 1/2 | full-field product rule |
| H=(1-o)z | 1/2 | o=0 identifies H=z |
| xD,yD | t,t | allowed flag-field outputs |
| oD | 1/2 | 1-H |

Rounded carry ranges are[0,floor((3M+A)/p)] for h (upper>=2),
[-2,0] forxstar, and[-1,0] fordelta/ystar. Every displayed carry fits.
Normalization is tight: xD=yD=M(1-oD)=t.

## Add G to obtain (t,t,0)

Starting from that relaxedD, set d=e=v=w=lambda=q=xstar=ystar=delta=t.
Fermat accumulators stayt. Affine carries are:
- d=x-xG: -xG/p;
- e=y-yG: -yG/p;
- xstar=q-x-xG: -(t+xG)/p;
- delta=x-xstar andystar=lambda*delta-y: -t/p.

These fit their rounded intervals. Forxstar the lower bound is-1 whenxG=0,1
and-2 otherwise, with upper0; the proposed value fits eachcase. Public
zero-coordinate simplifications do not contradict the assigned equalities.

Set H=T=S=1/2 andJ0=J=oU=0. Products dv andew return1/2 withW=1/2,c0.
Boolean-product envelopes permit S=1/2 andJ0=0 at equalhalf operands;
the subsequent products withJ0=0 return0.
Choose flag-field outputs S*xstar=t-xG/2, S*ystar=t-yG/2, both in[0,t].
Then xU=(t-xG/2)+J*x2+oD*xG=t, andsimilarlyyU=t, withcarry0.
The2G terms vanish becauseJ=0. The state U=(t,t,0) is normalized.

## Arbitrary finite endpoint and search cost

Set the last bit to1/2. Both coordinate inputs aret, so each integer mux
product can independently take any value in[0,t]. To output coordinateqQ
choose a=min(qQ,t),c=qQ-a. Both are admissible. Infinity-flag inputs1/2,0
permit both selectorproducts0. Thus ANY finiteQ is feasible.
Additional unknown stages can first select(t,t,0), repeat the same gadgets,
and leave arbitraryQ to the final selector.

At most12 next-prefix states are excluded:2 infinity cases; atmost4 zeros of
x(X+G)-x(X), andatmost6 zeros ofy(X+G)-y(X). The latter rational functions
are nonzero, with distinct poles at-G andO of totaldegrees4 and6.
At fixed prefixdepth D0=2jG; doubling is injective in the odd-prime subgroup,
so there are onlyO(1) exceptional scalar prefixes, not a growing fraction.

At depthL-2, prefixj is the block4j,...,4j+3. Each fullblock below n permits
the fractional scalar4j+3/2<=n-1. The witness extends to ancestors by setting
earlier bits to their exact prefixvalues; forward-only simplification preserves
it. Therefore zero-before-one DFS visits at leastfloor(k/4)-O(1) feasible
blocknodes before finding the unique truek. Uniform k yieldsOmega(n) expected
nodes; upper-half k yieldsOmega(n) nodes. Large LP/certificate/propagation costs
only add work. The directQ=O shortcut does not change this average order.

Scope depends on the exact frozen gates, intervals, one-way propagation and
absence of extra cuts/curve identities. A changed relaxation is a new hypothesis
requiring a new fullcost argument. Do not spend a pilot merely confirming this
paper witness. Verified improvement remains NONE.
