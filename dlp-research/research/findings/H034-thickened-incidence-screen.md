# H034 deterministic thickened incidence: seed-saving premise and penalty

Status: new PAPER alternative, not the frozen diagnostic. Root proposed;
independent Astra graph/probability reviews and Sol generation/batching review
completed. Balanced-parameter cost substitutions below are root deductions with
Astra moment review; they are not a complete-cost win, Lean theorem or novelty
claim. No numerical run. Shared inverse arithmetic and birthday constants remain
prior art. Existing AGG source application is documented in the mathematical
screen; this record derives the particular graph counts directly.

## Concrete deterministic graph

Over prime Fell, retain point vertices(x,y) and line vertices(s,t), 2ell² total.
For S={0,...,k-1}, 1<=k<ell, include the edge exactly when y-sx-t belongs to S.
It is simple, bipartite, regular of degree d=ell*k, with ell³*k edges. No stored
edge list, random graph sampler or duplicate-edge bitset is required. Labels
at all vertices remain IID uniform in Fq²; this randomness is still paid.

Enumerate line(s,t), x, then r in S, with y=sx+t+r modulo ell. For each line
hold b=t and point-row base X=0. For each x, start y=b, emit k edges with point
index X+y while incrementing y cyclically, then b<-b+s mod ell and X<-X+ell.
Maintain the edge ordinal by incrementing it. This uses bounded additions and
comparisons per edge, not unavoidable per-edge multiplication or division.
Its exact comparison with an optimized old iterator is still required.

The descriptor ordinal is e=((s*ell+t)*ell+x)*k+r. On an exact match, divide
first by k, then decode x,t,s in base ell; reconstruct the point coordinate.
Compared with old decoding, one extra division/remainder is paid. It does not
occur on unequal hash probes. The edge descriptor retains its cap-sized width.

For cap E=ceil(3sqrt(q)/2), choose the least qualifying prime with
4ell^6*k(ell)^2>=9q, scanning integers and checking primes/predicate exactly.
Do not assume a sizing predicate with floors is monotone. For the original
k=floor(ell/bitlength(ell)) proposal, prime127 gives k18 whereas131 gives k16;
the predicate drops. Bertrand bounds suffice for coarse Theta sizes; no exact
prime-spacing equivalent is asserted. Trial-division search and parameter work
are paid uniformly, not public advice.

## Exact form count and the role of parallel lines

Two different-slope lines have exactly k² common point neighbors: every ordered
(r,r') in S² uniquely determines(x,y). Distinct residue pairs cannot give the
same point. Parallel distinct lines have codegree ell*|S intersect(S+c)| for
an appropriate nonzero c, at most ell*k.

For any edge prefix, put

    D=binom(m,2)-sum_v binom(deg(v),2),
    C4=sum_{line pairs} binom(codegree,2).

The count of distinct four-support signed equations modulo global sign is EXACTLY
N=8(D-C4). A bipartite four-set has at most two perfect matchings; the second
exists precisely in a4-cycle and repeats the same eight forms. This differs
from unrestricted complete graphs, where three matchings can coincide.

For R complete lines and m=R*ell*k, a coarse bound gives
N/(4m²)=1-k²/(2ell²)+O(1/ell) when R=Theta(ell²). That relative expansion does
not describe the very first few lines. The sharper interval-S bound below
resolves the prefix issue for quantitative stopped costs.

Each line has nonzero codegree with at most2(k-1) parallel partners. Thus
parallel4-cycles total O(R*ell²*k³)=O(m*ell*k²), improving the coarse bound that
allowed every parallel pair. Combining the different-slope cycles, adjacency
terms and at most one partial line yields the UNIFORM ABSOLUTE estimate

    N(m)=4m²*(1-k²/(2ell²))+O(m*ell*k²).

It covers small m as an absolute bound. Completing a partial line changes counts
by O(m*d), absorbed above. The exact graph event assumptions remain odd prime q,
independent uniform labels, and geometry-first relation selection.

## Collision law and a rejected overly optimistic setup inference

Deduplicated four-support forms have marginal1/q and pairwise1/q² probabilities.
Variable-overlap neighborhoods have size O(d*m); disjoint variable sets give
the needed joint independence. The previously checked AGG zero-event bound
therefore applies, and lower-support events are O(md/q). For t=2m<=3sqrt(q),
survival differs uniformly from exp(-t²/q) by

    O((k/ell)² + ell*k²/sqrt(q) + d/sqrt(q)).

Integrating across the fixed cap and charging full-batch overshoot gives an
expected candidate-key error of

    O(sqrt(q)*(k/ell)² + ell*k² + d).

Seed exceptions have probability O(ell^4/q); their capped-key/fallback effect
is O(ell^4/sqrt(q))=O(ell/k) under the sizing regime. Conditional mark arguments,
null recovery, direct input dispatch and paid fresh fallback remain as before.

The initial choice k=floor(ell/bitlength(ell)) gives
ell=Theta(q^(1/8)(log q)^(1/4)), roots=Theta(q^(1/4)sqrt(log q)). It preserves
the ideal limiting collision constant, since k/ell tends to zero. However,
root noticed that the repeated-form loss creates an additional key term of
order sqrt(q)/(log q)² in this model. That exceeds the old q^(1/3)log(q) seed
scale. Merely combining reduced seed cost with inversions/overshoot would miss
this penalty. That optimistic aggregate inference is REJECTED.

## Batching correction and a balanced alternative

Sol identified a second trap: using natural batches of size ell_new raises
inverse count to Theta(q^(3/8)/(log q)^(1/4)) for that initial choice. Root's
full-line repair was independently accepted: batch all d=ell*k edges of each
fixed line, truncating only the final line at E. All source points are known;
batch inversion needs nonzero denominators, not statistical independence.
The existing complete seed scan guarantees these denominators on leaf entry.

There are at most ceil(E/d)<=ell² batches, scratch10d field entries plus2d
integer/exception entries, and fewer than2d prepaid keys past the inspected hit.
Every regular batch retains(5b-3)M+2bS+6bA+I. This removes the inverse-count trap,
but does not remove repeated-form collision loss or leading enumeration costs.

Root then proposed balancing that loss against seeds using k=floor(cuberoot(ell)).
With the same least-prime/cap rule,

    ell=Theta(q^(3/20)), roots=Theta(q^(3/10)), d=Theta(q^(1/5)).

Astra independently checked the sharpened uniform moment bound under this rule.
Its four error terms are respectively O(q^(3/10)), O(q^(1/4)), O(q^(1/5)) and
O(q^(1/10)) for repeated forms, prefix correction, dependency/overshoot and
seed events. Thus, writing a=integral_0^3 exp(-x²)dx,

    E[T_candidate]=a*sqrt(q)+O(q^(3/10)).

Root's elementary cost substitutions give O(q^(3/10)log(q)) eager seed group
operations, O(q^(3/10)) batch inversions, and O(q^(1/5)) scratch/overshoot.
The additional native balanced-cost follow-up failed with 'agent thread limit
reached' and was NOT run; these substitutions are not falsely attributed to it.
They follow the independently reviewed general full-line formulas.

Do not hide the fallback's own remainder. If its expected key cost is
cB*sqrt(q)+RB(q), the total key count is

    (a+cB*exp(-9))*sqrt(q)+O(q^(3/10)+|RB(q)|).

An unspecified o(sqrt(q)) fallback remainder is not O(q^(3/10)). Full weighted
work also retains random bits, prime search, graph indexing, root/leaf traffic,
hashing, allocation, verification and clearing. A positive new leading per-edge
charge could dominate every subleading saving. The upper bounds are therefore
candidate-specific mathematical progress, not verified whole-solver improvement.

## Process and next decision

Root proposer/integrator; /root/h007_additive_relations independent graph and
uniform-probability reviewer; /root/h010_early_dependencies independent original
generation/full-line batching reviewer. No runs, imports, edits or children by
reviewers. The separate writer implements ONLY the older frozen C4-free test.
The initial logarithmic-thickness proposal and its failed inference are retained.

Next cheap checks: explicit common-cost iterator comparison and fallback remainder,
then independent prior-art and source review if a complete-work regime survives.
No new experiment, Lean infrastructure or challenge alteration follows. The
square-root main exponent and verified-improvement status NONE are unchanged.
