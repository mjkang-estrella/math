# Frozen statement — fresh-structural-discovery-r135

Frozen 2026-10-20, before proof drafting. Provenance: Factory Droid / claude-opus-5-5 / high.
Pinned source revision stipulated true: openai/math commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
(the preprint `preprints/The-crossing-number-of-complete-bipartite-graphs-September-23-2026`,
Theorem thm:main: cr(K_{m,n}) = d_m d_n). This file is the exact frozen scope; the proof obligation
is the statement below, unchanged.

## Conventions (fixed)

A *drawing* of a finite graph in the plane: vertices are distinct points; each edge is a simple
continuous arc joining its endpoints whose interior avoids all vertices; interiors of two edges meet
in finitely many proper crossings (transverse double points); there are no triple crossings, no
tangencies, and no common subarcs of two edges. Two edges are *adjacent* if they share an endpoint,
and *independent* otherwise.

For edges e, f of a drawing D, write chi(e, f) in {0, 1} for the parity (odd = 1, even = 0) of the
number of crossings of e with f. A drawing D is *even-adjacent* if chi(e, f) = 0 for every pair of
adjacent edges e, f. (This is the drawing class called "weakly semisimple" by Balko--Fulek--Kyncl;
terminology here is self-contained.)

Write oc(D) for the number of unordered pairs {e, f} of edges of D with chi(e, f) = 1. In an
even-adjacent drawing every such pair is independent.

For a positive integer r, put
    d_r = floor(r/2) * floor((r-1)/2),
equivalently d_r = C(floor(r/2), 2) + C(ceil(r/2), 2).

## Theorem (frozen)

For all positive integers m, n:

(1) (Lower bound, parity form.) Every even-adjacent drawing D of the complete bipartite graph
    K_{m,n} satisfies
        oc(D) >= d_m d_n.

(2) (Exactness.) There exists a drawing of K_{m,n} in which adjacent edges do not cross at all,
    every two edges cross at most once, and exactly d_m d_n pairs of edges cross (namely the
    balanced-axis drawing with generic axis intercepts).

## Immediate consequences (part of the frozen scope)

With the crossing-number variants
    ocr+(G)  = min over drawings of G with no adjacent crossings of the number of oddly crossing
               unordered edge pairs,
    ocrpm(G) = min over even-adjacent drawings of G of the number of oddly crossing unordered edge
               pairs,
    pcr+(G)  = min over drawings of G with no adjacent crossings of the number of unordered edge
               pairs that cross at least once,
the Theorem gives, for all positive integers m, n:
    ocrpm(K_{m,n}) = ocr+(K_{m,n}) = pcr+(K_{m,n}) = d_m d_n,
and, quoting the pinned Theorem thm:main (cr(K_{m,n}) = d_m d_n), these three quantities coincide
with the ordinary crossing number on K_{m,n}. (Derivations: the lower bound of (1) applies to both
restricted classes; the drawing of (2) gives all matching upper bounds, and crossing pairs >= odd
pairs in any drawing gives the pcr+ lower bound from (1).)

## Explicitly not claimed (frozen limits)

- No determination of the unrestricted odd, independent odd, or pair crossing numbers ocr, iocr,
  pcr of K_{m,n}: the argument needs the even-adjacent hypothesis to control the diagonal blocks,
  and removing that hypothesis is not part of this scope.
- No statement about Harborth-type formulas for complete tripartite graphs K_{l,m,n} (studied
  prefreeze and found infeasible in this round; see working notes).
- No worldwide-priority or count claim; novelty limits are documented in reading-limits.md and
  report.md.

## Source dependencies

Logical: none beyond the pin being stipulated true; the proof is self-contained (the needed linear
algebra is re-proved over characteristic-2 fields). Methodological: the proof transports the pinned
preprint's operations (cycle pairing lem:cycle-pairing, additive block relation lem:additive,
subspace bound lem:subspace, rank-sum corollary cor:rank-sum, rank detector lem:detector with
lem:triangular-basis, odd/even deletion of sec:formula) to parity data; the transport requires new
steps listed in the proof's provenance discussion. The upper bound is the classical axis
construction (Woodall, as recorded in the pinned preprint's sec:formula).
