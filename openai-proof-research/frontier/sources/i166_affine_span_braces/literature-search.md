# I166 literature search log

Searches were run in two waves: before building the generation/rank
tooling, and after the computational results, targeting the specific
statements I166 relies on or refutes.  WebSearch (general web index) was
the retrieval tool; no scholarly database behind authentication was
queried.  Absence of hits is reported as retrieval results only, never as
a novelty certification.

## Wave 1 (before computation)

1. `"Hamiltonian cycle space" F2 dimension graph` and variants.
   Hits: Hefetz–Krivelevich arXiv:2606.05835 (cycle space over F2,
   Hamiltonian cycles in pseudorandom/dense graphs), arXiv:2506.19731
   (Hamilton cycle space F2 dimension, dense/random), pseudorandom JCTB
   2025, random regular graphs arXiv:2507.04488.  All concern the F2
   cycle space in dense or random graphs.  Nothing about the real/rational
   affine hull of Hamiltonian cycles in cubic bipartite planar graphs or
   braces.
2. `counting Hamiltonian cycles cubic bipartite planar graphs`.
   Hits: Pivotto–Royle arXiv:1901.10683 (counts in cubic planar graphs,
   including Hamiltonian-cycle enumeration tables), Goedgebeur–Meersman–
   Zamfirescu arXiv:1812.05650 (counts of Hamiltonian cycles in
   k-regular... families, computational enumeration).  These enumerate;
   they do not prove a universal h >= n/2+2 lower bound for the Barnette
   class, and contain no affine-dimension statements.  Their tables are
   consistent with (and much broader than) my sample; I did not re-verify
   their numbers.
3. `Barnette conjecture lower bound number of Hamiltonian cycles`.
   No full-scope duplicate of Q164 found.  Known: Barnette's conjecture
   (existence) is open; Tutte's 4-florette lower bound h >= 3 for
   Hamiltonian... (Tutte's "unique Hamiltonian cycle" work shows h != 1
   for cubic graphs containing one; Smith's theorem gives h even-ish
   parity structure for cubic graphs: the number of Hamiltonian cycles
   through a given edge is even).  Smith/Tutte give h >= 3 for our class
   once one cycle exists; nothing like n/2+2 was found.

## Wave 2 (after computation)

4. `brace theory McCuaig generation theorem planar braces four-cycle
   expansion`.  Hits: McCuaig, "Brace generation", J. Graph Theory 38
   (2001) 124-169 (generation theorem for ALL braces, base graphs include
   K_{3,3} and biwheels; operations richer than the planar C4-expansion);
   Fabres et al. "Minimal braces" J. Graph Theory 2021 / arXiv:1903.11170
   (uses McCuaig's theorem as the induction engine); arXiv:2202.11641
   "Matching Theory and Barnette's Conjecture" (the GSW paper I166 audits
   via the local text copy); arXiv:2408.08128 (2-factor Hamiltonicity
   conjecture note; cites GSW).  Assessment: McCuaig's theorem generates
   general braces and does not claim planar cubic braces are reachable
   from the cube through braces by planar C4-expansions; my certified
   order-18 obstruction (B18) concerns exactly that stronger statement,
   which GSW themselves flag as false in general (their Figure 4
   discussion).  I did not obtain or read McCuaig 2001 in full; it
   remains an unread lead for a possible alternative induction backbone.
5. `affine hull Hamiltonian cycles bipartite graph dimension kernel
   incidence matrix`.  Hits: lecture notes and linear-algebra papers on
   incidence-matrix kernels (unsigned incidence kernel = cycle space for
   bipartite graphs; rank n-1 for connected bipartite).  These confirm the
   classical upper bound d(G) <= n/2+1 used by I165/I166.  No work on the
   affine hull of the Hamiltonian subset.
6. OEIS census cross-check: query `1,0,1,1,2,2,8 cubic bipartite
   polyhedral` returned A007083, "Number of unlabeled trivalent
   3-connected bipartite planar graphs with 2n nodes", citing HMM 1985 and
   Brinkmann-McKay plantri.  Terms at orders 8..20 are 1,0,1,1,2,2,8 and
   match I166's independent census exactly (see census_check.py).  The
   matched bytes are stored as oeis-a007083.txt in this directory.

## Non-conclusions

- No literature source found stating or refuting d(G) = n/2+1 (real affine
  dimension of Hamiltonian-cycle incidence vectors) for cubic bipartite
  planar 3-connected graphs or braces.  This is a retrieval report, not a
  novelty proof.
- McCuaig's brace-generation theorem and the Pivotto-Royle /
  Goedgebeur-Meersman-Zamfirescu enumeration tables are plausible
  independent cross-checks for larger orders; both were left unread in
  full (timeboxing), and are recorded here as concrete next-step leads.
