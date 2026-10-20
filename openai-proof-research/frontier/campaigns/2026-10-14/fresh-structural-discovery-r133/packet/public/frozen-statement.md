# r133 frozen statement (written before proof drafting; do not edit)

Round: fresh structural discovery r133, 2026-10-20. Provenance: Factory Droid / claude-opus-5-5 / high.
Pin: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (stipulated true, including operative proof operations).
Family: 106 (Hardness of coloring three-colorable graphs). Source:
preprints/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026.

Conventions. Graphs are finite, simple, undirected and loopless unless a loop is mentioned.
C_N is the cycle on Z_N with i adjacent to i+1 and i-1. X -> Y means a graph homomorphism exists.
alpha(X) is the independence number. A graph is bipartite iff it has no odd cycle.

## Theorem A (odd-cycle completeness with vanishing independence ratio)

For every fixed integer k >= 1 and every fixed real delta > 0 there is a deterministic
polynomial-time algorithm R_{k,delta} that maps each explicitly encoded Boolean 3-CNF formula phi to a
nonempty finite simple undirected unweighted graph G_phi such that

- if phi is satisfiable, then G_phi -> C_{2k+1};
- if phi is unsatisfiable, then alpha(G_phi) < delta |V(G_phi)|.

The running time and output size are polynomial in the binary encoding length of phi; the
constants and the polynomial degree may depend on (k, delta) but not on phi.

## Corollary B (Brakensiek-Guruswami conjecture, as stated in KOWZ Conjecture 1.2)

Let H and G be finite loopless undirected graphs with H non-bipartite and H -> G. Then it is
NP-hard to distinguish graphs X with X -> H from graphs X with X -/-> G (the decision problem
PCSP(H, G)). Consequently the search problem (given X with X -> H, output a homomorphism X -> G)
is NP-hard under polynomial-time Turing reductions.

Stronger form proved on the way: for H non-bipartite and every fixed delta > 0, it is NP-hard to
distinguish H-colourable graphs from graphs with alpha(X) < delta |V(X)|.

## Proof plan fixed before drafting

Run the 106 construction with the half-shift threshold 1/8 replaced by rho = 1/(4k+2) in the clique
test and edge rule, bump slope 1/rho, Lipschitz constant L = 2/rho = 8k+4; verify the soundness
interface (f odd, [-1,1]-valued, equal to 1 on A, constant across zero links, L-Lipschitz within
copies) and rerun the source parameter order with this L. Completeness: colour by the 2k+1 arcs
[i/(2k+1), (i+1)/(2k+1)). Corollary B: odd cycle in H and fibre counting for loopless G.

Novelty scope at freezing: new to this project. Literature status recorded in working-notes Step 5
(BG described as known only under the Rich 2-to-1 Conjecture in arXiv 2605.09815v2, 18 Oct 2026).
No worldwide-priority claim. Contribution and correctness are for separate reviewers.
