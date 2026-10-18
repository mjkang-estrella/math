# Primary operation comparison and a technical lift corollary

## Actual primary reading

Marcus–Spielman–Srivastava, *Interlacing families I*, Annals182 (2015),307–325, [publisher PDF](https://annals.math.princeton.edu/wp-content/uploads/annals-v182-n1-p07-p.pdf): extracted lines1–175,250–454,700–760 read. The relevant contracts are Theorem3.2 (matching roots), Theorems4.4 and5.2 (selection after partial sign assignments), Theorem5.1 (arbitrary independent sign probabilities, including0 and1), and AppendixA's permutation expansion. Section6's proof of Theorem5.1 was not read; its established theorem is used as a primary dependency, not independently reproved.

Huang–McKenzie–Yau, [arXiv2412.20263](https://arxiv.org/abs/2412.20263), downloaded PDF text lines170–320 read. Corollary1.3 gives positive asymptotic probability for the two-sided Ramanujan event in each fixed degree. The surrounding explanation gives the joint-edge interpretation. The global proof and Remarks3.10/3.12 were not read here. Robinson–Wormald1994's [publisher abstract](https://onlinelibrary.wiley.com/doi/abs/10.1002/rsa.3240050209) states asymptotically almost-sure Hamiltonicity for each fixed degree≥3. Its author PDF retrieval failed with503, and its proof was not read. These statements already make mere simultaneous existence a routine event intersection, not the sought deterministic repair.

## Elementary consequence of the MSS operation — technical only

Let G be a finite simple bipartite graph of maximum degree d≥3 with a specified spanning Hamilton cycle C. Fix signs on C having product−1; leave all remaining edge signs independent and uniform. Write μ_G for the matching polynomial and p for the expected characteristic polynomial of this partially signed graph.

In the determinant expansion, a nonmatching permutation cycle survives averaging only if all its edges belong to C. The only such simple cycle of length≥3 is the whole spanning C. Its two orientations contribute −2 product_C(sign)=+2. All matching terms are unchanged. Thus p=μ_G+2. This is an author deduction from the primary determinant operation, not an assertion that the cited paper states this exact corollary.

Order the C-edges first. The MSS interlacing family restricted to those fixed signs remains an interlacing family, so some completion has largest eigenvalue at most the largest root of p. The latter polynomial is real-rooted by Theorem5.1. Since μ_G(x)>0 for x larger than its largest root, p has no roots there, and its largest root is at most that of μ_G, hence at most2√(d−1). Bipartite spectral symmetry gives the corresponding lower bound for this same completion.

In the associated two-lift, walking once around C changes sheet because its sign product is−1. Its lift is therefore one spanning cycle of length2|V(G)|. Old and new spectra form the lift spectrum. Starting from K_(d,d) and iterating gives Hamiltonian bipartite Ramanujan graphs of orders2d·2^j. Simplicity and degree are preserved. No polynomial-time sign-selection algorithm is asserted.

This is a short fixed-sign determinant/interlacing consequence of classical primary operations, independent of pinned178. It is classified author-side TECHNICAL, not nominated. For nonbipartite inputs the symmetry step is unavailable; no two-sided signing assertion follows from this argument. It does not solve exact spectral repair under the source178 hypotheses or an all-even-order deterministic construction.

## Unpaid operation in the actual178 route

The source178 repair gives the complete Schur-complement reduction, the full-edge tilted drift, local-mass fluctuation bounds, typical-resolvent blocks, rational law approximation, pairwise-independent polynomial seed enumeration, and exact positivity test. Retaining Hamiltonicity is not supplied by deleting a negligible bad-event set: even disjoint individually cycle-preserving switches can split the cycle. The proposed same-type law repairs only its un-tilted first moment. Its positive tilted drift, global connected-cycle sampling, and efficient deterministic search remain unproved. No literature priority is inferred from the bounded search.
