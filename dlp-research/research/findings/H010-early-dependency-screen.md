# H010 early dependencies: two supplied operations fail the work gate

Native Sol /root/h010_early_dependencies completed an isolated initial proposal.
No edits, experiments, numerical scratch or children. Root records the actual
operations with scope corrections below. Verified improvement NONE; ordinary
full-range classical square-root reference unchanged.

## Even circuits from unlabelled-anchor secants

Build a paid pool of B distinct points U_i with unknown logarithms. Independently
sample a,b, set R=aG+bQ, choose a uniform pool anchor U_i, and look up
W=-R-U_i in the pool. A match U_j gives the verified edge

    U_i+U_j+aG+bQ=O.

An even circuit with alternating edge signs cancels the anchors. If the resulting
Q coefficient is nonzero, recover k and verify kG=Q. A constructed sum of labelled
identities is insufficient: the independent target labels and coefficient check
are essential. Odd cycles alone generally retain an anchor. Parallel edges are
allowed as length-two circuits; loops alone do not eliminate their anchor.

For a fixed pool and independent uniform target, the one-anchor lookup succeeds
with probability B/q before excluding degeneracies. Successful ordered endpoints
are uniform. For m=o(B) independent uniform edges, the expected number of useful
circuits tends to zero; the usual cycle-count sum is bounded by a convergent
geometric sum in O(m/B), including parallel edges. Thus constant-probability
occurrence needs order-B edges and order-q attempted one-anchor queries. Labelled
point generation, memory, graph maintenance and final verification add cost.
The proposer gave no biased geometric edge producer that changes this law.

An optimistic constant-cost whole-pair reporter has mean available edges <=B²/q
for a uniform target. Under an ADDITIONAL uniform-edge/circuit assumption,
B+q/B already balances at square root. Root does not apply that assumption to
every correlated batch reporter: the reviewed rejection is of the actual
independent one-anchor operation. No reporter oracle is supplied.

Graph cancellation and geometric relation generation are established prior art:
[Diem, sections1 and3](https://jtnb.centre-mersenne.org/item/10.5802/jtnb.815.pdf).
Higher-genus results do not transfer automatically. A coordinate-aware sampler
producing useful circuits unusually early with paid labels could reopen the
question, but changing the graph elimination routine alone cannot.

## Repeated-point divisor certificates with one auxiliary unknown

Choose Q'=A0G+B0Q with B0 nonzero and one independent unknown-log point U.
For multiplicities 0<=a,b,c<=L<q and b>0, seek a function with divisor

    a(G)+b(Q')+c(U)-(a+b+c)(O).

For distinct finite support points, the standard L(sO) basis, s=a+b+c, supplies
a square Hermite evaluation matrix of local jets. Its nonzero kernel certifies
exactly the required zeros: total zero degree already equals the pole bound.
Each certificate gives (a+b A0)+b B0 k+c u=0 mod q, where U=[u]G. Two certificates
with nonzero determinant in the k,u coefficients recover k; verify it. Duplicated
or dependent certificates are failures, not new information.

Root qualification: G,Q',U must be distinct finite support points, or repeated
locations must be merged with summed multiplicities. Stacking duplicate jet
constraints at coincident points would be unsound. Nonzero/membership/distinctness
conditioning is not exact iid sampling. The following count is in the ideal iid
group-point model; any transferred probability needs the declared conditioning.

For every fixed admissible triple in that model, b is nonzero modulo q, so the
principal-divisor group relation has probability1/q. First moment gives at most
O(L³/q) expected certificates. Constant probability of even one certificate needs
L=Omega(q^(1/3)); this is necessary, not sufficient for two independent useful ones.
With only G,Q', the analogous bound is O(L²/q).

The supplied producer exhaustively enumerates the multiplicity cube. It visits
Theta(L³) profiles, already Omega(q) at that necessary scale, before paying jets
or rank computations. This is the decisive full-sweep screen. Straightforward
dense matrix tests have a loose O(L^6) whole-sweep upper bound, but an expensive
upper bound alone is NOT a lower-bound proof. Root does not use that raw argument
to exclude faster structured searching or every early-stop strategy.

On an elliptic curve, direct group-sum testing also checks this principalness
condition; constructing a jet engine is not necessary just to test a prescribed
triple. Neither representation supplies a cheap selector of good triples.
Primary prior art cited by proposer discusses multiplicities:
[Mahalanobis–Mallick, section3.1.3](https://arxiv.org/pdf/1703.07544).

The omitted rank-one dictionary idea overlaps known labelled decompositions;
[APS, sections3–3.2](https://iris.unitn.it/retrieve/handle/11572/202653/186850/Amadori,%20Pintore,%20Sala%20-%20On%20DLP%20for%20prime-field%20EC%20(rev).pdf)
already removes a linear-algebra stage while leaving the expensive selector open.
No novelty or faster full solver established. No matrix engine or numerical pilot
is justified by either supplied operation. These findings do not prove all
solvers require Theta(B) factor-base rows.
