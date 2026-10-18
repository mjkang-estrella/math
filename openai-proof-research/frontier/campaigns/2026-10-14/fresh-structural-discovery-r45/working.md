# Hamiltonian-preserving exact repair: exact calculations and unpaid interfaces

This is a pre-freeze author work note, not a proof of a proposed full theorem.

## Source notation

Fix d≥3, q=d−1, s=2√q. For a simple d-regular G with a specified Hamilton cycle C, put F=G\C, k=d−2. Let v_i be an orthonormal adjacency eigenbasis on 1-perp, λ_i the eigenvalues, and x_i^σ=s−σλ_i. The source ideal switch kernel is

K_σ=(d−2)^{-1} [[−s,σd],[σd,−s]].

For oriented edges g=(u,v), j=(x,y), write z_i(g)=(v_i(u),v_i(v)). The ideal near correction is H_ik^σ=(z_i(g)−z_i(j))^T K_σ(z_k(g)−z_k(j)). The actual switch deletes uv,xy and adds uy,xv.

## Off-cycle restriction changes the mean

For independent uniform oriented F-edges, each endpoint is uniform on vertices and E z_i=0. If B_ij=<v_i,A_F v_j>, then

E[z_i(g)z_j(g)^T]=(1/n)[[δ_ij,B_ij/k],[B_ij/k,δ_ij]].

Consequently E H_ij^σ=4/((d−2)n)[−sδ_ij+σd B_ij/k]. This is not the source's −4x_i^σ δ_ij/((d−2)n). At a near-edge unit vector v, the leading drift at σλ≈s is proportional to (2s−σd<v,A_Cv>)/k. The source assumptions have not been shown to give the needed favorable sign. This exact identity disproves reuse of the original covariance identity; it is not an example refuting the desired repair theorem.

## A same-type mixture restores precisely the first moment

Choose cycle-cycle with probability2/d, and F-F with probabilityk/d. In the F case draw independent uniform oriented F edges. In the cycle case choose a global orientation of C uniformly, then draw two independent edge positions; orient g forward and j backward in that global orientation. Given the type and global orientation, both endpoint means vanish, and the draws are independent. The marginal of each slot is the uniform oriented G-edge law after averaging the type and orientation. Thus the cross terms E z_i(g)z_j(j)^T vanish and the summed single-slot covariances equal those in the source. Hence

E H_ij^σ=−4x_i^σ δ_ij/((d−2)n)

exactly. The joint pair law has a density bounded by a constant depending only on d relative to two uniform oriented G edges (it excludes mixed types and half of the cycle orientations).

A valid cycle-cycle switch of this orientation is a 2-opt reversal and leaves one Hamilton cycle. An F-F switch leaves C untouched. This statement is about one switch only.

## Two individually valid disjoint reversals can jointly split the cycle

Take the cycle 0,1,2,3,4,5,6,7,0. Switch A deletes01,45 and adds04,15. Switch B deletes23,67 and adds26,37. Either switch alone produces one 8-cycle. Their endpoint sets are disjoint. Together they produce two 4-cycles: (0,4,3,7) and (1,2,6,5). All inserted edges are distinct nonedges of the original cycle.

This disproves the shortcut “vertex-disjoint cycle-preserving 2-opt switches preserve the Hamilton cycle simultaneously.” It does not prove that a surrounding d-regular graph has no other Hamilton cycle, and does not satisfy or contradict the source's large-n spectral hypotheses. The same interleaving pattern embeds in longer cycles by subdividing untouched arcs.

## Exact debts remaining

1. The source projector tilt relies on full-edge covariance diagonal in the adjacency eigenbasis. Restoring the un-tilted mean by a same-type mixture does not imply that its tilted covariance has the same positive bias. Conditional type/orientation covariances need a separate argument or a new tilt.
2. Reorienting each cycle switch against the current Hamilton cycle preserves that cycle sequentially. It makes the switch law history dependent. The source pairwise-independent Frobenius cancellations and affine-seed enumeration therefore do not apply without a new proof.
3. Conditioning independent switches on a globally connected resulting cycle does not inherit the source moment bounds merely from pointwise one-switch density bounds. A small conditioning probability could amplify the source error probabilities.
4. A random constructive proof would still need conditional drift and concentration. A deterministic polynomial algorithm additionally needs an efficiently searchable distribution or pessimistic estimator; no such algorithm is supplied here.
5. Starting the source's empty-pairing construction with a fixed Hamilton cycle is a separate unpaid initial-account interface, not a consequence of the final repair theorem.

No implication of impossibility is made from these failed routes.
