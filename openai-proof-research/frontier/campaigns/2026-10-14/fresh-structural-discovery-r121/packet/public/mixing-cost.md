# Source259: cheap graphings and the mixing interface

All calculations here preceded any possible freeze. No target was frozen, and no method exclusion below is a candidate for acceptance.

## Actual source and stronger antecedents

The stipulated group is Γ=A *_J (J×〈t〉), where A=F(a,b1,…,b99), u0=1, ui=u(i−1)abi, w=u99a, and J=〈b1,…,b99,w〉. Source `actions:normal-form` embeds the factors, makes J free on the displayed generators and gives infinite order of t. Its `intro:main` supplies Bernoulli cost at least1+η, with η=α/100, 0<α<1/200 and e^96·96^99·α^3/95^95<1/2. These are assumptions here, not audited conclusions.

The full source `actions:small-marker` and `actions:low` proofs were read. All t-edges plus J-generators restricted to a marker of measure p generate the B=J×〈t〉 relation for cost1+100p. The word w recovers the next a-edge from99 consecutive available source heights. On X×Z/M, M>100, this gives cost≤1+99/M. Arbitrary small markers alone are not a cheap Γ-graphing: the a-edge recovery is essential.

Historical I82 §8 already verifies ergodicity of these finite-height actions and keeps the full prescribed ergodic-cost interpolation question open. Parent r2 lifts the graphing to X×Zhat and obtains cost1; its nontrivial rotation factor obstructs strong ergodicity. Arithmetic r30 supplies a stronger weakly mixing spectral-gap cost-one action X×[0,1]^F via a quotient q:Γ→F(c,d), with q(t)=1, q(a)=d, q(u1)=c, q(ui)=1 for i≥2. The proof's availability quantifier is every first coordinate, not one representative of a fiber. Its gap comes from the free subgroup〈w,b1〉.

The actual contribution comparison §2.2 supplies the stronger compatible lift q₂:Γ→F(c,d): q₂(t)=1, q₂(a)=d, q₂(u_i)=c^i, hence q₂(b_i)=d⁻¹c and q₂(w)=c⁹⁹d. For π(c)=π(d)=1, πq₂=χ, the source height. The source's99 initial height fibers become E,Ec,…,Ec⁹⁸ for a small c-marker E. In the propagation step y=vu₉₉⁻¹ has row sources y u_{i−1} in the already available99 translates; yw=va supplies the next a-edge. This gives graphing cost1+100p+99ρ and hence cost1 as p,ρ→0. The images c⁹⁹d and d⁻¹c do not commute, so the restriction to H=〈w,b1〉 is injective; the same Bernoulli restriction gives the previous spectral-gap and weak-mixing conclusions. This is an actual compatible source-row substitution, not merely a negative rating of an earlier author. It was read before this route was archived. No review rating is adopted as a gate for this round.

## A concrete replacement class

Consider Z=[0,1]^I, with independent uniform coordinates, for a countable Γ-set I. On coordinates use (zg)(i)=z(gi), compatible with the source right-action convention. Consider Y=X×Z with product measure, where X=[0,1]^Γ is the ordinary Bernoulli action. This is a natural proposed way to make the auxiliary height system mixing while retaining freeness. The following calculation treats all such I, not a finite sample.

If some i has infinite stabilizer H, choose distinct h_j∈H escaping finite subsets of Γ. For F(x,z)=1_{z(i)<1/2}−1/2, F(·h_j)=F and ∫F^2=1/4. Thus Y is not mixing. This does not depend on whether its restriction to a different subgroup has spectral gap or is mixing. In particular, the r30 factor has an infinite kernel containing〈t〉, so its nonmixing conclusion is an exact correlation calculation.

Conversely, suppose every point stabilizer is finite. For finite coordinate subsets S,T⊂I the set of g with gS∩T nonempty is finite: each individual transporter is empty or a coset of a finite stabilizer. Therefore two cylinder functions have independent coordinate supports for all g outside a finite set. Approximation by cylinders proves mixing of Z, and similarly of X×Z. Empty I gives just X and causes no exception below.

But in this case Y is a free factor of iid. Write I as a countable disjoint union of transitive sets Γ/Hj, with Hj finite. Use one independent ordinary Γ-Bernoulli stream Uj for each j. For a coset γHj define

    Vj(γHj) = 1 − (1 − min_{h∈Hj} Uj(γh))^{|Hj|}.

The expression is independent of the representative γ, since right multiplication permutes Hj. Disjoint cosets use disjoint coordinates, so the outputs are independent. For k=|Hj|, the minimum has distribution function 1−(1−s)^k; this continuous distribution-function transform is uniform on[0,1]. Left multiplication by g permutes the cosets and the input coordinates compatibly, so this is an equivariant factor map onto the jth orbit's iid process. The countable product, together with a separate stream for X, is an ordinary Γ-Bernoulli action with a standard nonatomic product base. The output is free because of X.

Abért–Weiss, [1103.1063v2](https://arxiv.org/pdf/1103.1063v2), Corollary2, says that all free factors of iid for a finitely generated group have the common maximal cost. The relevant proof was read, not just its abstract: §2 proves Bernoulli weak containment by finite partitions, independent labels and a second-moment estimate; §3 Lemmas7–8 and Theorem9 transfer a clopen compact generating graphing along weak containment; the proof of Corollary2 applies both containment directions for free factors. Thus

    Cost(Y) = Cost(X) ≥ 1+η.

No assertion that arbitrary extensions retain cost is used. Indeed the actual source projection Y_M→X decreases cost and already invalidates that assertion. The special fact here is that our proposed replacement is a FREE FACTOR OF IID, with its factor map explicitly supplied.

## Other attempted repairs and exact remaining step

Taking a product of the r30 low-cost action with independent Bernoulli noise preserves its nonmixing quotient: a nonconstant function of that quotient still has constant correlations along t^n. Replacing quotient coordinates by independent Bernoulli fields over their full cosets is not an unproved small perturbation. With a Bernoulli base on each stabilizer, the coordinates reindex to independent Γ-coordinates; it returns to the iid situation above. A nontrivial invariant mixture used as an inner base also leaves nonmixing functions.

These observations exclude these particular product/independent-coordinate repairs. They do not show that every mixing Γ-action is a factor of iid, nor that every mixing action has maximal cost. They do not refute the existence of a free mixing cost-one action. They also do not solve I82's prescribed ergodic-cost interpolation question.

A full construction would need a dependent mixing action whose measurable row-recovery structure yields graphings of cost approaching1 without producing a nonmixing factor. The source's99-step availability and the r30 one-exceptional-coordinate argument do not yet supply such an action. No such compatibility construction was obtained, so no full scope was frozen. The complete route check above is retained only to avoid repeating the same iid repair.
