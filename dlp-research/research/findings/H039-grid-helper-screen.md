# H039 weighted grid helpers: concrete construction, no cost survivor

Status: PAPER proposal and early cost rejection. Native Astra
/root/h007_additive_relations proposed it under the independent H039 higher-arity
lens. Root checked the coefficient construction and recurrence, then screened
the purported source savings against H037's paid IID comparator. No numerical
run, implementation, new Lean claim or experiment admission. Verified complete-
work improvement remains NONE; no novelty claim for finite differences.

## Construction and exact elementary checks

Let H=a² with a>=1. Prepare2a independent uniformly labelled group points A_i,
B_j, indices0<=i,j<a. Their labels are explicit affine combinations of G,Q.
Set

    M=4a+1, D=a+M*a², C=4D+1,
    c_i=C+i+M*i², Z_ij=A_i+[c_i]B_j,
    4*max_i(c_i)<q.

Root checked that a nonempty signed sum of at most four DISTINCT c_i cannot be zero
modulo q. Its integer magnitude is below q. The constant C dominates the
remaining terms when positive and negative term counts differ. With equal
counts there are at most two terms on either side. Since M exceeds the maximum
possible difference of those index sums, equality forces both sums of indices
and sums of squares to agree. Their unordered pairs then agree, contradicting
distinct indices. The one-term-per-side case is immediate.

For each j initialize [C]B_j, [1+M]B_j and [2M]B_j, paying their scalar work.
The forward-difference recurrence is

    D_i=[1+M*(2i+1)]B_j,
    [c_(i+1)]B_j=[c_i]B_j+D_i,
    D_(i+1)=D_i+[2M]B_j.

Combining with A_i takes a third group addition per emitted helper (boundary
updates can be omitted). Both scalar label coordinates follow the same paid
recurrences. Root verified these identities. Complete group operations are
required; affine denominators cannot silently discard exceptional additions.
Normalization, initialization, labels, storage and any checks are extra costs.

The proposer then applies a paid uniform permutation to all H helpers and uses
the fixed sparse/thickened graph's paired-key search and ordinary descriptors.
This is a proposed new source distribution, not authorization to alter or
rerun the consumed H034 diagnostic.

## Collision-law status

The proposer gives a potentially useful projection argument: a signed form on
four distinct grid rows identifies those rows/signs via A_i coefficients; the
short signed-sum property identifies their column assignments via B_j
coefficients. Nongeneric row coincidences occur with expected fraction O(1/a)
under the paid uniform permutation. The proposer reports a dependency-bound
error O(1/a), translating at H=q^(3/10) to stopped-key error O(q^(7/20)).

These graph-wide alias, useful-label and stopped-law claims are retained as
PROPOSER ANALYSIS, not a newly independently verified Poisson theorem or frozen
solver specification. In particular, normalization, repeated functional
multiplicities, seed checks/conditioning, finite prefixes and exception handling
would need a full proof before acceptance. The reported bound is already weaker
than the existing q^(3/10) remainder. A weak upper bound does not prove an actual
penalty of that order. No such probability assertion is needed for the cost
rejection below, even if one grants the hoped-for original collision law.

## Decisive full-work screen

H037-newton-source-hypothesis.md already provides a competent IID comparator:
paid fixed-position tables of O(H/log²(q)) total size, constant-many scalar
chunks per H=Theta(q^(3/10)) source, complete projective additions and paid
normalization. H IID labelled points therefore cost O(H) group-field work under
that declared indexed-access model. Its preprocessing is not free advice.

The grid also materializes H helpers, labels and the permutation, costing at
least Omega(H) writes/work and H-point storage; its recurrence uses O(H) group
additions plus initialization. Thus replacing H independent sources by2sqrt(H)
does NOT improve the generation exponent against that allowed comparator.
It may reduce ideal randomness consumption or change finite constants. No
matched complete invoice or calibrated gain establishes either as a material
full-size solver saving. The identical outer search leaves any source-only
O(q^(3/10)*polylog(q)) saving subleading to sqrt(q); its relative scale is
q^(-1/5)*polylog(q). This is not a runtime prediction or a finite percentage.

Disposition: park before implementation or an additional probability-review
wave. Even a sharper dependency bound would not by itself fix the complete-work
premise. Reopen only with a specified resource regime or leading-cost mechanism
that changes this comparison. Do not count fewer random seeds, helper additions
or this checkpoint as an algorithmic breakthrough. Other H039 independent
proposers remain live and have not been given this initial proposal.
