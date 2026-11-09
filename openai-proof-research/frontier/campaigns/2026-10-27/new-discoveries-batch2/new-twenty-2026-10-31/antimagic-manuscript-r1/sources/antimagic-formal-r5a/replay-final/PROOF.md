# Round 5A proof notes — partial, not acceptance

The reviewed higher-depth formula was re-derived before Lean work and checked by
scripts/grid5a.py in all nine requested cases (t = 2, 4, 6; n = 3, 4, 5).
The script compares the reviewed shell/tuple assignment with its closed formula,
then independently checks incidence weights, bijectivity, properness and the
colour count. Missing the binary patch and duplicating a label are negative
controls. Numerical checks are diagnostics only.

Write N = internalEdges t n, q = t^(n-1), Z = (N-t)/2+1 and R = Z-1.
For the symbolic nonbinary construction write t = 2s, s >= 2. The following
arguments are now Lean proofs, without assumptions of any construction Prop.

1. The exact offset recurrence is O(h) = t^(h+1) + O(h+1) when h+1 < n;
O(h) = 0 when n <= h+1; N = t + O(1). Offsets are antitone.
Even t makes every offset at h >= 1 even, hence O(1) = N-t = 2R.
The intervals [O(h), O(h)+t^h) for 2 <= h < n are pairwise disjoint
and cover [0,O(1)). Coverage is induction on n: the new last row occupies
[0,t^n), and every older interval is shifted by t^n. This is a symbolic
proof for arbitrary depth, not a finite certificate.

2. The frozen shell formula at an internal row is shellEntry Z (O(h)+i),
since the patch is the identity for t >= 4. The coordinate bound places all
these labels in [1,N-t+1] with Z omitted. Row one is exactly Z together with
[N-t+2,N]. Shell injectivity and coordinate injectivity prove uniqueness
across rows; the explicit shell inverse plus interval coverage prove existence.
internalMap_bijective transfers this permutation to InternalVertex, an actual
subtype of Nonroot t n, with all original graph definitions unchanged.

3. The final internal row has O(n-1)=0 and q=2k with k<Z. For its zero-based
coordinate r, the tuple parameter derived from the frozen parent label is
2k-r/2 when r is even, and 1+r/2 when r is odd. The two branches occupy
[k+1,2k] and [1,k]. Quotient/remainder uniqueness proves injectivity; equal
finite cardinalities prove parentMap_bijective. The cancellation identity is
shellEntry Z r + a = Z + sigma k a.

4. The inherited leafEntry permutation therefore transfers to all q*t leaf
row positions: divide a position by t for its parent, take its remainder for
the slot, apply parentParameter and leafEntry. Equality of leaf labels forces
equal tuple parameters and slots, then equal parents and positions.
leafRowMap_bijective gives full coverage of the high interval [N+1,N+t^n].
The exact formula agreement is leaf_formula.

5. formula_range_rows proves positivity and the global upper bound N+t^n.
The two actual vertex permutations combine into formulaMap_bijective on
Nonroot. higherLabeling composes its equivalence with incomingEquiv and the
cardinality cast, so it is a literal Labeling (tree t n), with no supplied
bijection assumption. higherLabeling_label retains the explicit +1 on Fin
labels and agrees exactly with the frozen label formula.

6. For a middle-row parent (h,i), the child shell coordinates form the even
segment O(h+1)+t*i+j. Pairing consecutive coordinates proves children sum tZ.
For a last-row parent, the inherited tuple sum adds back sigma, and the
cancellation in step 3 proves incoming label plus leaf labels equals
s*(2N+tq+1)+Z. Both statements are symbolic natural-number identities.

Antimagic5AWeights transports these identities through literal_weight_row to
the actual incidence weights of higherLabeling, and proves the bottom weight
identity. Remaining: the global weight bands, root weight/root separation,
properness and colour-count argument must be completed. In particular label
range bounds are not weight range bounds. NonbinaryWeightCompletion is the
exact residual Prop asserting IsLocal and the required colourCount for the
already-built literal labeling. nonbinaryHigherConstruction_of_weights proves
that this residual Prop suffices for Round3.NonbinaryHigherConstruction.
Neither Prop is unconditionally proved. The binary higher-depth construction
has not been attempted, preserving target order. ModelBridge is untouched.

Source attribution remains the reviewed new shell/tuple construction for
n >= 3; the n = 2 binary labeling is published Figure 5, the nonbinary depth-two
case uses published Lemmas 2.2 and 2.9, and the full target is Conjecture 6.1.
The sibling lane alone owns ModelBridge. No novelty or acceptance claim is made.
