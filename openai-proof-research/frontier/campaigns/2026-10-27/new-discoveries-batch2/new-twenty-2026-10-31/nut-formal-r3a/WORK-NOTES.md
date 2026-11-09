# Proof mechanism and continuation notes

The new real cofactor theorem avoids adjugate rank classification. If the
principal submatrix deleting i were singular, choose its nonzero nullvector v
and insert zero at i to get w. Every coordinate of Aw other than i vanishes.
Symmetry gives uᵀAw = wᵀAu = 0. Since u_i is nonzero, (Aw)_i also vanishes.
Thus w belongs to the one-dimensional full kernel. It is a scalar multiple of
u, and w_i = 0 forces that scalar to vanish, contradicting v ≠ 0. This proof
works for every n+1, including n = 0; the empty minor cannot be singular.
Determinant zero follows from the nonzero nullvector. The standard principal
cofactor identity then proves every diagonal adjugate entry is nonzero. Integer
specialization uses injectivity of integer casting into the reals and ring-hom
compatibility of determinant and adjugate.

The explicit character lift sends v_i to χ(a) v_i at (i,a). Reindex the adjacency
sum by b ↦ b+a and use translation invariance and character multiplicativity.
Evaluation at a = 0 recovers v, so the lift is injective. Transport this kernel
back through L.symm to the original graph. Original real nullity one bounds the
quotient nullity above by one; the restricted full original nullvector bounds
it below by one. `nut_circulant_quotient` composes these constructions without
adding coordinate, linear lift, or nullity hypotheses to the graph statement.

For connectivity, truncate the full kernel vector to a hypothetical nonempty
proper cut with no crossing edge. The truncation is still a kernel vector. Its
zero coordinate outside and nonzero coordinate inside contradict proportionality
to the original full vector. Reachable vertices from a fixed root form such a
cut if the graph is disconnected. No regularity hypothesis is needed.

For cubic cancellation, erase two distinct specified neighbors from the
three-element neighbor set. The remaining set is a singleton. If the first
two kernel values cancelled, the third would be zero. This proves
`cubic_kernel_no_cancel`. With the coordinate character formula, two different
shifts contributing opposite character signs to the same quotient vertex
would cancel. Thus `neighbor_character_coherent` proves all those signs equal.

A3 continuation should use this coherence to identify absolute entries with
raw neighbor counts, then use the actual connected graph for support cuts.
For internal edges, inversion preserves the shift set. Shift zero is forbidden
by looplessness. Its sole possible nonzero fixed point under inversion is m/2
when m is even. The remaining shifts pair into loops. Cubicity and quotient
connectivity exclude the degree-three isolated support and triple-edge cases.
These are mathematical continuation notes, NOT Lean proofs of A3. No abstract
GraphGrammarBridge hypothesis was introduced as a substitute.
