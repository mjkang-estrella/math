# Statement correspondence

This is a partial formalization, not a refutation certificate ready for acceptance.

Source: Ledezma, Pastine, Torres and Valencia-Pabon, arXiv:2112.01884v2, 11 February 2022. The source text and PDF are copied under inputs with SHA-256 receipts. The source's §1 defines the diameter only for connected graphs as the maximum shortest-path length. Its §1 defines [n] as {1,...,n}, 2-stable subsets as containing no consecutive elements, explicitly including the cyclic pair {1,n}. Its §2 also describes stability as 2 ≤ |i-j| ≤ n-2 for distinct elements. Conjecture 2 is on printed page 21.

| Source | Lean in src/Definitions.lean | Correspondence |
|---|---|---|
| [n] | Fin n | Position i in Lean denotes source position i+1. |
| k-subsets | Finset (Fin n), card = k | Finsets have no repeated elements. |
| Cyclically 2-stable | Stable n s | For each ordered pair in s, the second value is not (first+1) mod n. This includes the wrap from n-1 to 0. |
| SG(n,k) vertices | Vertex n k | Subtype with both cardinality and stability proofs. |
| Empty intersection adjacency | SG n k | Distinct vertices with Disjoint finsets; symmetry and looplessness proved. For k > 0, disjointness already forces distinctness. |
| D(G) | diam G = G.diam | Mathlib takes ediam.toNat. It assigns 0 to disconnected graphs; therefore connectivity is explicitly required in both remaining bridge propositions. For a finite connected graph, connected_iff_ediam_ne_top and dist_le_diam give the genuine maximum. |
| 2 ≤ r ≤ k-2 | 2 ≤ r and r+2 ≤ k | Equivalent over naturals under these bounds. |
| Integer difference in {0,1} | Difference after casting natural diameters to integers, membership in Set ℤ | No truncated natural subtraction. |
| k=12,r=3 | 27,28 and k=12 | The conditional endpoint specializes exactly this instance, independently of Theorem 6. |

The graph definitions extend to all natural n,k. At n=1 the modular successor equals itself and Stable excludes the singleton; at n=0 the vertex index type is empty. These degenerate extensions have no bearing on the conjecture's hypotheses, which force k ≥ 4 and n ≥ 10. No source assertion in this parameter range changes under the extension.

src/Checkers.lean defines decode n m by filtering Fin n with Nat.testBit. Bit zero denotes source element 1. validMask checks m < 2^n, cardinality k and cyclic nonconsecutiveness. validMask_sound proves those literal finite-set properties from a successful Bool check. It does not prove enumeration completeness or injectivity of decode.

labelCheck_sound proves the local edge-label inequality from successful finite Bool checks and membership of both endpoints in the checked list. label_walk_bound and labels_lower_distance prove the corresponding bound for all walks and then graph distance, the latter explicitly requiring reachability. parentCheck_sound proves the local parent conditions. parent_walk constructs a walk to the root by induction on depth. parent_connected proves connectivity from those conditions on every vertex.

Data27 certifies the validity and number of the listed masks and the validity of the explicit witness masks only. It does not certify a bijection, a labelling, a parent tree, rotations, connectivity or a diameter. Python computations do not supply Lean hypotheses.

The only conjecture-level Lean endpoint is mathdb_352827_conditional, which takes exactly LowerCertificateBridge and UpperCertificateBridge as hypotheses. There is deliberately no theorem named mathdb_352827 in this partial handback.


Round 2 addendum: Encoding proves the bounded mask bijection by both inverse laws. Rotations proves literal graph automorphisms and their action on individual bits. Enumeration proves completeness of a reference powerset enumeration, not equality with the stored tables. MaskSemantics proves a graph isomorphism given valid, injective and complete indexed masks. IndexedCertificates proves parent and label checker soundness. Packed tables allow small kernel-decided certificate modules. LowerIndexed concerns the indexed 819-vertex graph; it does not establish a lower bound in the literal graph without the missing isomorphism premises. No unconditional literal endpoint is claimed.
