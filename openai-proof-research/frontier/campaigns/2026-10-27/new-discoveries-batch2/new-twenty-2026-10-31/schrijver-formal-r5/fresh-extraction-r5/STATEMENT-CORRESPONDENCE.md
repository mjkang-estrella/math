# Statement correspondence

The endpoint is the unconditional theorem Schrijver.mathdb_352827 : ¬ SchrijverUnitGap in src/EndpointRound5.lean. All original definitions remain byte-identical.

Source: Ledezma, Pastine, Torres and Valencia-Pabon, arXiv:2112.01884v2, 11 February 2022. The source text and PDF are copied under inputs with SHA-256 receipts. The source's §1 defines the diameter only for connected graphs as the maximum shortest-path length. Its §1 defines [n] as {1,...,n}, 2-stable subsets as containing no consecutive elements, explicitly including the cyclic pair {1,n}. Its §2 also describes stability as 2 ≤ |i-j| ≤ n-2 for distinct elements. Conjecture 2 is on printed page 21.

| Source | Lean in src/Definitions.lean | Correspondence |
|---|---|---|
| [n] | Fin n | Position i in Lean denotes source position i+1. |
| k-subsets | Finset (Fin n), card = k | Finsets have no repeated elements. |
| Cyclically 2-stable | Stable n s | For each ordered pair in s, the second value is not (first+1) mod n. This includes the wrap from n-1 to 0. |
| SG(n,k) vertices | Vertex n k | Subtype with both cardinality and stability proofs. |
| Empty intersection adjacency | SG n k | Distinct vertices with Disjoint finsets; symmetry and looplessness proved. For k > 0, disjointness already forces distinctness. |
| D(G) | diam G = G.diam | Mathlib takes ediam.toNat. It assigns 0 to disconnected graphs; therefore connectivity is explicitly required in both proved bridge propositions. For a finite connected graph, connected_iff_ediam_ne_top and dist_le_diam give the genuine maximum. |
| 2 ≤ r ≤ k-2 | 2 ≤ r and r+2 ≤ k | Equivalent over naturals under these bounds. |
| Integer difference in {0,1} | Difference after casting natural diameters to integers, membership in Set ℤ | No truncated natural subtraction. |
| k=12,r=3 | 27,28 and k=12 | The endpoint specializes exactly this instance, independently of Theorem 6. |


The frozen SchrijverUnitGap universally quantifies natural k,r with 2 ≤ r and r+2 ≤ k. It takes the difference after casting both natural diameters to integers. The endpoint negates this exact Prop; its witness k=12,r=3 satisfies both hypotheses. Finite connectedness is proved through the spanning parent trees and literal graph isomorphisms, so Mathlib's default value for disconnected graphs does not affect either diameter bound.

Encoding uses Nat.testBit and decode n m : Finset (Fin n); encode/decode inverse laws are frozen. referenceMasks is defined through the literal powersetCard enumeration and proved equivalent to validMask. StoredEnumerationComplete means exact membership equivalence, not equality of numerical counts. Enumeration27 and Enumeration28 retain their frozen definitions in BridgeTransport. Round 5 proves them as enumeration27_proved and enumeration28_proved.

PathGenerator:pathMasks_cover proves completeness for arbitrary bounded finite sets with no consecutive natural positions. PathCoverage:validMask_path_cover transfers literal cyclic stability to that path condition; cyclicMasks_complete proves equivalence with referenceMasks using the full validity filter. PathCoverage:validMask_end_cover proves the weaker cyclic endpoint filter retains every valid mask. The two Enumeration*Proof modules kernel-decide list equality with the stored tables, use frozen validity for table-to-reference membership, and use the generator for reference-to-table membership. The graph, adjacency, rotation, connectivity and diameter meanings are never replaced by an unbridged finite surrogate.

The source definitions extend to natural n,k in Lean. At n=0 the index type is empty; at n=1 modular self-successorship excludes the singleton. These cases do not arise under the conjecture hypotheses, which force k≥4 and n≥10. The proof does not invoke source Theorem 6. The journal-scope limitation from the root ruling is retained.
