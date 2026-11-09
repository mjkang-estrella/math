# Round 2 proof notes

Source fidelity follows the root ruling and the independently reviewed ordinary proof. Citation numbering is the published Lemmas 2.9 and 2.10 and Conjecture 6.1. The binary depth-two construction is attributed to source Figure 5. The open even t >= 4 depth-two construction uses source ingredients; it is not proved here.

For a positive-depth vertex (h,i), the parent is (h-1,i/t). The bound on i/t follows by dividing i < t^h by positive t. The child maps are j -> (h+1,t*i+j), with inverse remainder modulo t. Quotient and remainder give the two inverse identities. The incoming edge map sends the vertex to the unordered pair of itself and its parent. Equality of pairs either identifies the lower endpoints or swaps both endpoints; the swapped alternative contradicts the strict depth increase. Every edge has a child orientation, proving surjectivity.

Every vertex is reachable from the root by induction on its depth. Incoming edges are in bijection with all vertices except the unique depth-zero root, so |E| + 1 = |V|. Mathlib's finite connected/cardinality criterion yields a tree, including acyclicity. Together with the child count and parent uniqueness this supplies the inherited FullTree structure with the exact prescribed root, depth and child relation.

Neighbors partition into children and parents. These sets are disjoint by depth; their cardinalities are respectively t or zero according to depth < n, and zero or one according to depth = 0. Thus degree is their sum. Under t >= 2 and n >= 1, degree one is equivalent to depth n. The latter subtype is explicitly equivalent to Fin (t^n).

Reindex the finite incidence sum by incoming endpoints. Membership of a vertex in an unordered pair is equality with either endpoint. The two incidence alternatives cannot overlap. Splitting the sum and reindexing the child part gives weight_children and weight_row. All +1 shifts are inside the summands.

At depth n the weight is exactly the incoming edge label. These edge labels are injective and bounded by m = |E|. Choose the edge labelled m. Its parent is below depth n and has t children. Its edges to child slots zero and one are distinct; at least one differs from the chosen edge. The two incident terms show that the parent weight exceeds m. The inherited leaf_color_bound then yields t^n + 1 colours. No local properness assumption is needed by this argument.

For depth one, the incoming vertices are explicitly equivalent to Fin t. Composing with the incoming-edge equivalence gives the inherited formula i+1 on each edge. The root weight exceeds t by using the maximum-labelled and first-labelled edges. Each leaf weight is at most t, proving properness. The lower bound and the total vertex count t+1 give exact colour count.

For binary depth two, binaryMap applies the Figure 5 formula minus one on the six actual nonroot vertices. Kernel `decide` proves its bijectivity and range. Its composition with the incoming equivalence is the literal graph labelling. The incidence identity reduces its weights to a finite endpoint sum; kernel `decide` proves properness and five colours. This proof does not assert any other construction instance.

Next round: prove bijection/range identities for the depth-two even t >= 4 formula, then the parity shells and leaf-block permutation for n >= 3, separating the binary patch. Use weight_row to turn row sums into literal graph weights. For ModelBridge, choose child orderings and construct compatible row equivalences by depth induction, then prove adjacency preservation. No new endpoint should become unconditional until both remaining Props are discharged.

The separate Antimagic2Finite module provides a generic finite-certificate bridge. Positive, bounded, bijective values of the exact formula on Nonroot vertices induce a literal edge equivalence. Its weights equal formulaWeight, which is a sum over actual incidence endpoints. The properness and colour-count fields therefore imply the literal construction. Antimagic2Regression checks this certificate at all six round-1 parameter pairs, independently of the row enumeration. These finite statements do not discharge any infinite family.
