Primary source: Kazemnejad, Pahlavsay, Palezzato and Torielli, “Connected and outer-connected domination number of middle graphs”, arXiv:2206.15439v1. Read from the immutable cached source in expanded-corpus-r139/sources/txt-2206.15439.txt. No network access was used in this lane.

The source introduction defines domination by “NG[v] ∩ S ≠ ∅”. IsDominating says every vertex is in S or is adjacent to a member of S. This is exactly the same closed-neighborhood condition.

Definition 1.2 says “A dominating set S of a graph G is called an outer-connected dominating set if the graph G − S is connected.” It defines the number as the minimum cardinality. IsOuterConnected uses the induced subgraph on the set complement and Preconnected. IsOuterConnected' uses Connected, adding nonemptiness. IsOCD and IsOCD' conjoin these with domination, definitionally. No empty-complement convention is specified in the source; both are treated separately here. One-vertex complements satisfy both conventions.

The four IsLeast endpoints state actual attained minima, independent of the sInf default at an empty feasible set. ocd and ocd' are sInf of attainable cardinalities; on G8 and its middle graph their proved values are 4. Convention B has no feasible set at a nonempty edgeless graph; its sInf is a totalization, not a claim that a minimum exists there. The uncredited edgeless control explicitly records that distinction.

Definition 1.3 gives vertex set “V(G) ∪ E(G)” and two adjacency cases: distinct incident edges, or an incident original vertex and edge. The formal type is the tagged disjoint sum W ⊕ G.edgeSet. The four match branches in middle implement vertex–vertex False, vertex–edge incidence in both directions, and distinct edge–edge sharing of an endpoint. There is no relabeling to Fin 19 or missing graph-isomorphism bridge.

Conjecture 7.1 reads “Let G be a graph of order n ≥ 2. Then” followed by γ̃c(G) < γ̃c(M(G)). MathDB 355217 states the same inequality and n ≥ 2 hypothesis, with explanatory family prose. The root ruling narrows credit to the connected form. mathdb_355217_connected and mathdb_355217_connected' negate the universal quantifier over every finite type and every connected simple graph of order at least 2, separately under the two conventions. Each proof explicitly specializes to Fin 8, G8, G8_connected, and rewrites both values to 4.

G8's explicit 11-edge list is 01, 06, 16, 23, 27, 37, 46, 47, 56, 57, 67. Its type has exactly 8 vertices. G8_connected proves source-domain connectivity using a parent map. g8_value and g8_value' assert the source minimum is exactly 4; middle_g8_value and middle_g8_value' assert the same for its literal middle graph.

The edgeless_two_literal_failure endpoint is a recorded, uncredited domain control. It does not supply the connected refutation. The infinite family and smallest-counterexample search are outside this formalization's scope. This lane does not self-accept.
