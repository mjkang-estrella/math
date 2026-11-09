# Proof: orientable total domination interpolation

Draft; AI-assisted. Finite simple graphs, incoming total domination.

An orientation D of a finite simple undirected graph G directs each edge in exactly one of its two directions. Write u → v for an arc of D. The orientation is <i>valid</i> if every vertex has positive indegree. A set S ⊆ V(G) totally dominates D if every vertex v, including every vertex of S, has an in-neighbour in S: there is u ∈ S with u → v. Let γ<sub>t</sub>(D) be the minimum size of such a set. For valid D the whole vertex set is a total dominating set, so this minimum exists.

For a graph admitting a valid orientation, define its spectrum Σ(G) = {γ<sub>t</sub>(D) : D is a valid orientation of G}, and define dom<sub>t</sub>(G) = min Σ(G) and DOM<sub>t</sub>(G) = max Σ(G). There are finitely many orientations, so both extrema are attained. The admissible nonempty graphs are precisely those whose every component contains a cycle. Indeed a tree component has fewer edges than vertices and cannot have positive indegree everywhere. Conversely, orient a cycle cyclically in each component, attach the remaining vertices along a spanning tree rooted on that cycle, and direct the tree edges away from the cycle; direct all remaining edges arbitrarily. Each vertex retains an incoming arc. The empty graph is also admissible under the vacuous convention, with spectrum {0}.


## 2. A transfer lemma and the complete proof

Fix valid orientations D and E of the same finite simple graph. Define Δ(D,E) = {(a,b) : a → b in D and b → a in E}, and put d(D,E) = |Δ(D,E)|. Each disagreeing edge contributes exactly once. A target-directed flip reverses an arc in Δ(D,E), thereby making that edge agree with E.

<b>Lemma 1 (forced heads).</b> Suppose that every arc a → b in Δ(D,E) is the unique incoming arc at b in D. Then every total dominating set of D is a total dominating set of E.

<i>Proof.</i> Let S totally dominate D. First we show that every head of an arc in Δ(D,E) belongs to S. Let a → v be such an arc. Choose w → v in E, using validity. If w → v also occurred in D, uniqueness at v would force w = a, contradicting reversal of a → v. Since the underlying edges are the same, v → w occurs in D and is reversed in E. By the hypothesis it is the unique incoming arc at w in D. Since S dominates w in D, its only possible witness is v, so v ∈ S.

Now let v be any vertex, and choose a ∈ S with a → v in D. If this arc survives in E, it dominates v there. Otherwise a → v lies in Δ(D,E). Choose w → v in E. As above, w → v cannot occur in D, and hence v → w lies in Δ(D,E). The first part of the proof, applied to its head w, gives w ∈ S. Thus w → v witnesses domination of v in E. This holds for every v, proving the lemma. □

<b>Lemma 2 (safe flip and repair).</b> If S totally dominates D but does not totally dominate E, there are a → b in Δ(D,E) and another incoming arc w → b in D with w ≠ a. Reversing a → b gives a valid orientation F of the same graph such that S ∪ {w} totally dominates F and d(F,E) = d(D,E) − 1.

<i>Proof.</i> If no such arcs existed, every disagreeing arc would be the unique incoming arc at its head. Lemma 1 would imply that S dominates E, a contradiction. Choose the stated a,b,w and perform the flip. Only b loses an incoming arc, and it retains w → b; all other vertices retain their old incoming arcs. Thus F is valid, and it is still an orientation of G. To check total domination by S ∪ {w}, use w at b and each old S-witness at any other vertex. This includes the new vertex w itself: its old witness is retained, since w ≠ b by looplessness. Finally, the changed edge now agrees with E, and no other edge changes. Exactly one element is removed from the disagreement set. □

<i>Proof of the theorem.</i> We prove the stronger statement that, for any valid D,E and integer c with γ<sub>t</sub>(D) ≤ c ≤ γ<sub>t</sub>(E), a valid orientation of the same graph attains c. Use strong induction on d(D,E). If γ<sub>t</sub>(D) = c, take D. Otherwise let S be a minimum total dominating set of D. Then |S| = γ<sub>t</sub>(D) &lt; c ≤ γ<sub>t</sub>(E), so S cannot dominate E. Lemma 2 supplies a valid F with

γ<sub>t</sub>(F) ≤ |S ∪ {w}| ≤ γ<sub>t</sub>(D) + 1 ≤ c,

and smaller disagreement with E. Apply the inductive assertion to F,E and c. The induction is well founded on nonnegative integers; when disagreement is empty the orientations coincide, so the strict case cannot arise. Taking D and E attaining the two extrema proves the claimed interval. □

There is no connectedness assumption anywhere in this argument. In particular all vertices in all components are quantified in each total-domination assertion, and the induction changes only an existing edge. It handles every admissible disconnected graph as stated. Alternatively, total domination numbers add over components, and sums of finite integer intervals are integer intervals. The empty case has the value already specified.
