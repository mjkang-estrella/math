# NEWr334 / 382297 — ordinary proof, awaiting root qualification and review

Zero accepted credit. No execution, formalization, independent review, manuscript or dispatch has occurred. This is a proposed full ordinary solution, not an accepted discovery. Bounded novelty only: the primary journal and later thesis still pose this precise problem, but there is no claim of universal literature absence. A later acyclic counterexample journal route returned 403; its independently public arXiv v2 proof was read, not substituted for clearance of the inaccessible journal. Root should resolve that final-version comparison and independently review novelty/significance before authorizing anything.

## Exact semantic endpoint and sources

For every n and every u,v in the transitive tournament T_n, whose arcs are i→j for i<j, uniformly retain a subset of the horizontal arcs in both copies and the n bidirectional vertical edges. Prove P(u^0→v^0) ≥ P(u^0→v^1). Reachability includes a length-zero path. A vertical edge is ONE random bit retaining/removing both directions together. This is E7 in arXiv:2406.01790v1, Definition 1.4, Model 4.5, Conjecture 6.4, and D7 in the published European Journal of Combinatorics 128 (2025), 104188, same numbered locations. The published p.14 explicitly distinguishes D8, in which the vertical arcs are retained separately; D8 is not needed here. Later Hollom thesis Conjecture 6.6.4 repeats this endpoint after noting the acyclic counterexample.

## Full ordinary proof

Fix u. Vertices indexed below u cannot be reached: horizontal arcs strictly increase index and vertical steps preserve it. For a prefix ending at k≥u, let R_k^0,R_k^1 be the sets of indices in [u,k] whose copies are reachable from u^0 using this prefix, and put A_k=|R_k^0|, B_k=|R_k^1|. The prefix restriction does not change reachability of any vertex in it, since a directed path cannot return from a larger index. At k=u, the distribution of (A_k,B_k) is (1,0) with probability 1/2 and (1,1) with probability 1/2.

Condition on the entire revealed prefix, with counts (a,b). The unrevealed arcs from reachable bottom vertices into (k+1)^0 and from reachable top vertices into (k+1)^1 are two disjoint sets of respectively a and b independent fair bits. They are independent of the prefix. Let X,Y indicate that at least one such bottom/top arc is present. Thus P(X=0)=2^{-a}, P(Y=0)=2^{-b}, and X,Y are independent. Let Z be the new vertical-edge bit, independent and fair. Exactly the new reachable indicators are

 U = X ∨ (Z ∧ Y),    V = Y ∨ (Z ∧ X).

To justify “exactly,” a path first entering the new index must do so by a horizontal arc from a previously reachable vertex; after entering, its only possible additional vertex at this index is its vertical partner. There is no route back into the old prefix. Consequently the counts have Markov transition

 (a,b) ↦ (a+U,b+V).

Denote this kernel by K and reflection by ρ(a,b)=(b,a). It obeys K(ρs,ρt)=K(s,t), by swapping X,Y and preserving Z. Also its count difference changes by at most one, since U,V are bits. Therefore no one-step transition from a>b ends at a<b, nor conversely.

Here is the entire positivity argument, including what ordinary symmetry alone does not prove. For any finitely supported probability mass μ, suppose Δμ(a,b)=μ(a,b)−μ(b,a)≥0 whenever a>b. For t above the diagonal,

 Δ(μK)(t) = Σ_s μ(s)[K(s,t)−K(s,ρt)]
             = Σ_{s above} Δμ(s)[K(s,t)−K(s,ρt)]
             = Σ_{s above} Δμ(s)K(s,t) ≥ 0.

The second equality pairs each state with its reflection; diagonal states cancel. The third uses the no-crossing property: s above and ρt below imply K(s,ρt)=0. All sums are finite. The initial distribution satisfies this condition, so induction gives it at every prefix. Equivalently one can reflect the suffix of a count-state history after its first diagonal hit; those paths cancel in reflection pairs and paths which have never hit the diagonal stay above it. Pathwise A≥B is NOT claimed.

For the next vertex, conditionally on (a,b),

 g(a,b) := E(U−V | a,b) = (1/2)(2^{-b}−2^{-a}).

Indeed U−V=(1−Z)(X−Y). The function g is antisymmetric, zero on the diagonal and nonnegative above it. For any prefix distribution just proved to satisfy Δμ≥0,

 E(U−V) = Σ_{a>b} Δμ(a,b)g(a,b) ≥ 0.

Taking k=v−1 proves the desired connection probability inequality for u<v. If v<u, both probabilities are zero by monotonicity of indices. If v=u, the same-layer probability is one and the other is 1/2. This covers all endpoints; n=0 has no endpoint pairs. The theorem follows.

## Failed shortcuts and adversarial checks

A single scalar E(A−B)≥0 would not suffice, since g is nonlinear in the counts. Pathwise domination also fails as a proof method: an above-diagonal state can increment only its top count. Full reflection dominance, not either shortcut, is preserved. A general DAG does not have the same sufficient statistic: the incoming reachable-parent counts at different later vertices are not the total counts A,B. Thus the acyclic counterexample of Przybyłowski does not contradict this proof and cannot refute the tournament statement. The complete-undirected-graph proof of van Hintum–Lammers uses a uniformly chosen source, undirected components and full vertex-permutation symmetry. Those are not hypotheses here; its conditional-component proof cannot be cited as a direct implication. The new issue addressed here is the exact prefix-count sufficiency and the reflection-preserving kernel for fixed ordered endpoints. Shortness alone is not a novelty claim or exclusion.

## Bounded prior-art and remaining qualification gaps

Read: Hollom arXiv v1 definitions/Models 4.4–4.5/Section 6; journal definitions, Section 6 and proof-context; later thesis relevant chapter conclusion; Leander 2009 Section 5 including Theorems 10–12 and proofs; Przybyłowski arXiv v1/v2 definitions and v2 Sections 3–4 proof body; van Hintum–Lammers final arXiv v4 theorem and proof. Leander proves cutset/antichain special post configurations in a conditioned edge-color model, not all E7 tournament outcomes. Przybyłowski's graph has missing adjacencies and uses gadgets; no monotonicity of the difference of connection probabilities under edge addition is available. Its acyclic negative result does not subsume this endpoint.

Current registry routing: OpenAI/math head 4eaee87548250b2682affda7d05d947c05554bae, LeanPool head 01db1d7049cf9668bda1e9e106875ee1278b43e6, Omega head 8bcd9134655d4c88a93778604e49583d6d9cf736. OpenAI contents and LeanPool projects/import index were fetched and searched; no bunkbed match. Omega root and README only, not a complete tree. These are routing checks, not proof or exhaustive novelty clearance. No exact ID match in the searched completed-result allowlist. Search-engine queries on transitive tournaments/bunkbed/reflection/Markov did not expose a matching proof; managed search telemetry is unavailable. Citing literature and figures are not universally cleared. The ScienceDirect 403 is retained as a gap, with no retry.

## DORMANT semantic Pi plan — no dispatch

Only if root approves source qualification, novelty/significance and the ordinary proof: Pi spark/GLM-5.3-Flash-EXL3, high thinking, should formalize the actual fair finite sample space. No generic solver or diagnostic task is proposed.

Use vertices Fin n × Bool. Define an edge-token type as the disjoint sum of (i,j,layer,h:i<j) horizontal tokens and Fin n vertical tokens. An outcome is a Boolean assignment to every token; a vertical token enables BOTH arcs. Define the arc relation literally and Reach by reflexive transitive closure. Define the exact finite-count endpoint

 |{ω : Reach ω (u,false) (v,true)}| ≤ |{ω : Reach ω (u,false) (v,false)}|

for all n,u,v. This cancels the common denominator 2^(n(n−1)+n), so no real probability infrastructure is needed for the final statement. Do not replace Reach with an unproved count-process proxy.

Prove prefix restriction of Reach using index monotonicity; exact recursive new-layer closure; the disjoint fair-bit fiber counts for incoming arcs from R^0,R^1; and that forgetting unreached-parent arcs and irrelevant future bits contributes common multiplicative factors. Establish the count-distribution transition (over rationals if useful), reflection equivariance, no crossing, the displayed finite-sum induction and new-vertex marginal formula. Finally transfer to literal Reach event cardinalities using the fiber-counting equalities, including arbitrary source u, n=0/v<u/v=u cases. These bridges are all proved above ordinarily and none may remain as an assumption. Suggested separate proof modules are definitions/prefix reachability, finite-bit fiber counts, reflection kernel, endpoint transfer; no dependency changes without root authorization. Pin Lean/mathlib only in the future assigned execution lane. Audit exact endpoint and transitive axioms; only propext, Classical.choice, Quot.sound. Extract and replay independently after implementation. Stop on any failed semantic bridge rather than adding axioms or weakening the statement.

Historical reconciliation addendum: history-reconciliation.json distinguishes completed r280 self-avoiding-walk counts, r294 two-color percolation and r64 undirected Kasteleyn scope from this fixed ordered transitive-tournament E7 endpoint. No theorem from those prior lanes is proposed again.
