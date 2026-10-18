# Balanced reserve construction: author-side local progress

Status: a proved local interface toward the unchanged full Eulerian decomposition target, not that target's proof, not an independent gate, and not a separate nominee. Standard max-flow integrality and the source181 sampling proof supply the main operations. No literature novelty is claimed for these local lemmas.

All digraphs below are finite, loopless, and have at most one arc for each ordered pair; antiparallel arcs are allowed. Two-sided cut expansion h means each of e(S,V\S), e(V\S,S) is at least h min(|S|,|V\S|). Imbalance is out-degree minus in-degree. Logarithms in probabilistic estimates may be natural; this changes no exponent comparison.

## 1. Integral correction with bounded vertex load

**Lemma.** Let P be a simple n-vertex digraph with two-sided cut expansion h>0. Let b:V(P)->Z have sum zero and |b(v)|<=k, where 0<=k<=h. Put M=ceil(kn/h). There is an arc subset F of P with imbalance exactly b and

 d_F^+(v)<=M,   d_F^-(v)<=M+k.

Consequently each directed cut of P loses at most (M+k) times its smaller-side order when F is removed. If b is the imbalance of P, then P−F is balanced and has two-sided cut expansion at least h−M−k.

**Proof.** For k=0 use F empty. Otherwise put epsilon=k/h<=1. For every S, zero total demand and the pointwise bound give b(S)<=k min(|S|,n−|S|)<=epsilon e_P(S,V\S). The standard source/sink max-flow cut criterion therefore gives a real nonnegative flow f on the original arcs, each of capacity epsilon, with divergence b. In particular its total outgoing flow at every vertex is at most epsilon(n−1)<=M.

To round without losing that bound, split each vertex into v_in and v_out, with an arc v_in->v_out of integer capacity M. Represent each original arc v->w by v_out->w_in with capacity1. Attach a supersource to v_in with capacity b(v) when b(v)>0, and attach v_in to a supersink with capacity −b(v) when b(v)<0. The fractional flow f, with total outgoing flow carried on v_in->v_out, saturates all source and sink arcs: at v_in, incoming original flow plus b(v)^+ equals outgoing original flow plus b(v)^−. Thus this integer-capacity network admits a saturating integral flow. Every represented original arc carries0 or1; take those carrying1 as F. Conservation gives divergence b, the internal capacity bounds d_F^+ by M, and d_F^-=d_F^+−b bounds d_F^- by M+k. Cyclic components of the integral flow cause no problem and may be retained.

For an outgoing cut, deleted arcs are bounded both by M|S| and by (M+k)|V\S|. The analogous incoming-cut bounds interchange the two degree bounds. Both are therefore at most (M+k)min(|S|,|V\S|). This proves all claims. ∎

The rounding does not prescribe paths, control their lengths, or provide internally disjoint routes for different cycle teams. It is useful precisely when an arc subset, rather than a path-by-path lift, is wanted. It uses no parallel artificial arcs in its output.

## 2. Balanced edge splitting at the source scale

Fix c>0 and a fixed positive integer l. For all sufficiently large D, every balanced n-vertex simple digraph with n<=D^1.02 and two-sided cut expansion at least cD^.90 admits a partition into l balanced spanning subgraphs, each with two-sided cut expansion at least c_l D^.90, for a positive constant c_l depending only on c,l.

It suffices to split into two and iterate a fixed number of times. Color arcs independently red/blue with probability1/2. For a cut with smaller side s and a directed cut size a>=hs, a lower-tail bound shows that either color has fewer than a/4 arcs with probability at most exp(−a/16). The union over colors, directions, and subsets is bounded by a constant times sum_{s>=1}(n exp(−h/16))^s=o(1). Thus both color classes have two-sided expansion at least h/4.

Since the original digraph is balanced, red imbalance at a vertex is a mean-zero sum of at most2(n−1) independent variables with range length1. Hoeffding and a union bound give, simultaneously at all vertices, absolute imbalance at most k=ceil(sqrt(n log(16n))) with probability at least7/8. The blue imbalance is the negative of red's. Hence for large D both expansion and imbalance events occur together.

Apply Lemma1 to the blue graph with b equal to its own imbalance, expansion h/4, and M=ceil(4kn/h). Delete its resulting F from blue and add F to red. Both resulting graphs are balanced, disjoint, and exhaust all arcs. Red still has expansion h/4; blue has expansion at least h/4−M−k. At the source scale,

 k=O(D^.51 sqrt(log D)),  M=O_c(D^.63 sqrt(log D)),

so M+k=o(D^.90). Both expansions are at least h/8 for sufficiently large D. A fixed number of such splits proves the assertion. A partition into exactly l follows by splitting pieces until there are l of them. All thresholds are uniform over the allowed n.

This repairs the balance omission of independent edge coloring ONLY when the input expander is already balanced. It does not turn arbitrary scale pieces into balanced inputs.

## 3. Eulerian sampled reservoirs

Fix c,p>0 with p<1. Let D^.90<=n<=D^1.02, and let P be a BALANCED simple digraph on n vertices with two-sided cut expansion at least cD^.90. There is a vertex subset V' of order at most2pn and a balanced subgraph Q supported on V' such that:

- Q has two-sided cut expansion at least D^.77/8 for sufficiently large D;
- Q is obtained from the actual induced digraph P[V'] by deleting an arc set with maximum in- and out-degree o(D^.77);
- P−Q is balanced;
- every original vertex has at least a fixed positive multiple of pD^.90 incoming and outgoing neighbors in V'.

**Sampling and the permissible exponent.** Form the simple undirected graph U by forgetting directions and merging antiparallel pairs. Every cut of U has at least as many edges as either directed cut of P, so U has cut expansion at least cD^.90. Apply the proof, not merely the displayed exponent, of source181 `lem:vertex-sampling`, `sections/residue.tex`57–265. Replace its tau=D^.74 by tau=D^.77. Its two essential perturbation ratios become tau/h=O(D^−.13) and tau n log n/h²=O(D^−.01 log D), both tending to zero. Its fixed witness-family concentration and order estimates are unchanged. Thus with probability1−o(1), U[V'] has undirected cut expansion at least D^.77 and |V'|<=2pn. Separately Chernoff gives sampled IN- and OUT-neighbor counts at least pcD^.90/2 at every original vertex, since both original degrees are at least cD^.90.

**Sampled imbalance.** For each v, conditional on v being sampled, its induced imbalance is

 sum_{u!=v}(1_{v->u}−1_{u->v}) 1_{u in V'}.

The coefficients are in {-1,0,1}; antiparallel pairs cancel exactly. Its mean is zero by original balance. Hoeffding and a union bound show that all sampled vertices have absolute imbalance at most k=ceil(sqrt(n log(16n))) with probability at least7/8. This event can be intersected with the preceding probability1−o(1) events; independence is not needed.

For any cut A in P[V'], the sum of its two directed cut sizes is at least the corresponding U[V'] cut size. Their difference is the sum of the induced imbalances over A. Since total imbalance is zero, its absolute value is at most k min(|A|,|V'\A|). Each directed cut therefore has at least (D^.77−k)/2 times the smaller-side order, and hence at least D^.77/4 for large D.

Apply Lemma1 INSIDE P[V'] with its actual imbalance b, expansion h'=D^.77/4, and actual order n'<=n. Its removed arc set F has degrees at most

 M+k <= ceil(4kn/D^.77)+k = O(D^.76 sqrt(log D))=o(D^.77).

Thus Q=P[V']−F is balanced and retains expansion at least D^.77/8. Since P and Q are both balanced, the global complement P−Q is balanced as well. This proves the assertions. ∎

The source's printed exponent .74 would NOT suffice for this particular correction bound: kn has exponent1.53, while (D^.74)^2 has exponent1.48. The valid .77 adjustment is essential; it remains below the source proof's strict .78 sampling threshold. All source hypotheses and finite-graph simplicity are retained.

## 4. What this does and does not repair

Together, sections2–3 permit several disjoint balanced edge reserves and, in each, a small sampled Eulerian reservoir, with balanced global complements. This removes a concrete local imbalance obstruction while staying inside the source scale. It is stronger than merely recording that random imbalances are small.

It does NOT supply a linear directed-simple-path partition of the nonreserved arcs. Such an assertion does not follow from the undirected endpoint-path theorem, even for the nearly balanced classes arising here. It does NOT construct balanced overlapping boxes at the scale-splitting stage. It does NOT replace the existing r33 low-degree folding and team-routing obligations or resolve the full cycle conjecture.

Operation credit: standard fractional flow feasibility and integer-capacity flow rounding; source181 deterministic witness-family sampling; elementary concentration and cut-balance identities. These are supporting author derivations. No independent proof, formal verification, or literature substantiality verdict is claimed.
