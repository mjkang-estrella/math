# Sustained routes and precise stops

No discovery endpoint was obtained. All calculations here are diagnostics, not Lean certificates.

## 372609 — local quasi-kernel expansion

Primary: Clow, 2601.11847, Conjecture 5.1; source Theorem 1.2, Corollary 2.2 and proof of Theorem 1.4 were compared. For a finite sourceless oriented graph, let A(v)=N+(v), C(v)=A(v) union {v}. Then

S(v) = {u outside C(v) : N-(u) is a subset of C(v)}.

Because v cannot point to an outside vertex, and the original graph has no sources, this is equivalently the vertices outside C(v) with nonempty in-neighborhood contained in A(v). S(v) is independent. The exact target is max_v (|A(v) union N+(S(v))| - |S(v)| - 1) >= 0.

First mechanism: maximize an expansion slack by charging each member of S(v) to an incoming edge from A(v). This only gives |S(v)| <= 3|A(v)| <= 9, insufficient to prove the target: the out-neighborhoods of members of S(v) can overlap. An injective charge from S(v) into A(v) union N+(S(v)) leaving one unused vertex would suffice. No such charge was established. Even if each source has an out-neighbor, Hall's condition is missing. The extra forbidden-short-cycle hypotheses in source Lemmas 4.1–4.3 establish disjointness in a restricted class; they cannot be discarded.

Second mechanism: try to adapt the source's minimal-counterexample argument, which leads to 3-out-regularity for a smallest counterexample to a GLOBAL small-quasi-kernel theorem. That minimality concerns a different predicate. Removing sinks or low-degree vertices from a graph violating the LOCAL conjecture changes which outside vertices become sources. There is no proved deletion-monotonicity lemma for the local slack. Thus the source reduction is not a proof of Conjecture 5.1.

Third mechanism: exact seeded annealing on valid sourceless oriented 3-out-regular graphs, orders 7,9,12,16,24,32. Mutation replaces one out-neighbor while rejecting reciprocal arcs and new original sources. The objective minimizes the maximum slack and then the sum. Script and all best graphs/slacks are retained in outputs/quasi.json. The unmodified cyclic tournament at order 7 has no allowed one-out-neighbor replacement; this is a limitation, not exhaustive search. For orders 9–32 the best maximum slack found was 2. No negative maximum was found. These tests sample only 3-out-regular graphs and do not clear graphs with sinks or mixed degrees.

Cyclic independent-cluster blow-ups give another structural check. In a directed three-cycle blow-up with positive cluster sizes a,b,c<=3, for v in the a-cluster, S(v) is the c-cluster and A(v) union N+(S(v)) consists of the a- and b-clusters. If all three vertices' cluster types failed, one would have a+b<=c, b+c<=a, c+a<=b; summing contradicts positivity. Thus this natural low-expansion family cannot refute the target. This observation is restricted to that family and receives no credit.

Remaining lemma: a general local charging/selection theorem under outdegree <=3, or an exact oriented sourceless counterexample with all slacks negative. Only after that would finite graph semantics be formalized.

## 373230 — Mostar maximum

Primary: 2602.17276 section 4.3, Conjecture 4.3; later/earlier relevant primary bodies 2210.03399 and 2211.06682 were fetched. The exact Mostar sum is over unordered edges; for each edge uv it uses the difference between the two vertex sets defined by STRICT distance comparison. It is not a sum of distance transmissions in arbitrary diameter.

A useful ordinary identity: if the connected graph has diameter <=2, then n_G(u,v)-n_G(v,u)=deg(u)-deg(v). Indeed, the endpoint contributions cancel, common neighbors are equidistant, and only exclusive neighbors contribute. Hence Mo(G) is the Albertson irregularity in this class. The primary discussion in 2211.06682 already observes this and explains why the conjecture follows in diameter two. Merely repeating that proof is excluded. The substantive missing step is forcing an extremizer to have diameter <=2 (or another global comparison).

A second exact reduction concerns clique/independent blow-ups of a connected base graph H with at least two vertices. Let cluster weights be w_i>0. Vertices in different clusters have base-graph distance; distinct vertices in one clique cluster have distance 1, and in one independent cluster have distance 2. For an edge between clusters i,j, the signed strict-distance imbalance is

  w_i*w_j copies of a common imbalance z_ij,
  z_ij = (w_i-1)*s_i - (w_j-1)*s_j
         + sum over k outside {i,j} w_k * sign(d_H(k,j)-d_H(k,i)),

where s_i=0 for clique clusters, s_i=-1 for independent clusters; endpoint contributions +1 and -1 cancel. Intra-clique edges have zero imbalance by symmetry. Thus Mo = sum_{ij in E(H)} w_i*w_j*|z_ij|. This reduces a structured search to small weighted base graphs, without claiming every graph has this form.

Tested 30 seeded random positive compositions/clique assignments for every connected unlabeled base graph of orders 2–5, separately at n=12,18,24,36. The best scores were 224,792,1920,6624, exactly the conjectured split-graph values. The script retains base edges, weights and clique flags. An initial endpoint-cluster coefficient error was caught before interpreting results and corrected: clique vertices must contribute zero rather than +1. Only the corrected replay is used; independent expanded-distance checks are retained in validation.

Primary 2210.03399 Theorem 2 has a bound for split graphs with arbitrary cross-edge count; it does not settle all connected graphs. Primary 2211.06682 bounds the relaxation Mo* by (2/sqrt(3)-1)n^3, larger than 4n^3/27. Its recursive construction is sharp for the RELAXATION, not automatically for Mo. We did not mislabel that construction as a counterexample. The April 2026 cut-edge paper 2604.06839 is only a restricted-class lead and was not used as a trusted subsumer: its edge-addition monotonicity proof asserts a false general principle (complete graphs have Mo=0 while deleting an edge can give positive Mo).

Remaining lemma: a valid compression making an arbitrary extremizer diameter two, with no decrease of the actual strict-distance sum; or a weighted base configuration yielding a genuine larger value. Neither was proved.

## 373308 — C4-free spanning-tree maximum

Primary current 2602.21639, Conjecture 1 and sections 2–3. The source classification is polarity graphs with exactly q+1 absolute points. The narrower MathDB phrase “precisely orthogonal polarity graphs” is not used to manufacture a classification counterexample.

First mechanism: exact low-order obstruction. The connected graph atlas has 57 C4-free unlabeled graphs of order 7. Kirchhoff cofactors give maximum tau=49=7^2, with witness edges retained. This is library-based exhaustive small-case evidence, not an exhaustive formal theorem or a resolution for all prime powers. A randomized greedy C4-free saturation search (350 starts each at orders 13 and 21) had best exact counts 185055<371293 and 87877028666<794280046581. Float determinants selected the best candidates; final counts were recomputed by exact integer determinants. No minimality or complete finite search is claimed at those orders.

Second mechanism: spectral pairing. For a polarity incidence matrix A including loops, the projective-plane identity A²=qI+J pairs nonprincipal eigenvalues +/-sqrt(q). When exactly q+1 points are absolute, the loop/degree correction gives Laplacian (q+1)I-A, with cofactor n^((n-3)/2). This is precisely the source computation, not a new proof. For an arbitrary C4-free graph, codegrees <=1 give a constraint on A², but the degree corrections are nonuniform and do not supply the same operator identity. Naive degree-product optimization leaves an exp(q/2+O(1)) factor, as the source explicitly states.

Third mechanism: insert the source stability theorem for sufficiently large even q and edge counts close to the extremal value. It embeds those graphs in a polarity graph; adding edges increases spanning-tree counts, so this regime is already resolved. A new proof would need to handle graphs BELOW that edge regime. Applying the same embedding to all graphs is unjustified, and passing to a merely edge-maximal C4-free graph need not force polarity structure.

Remaining lemma: a determinant bound using nonuniform degrees and codegree<=1 that recovers the missing exponential factor outside the stability regime, or an explicit low-edge-count counterexample. No candidate supports Lean investment.
