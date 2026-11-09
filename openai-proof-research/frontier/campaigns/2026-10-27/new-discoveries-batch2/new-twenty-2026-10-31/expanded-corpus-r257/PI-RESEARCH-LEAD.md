# Conditional next task for root to route to Pi

No full candidate survives. This document is a precise research interface, not a request to execute and not CANDIDATE.md.

Priority: 325400, after source qualification. Finish the thesis/citing-work/journal and visual figure inventory; do not infer clearance from the failed thesis fetch or the absence of a journal citation on arXiv. Refresh registry HEAD only when access is lawfully available. Check that no root/sibling has taken this record in the meantime.

If root clears these gates, test 2-connected nonchordal graphs on 9--11 vertices, excluding the printed graph classes and the triangle-free diameter-two case proved in ATTEMPTS.md. Use a fixed graph-generation budget of <=120 CPU seconds, <=140 wall seconds, at most two CPUs, sampled RSS <=6 GiB; stop on the first exact witness or at the cap. No full corpus sweep. Earlier source claims thousands of checked graphs without enough detail to establish an exhaustive order cutoff; 9--11 is a bounded exploratory choice, not an untested-range claim.

For each graph compute an exact integer all-pairs distance matrix and enumerate every S of size >=2. Compute the entire FC(S), not a tie-broken minimum. Reject the graph immediately if any FC is disconnected. Return a graph only if every FC is connected and a nonblock certificate is supplied. This algorithm is exponential in n but certificate verification is a finite direct calculation; no heuristic score is proof.

Certificate schema: n; sorted edge pairs; D[n][n]; for every ordered pair a path of length D[a,b]; triangle inequalities D[a,c]<=D[a,b]+D[b,c], zero diagonal, positive off diagonal, and edge lengths one; for each mask S with popcount>=2 the complete partiality vector, minimizer mask F, root r in F and a parent tree spanning F using graph edges. Nonblock witness: an induced chordless cycle of length >=4, or a verified nonclique 2-connected block with its connectivity certificate.

Soundness bridge for D: graph-edge paths give true distance <=D. Triangle inequalities and D(edge)=1 give D<=length of every graph path; therefore D equals graph distance. The partiality computations then use the source's d. Trees prove connectedness of the induced fair centers. A nonchordal cycle disproves being a block graph. Universal enumeration covers all allowed S; singleton S gives V and is harmless. For n=11 the table has 2036 relevant masks; straightforward integer/tree certificates are well below a few MiB. Lean can later prove the checker once and replay explicit data with kernel reduction, with no native_decide, new axioms, or unproved metric bridges.

If the bounded diagnostic finds nothing, return the exact tested graph list/hash and stop; it is not a theorem for all graphs. The missing general lemma remains: every 2-connected nonclique admits a disconnected FC. No significance claim is attached to the two reduction lemmas alone.
