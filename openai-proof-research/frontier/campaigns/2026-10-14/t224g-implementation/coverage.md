# Exact coverage

`Sandwich w u b` says w=true implies u=true and u=true implies b=true. This formalizes the BOOLEAN hypothesis only; no Voronoi insertion geometry is proved to satisfy it.

- birth_identity and death_identity: for an arbitrary real-valued function on TWO Bool inputs and any sandwich triple, prove the complete drift-plus-refresh table, including the half mixed-coefficient drift correction.
- refresh_identity: derives the averaged two-fair-color refresh difference under w<=b.
- birth_minus_refresh and death_minus_refresh: subtract the refresh table to isolate the exact drift.
- replica_product_decomposition: real scalar x*y-1=(x-1)+(y-1)+(x-1)*(y-1).
- two_factor_telescoping: real scalar ab-cd=(a-c)b+c(b-d).
- pair_kernel: two sandwich triples yield the exact product-increment identity including the old-bit equality indicator.

The8 definitions explicitly encode these finite averages; no probabilistic measure or expectation is hidden in them. Arbitrary real f is allowed, so these proofs are not merely finite samples of payoff values.

Controls contain two positive nonvacuity facts (compatible mixed old bits and zero mixed-old product) and five exact counterexamples: deleting the mixed-old indicator, deleting drift, deleting the half mixed-coefficient correction, deleting the replica cross term, and deleting the sandwich hypothesis. They are proved inequalities, not expected compile failures.

The analytic author candidate remains entirely outside this formal coverage: locality for every selected subset and every formal cap, topology, arm inequalities, conditional signed messages, forest integration, replica independence, temporal densities, J1 compactness and full-plane convergence are not checked by these declarations. No finite theorem is advertised as an instance of the whole infinite process theorem.
