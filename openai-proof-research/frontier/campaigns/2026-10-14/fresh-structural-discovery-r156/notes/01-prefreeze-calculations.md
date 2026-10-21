# r156 live calculations — subgroup flags

PREFREEZE / no nominee. First family screen: lattice-polytope/Ehrhart algebra, no catalogue matches under the recorded terms. Second/final family: subgroup-poset topology, selected Source310. No further family will be selected. Earlier arithmetic r44 already paid rational nontrivial-isotypic representation bounds; coefficient changes already occur in Source310 introduction. Neither is a candidate.

## Interval calculation (exploratory, to compare with primary proofs)

Let X=S_p(G) be nonidentity p-subgroups. For P in X, the normalizer condition in the p-group Q gives P<N_Q(P) whenever P<Q. Thus Q -> N_Q(P) is an order-preserving downward retraction of X_{>P} to p-overgroups normalizing P. This subposet is S_p(N_G(P)/P). A nontrivial p-core in that quotient contracts it. If P is p-radical, Source310 plus Quillen's elementary/all-subgroup equivalence makes its augmented rational homology nonzero, including the empty quotient case.

For an interval (H,K) with K a p-group: if H is not normal in K, the same normalizer map retracts it onto (H,N_K(H)], a cone. If H is normal, the interval is the proper nonzero subgroup poset of K/H. A nontrivial Frattini subgroup contracts the latter via Q -> Q Phi(K/H): a proper subgroup remains proper by the defining Frattini property. If K/H is elementary abelian of rank d, it is the subspace building, with reduced homology of dimension p^{d(d-1)/2} in degree d-2. The d=1 case is the empty building in degree -1.

For sigma=(P_0<...<P_k), the link is the join of (1,P_0), each (P_{i-1},P_i), and X_{>P_k}. Unless P_0 is elementary abelian and every P_{i-1} is normal in P_i with elementary quotient, one interval is contractible. Otherwise write d_0=log_p|P_0| and d_i=log_p|P_i:P_{i-1}|, a=sum d_i, M=p^{sum binom(d_i,2)}. Join Kunneth then gives

  Htilde_j(link sigma;Q) = Q^M tensor Htilde_{j-a+k+1}(S_p(N_G(P_k)/P_k);Q).

At an interior point x of sigma the local group is correspondingly H_i(X,X-x;Q) = Q^M tensor Htilde_{i-a}(S_p(N_G(P_k)/P_k);Q). Nonvanishing somewhere is equivalent to the elementary-section conditions and P_k radical, by stipulated Source310. This is a classical interval/join composition with the source, not evidence of a substantial result. Module equivariance and integral torsion need separate careful wording; no such stronger theorem is asserted here.

## What might go beyond this paid local computation

A global chain model supported ONLY on subgroups simultaneously elementary and radical would be a different assertion. Merely deleting nonelementary vertices using their original lower intervals and nonradical vertices using their original upper intervals is invalid: the first deletions can change intervals used by the second. Need test the strongest compatible composition, including Quillen/Bouc equivalences and homotopy-colimit replacements, not just this naive deletion.

Test case planned: GL_3(F_2), p=2. Its natural building is a connected incidence graph with reduced first Betti number8. The simultaneous elementary/radical intersection appears to consist of fourteen incomparable Klein-four subgroups, with reduced zeroth Betti number13. This is not yet a checked computation and will be independently enumerated. If confirmed, it defeats that direct induced-subposet model, not every compressed chain model or a new substantial obstruction theorem.

A compatible rank filtration of the full subgroup complex already yields local Steinberg modules at elementary subgroups. The resulting differential consists of residues to codimension-one elementary subgroups. Reverse filtration by radical groups can carry higher homology and connecting maps. The actual task is to inspect whether a stronger known construction already packages both; do not declare this an unpaid theorem by title mismatch.
