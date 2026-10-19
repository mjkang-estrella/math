# Other structural screens

All of these are preselection comparisons. No theorem was frozen. They are not correctness or contribution reviews of previous authors.

## 186: the product-to-slice compatibility is already explicit

The graph source's `thm:variance` has no monotonicity assumption and uses every bias p, with constant 2^17/(log n)^2. Its Fourier and block operations were read. The hypergraph companion supplies the corresponding fixed-r exponent r/(r−1), again for arbitrary Boolean properties, not just monotone ones. The title of the first paper understates the actual contract.

The feasibility idea was to extend a function on m-subsets to other layers by averaging uniform completions/deletions. Its obstacle is preserving variance while controlling averaged edge gradients. Actual I60 §§2–3 already supplies the whole compatible calculation, not merely a mention of slice measures. If every invariant cube Boolean h obeys Var(h)≤a Σ I_e(h) at p=m/N, I60's Transfer theorem T gives

    Var_slice(f) ≤ (aN + E|Bin(N,p)−m|/2) δ_m(f).

Here δ_m is the probability that f changes after a uniformly random delete/add swap, and Nδ_m is the normalized influence used in the all-slice result. Its other convention is I_m=m(N−m)δ_m/N. The completion function has exactly the same mean on every layer. Conditional slice Poincaré loses at most |k−m|δ_m/2 in variance. The averaged adjacent-layer L1 gradients are at most δ_m. Threshold coarea, rather than an invalid Boolean-to-real L2 spectral assertion, then gives aNδ_m. These operations compose for every p; fixed-density lower/upper bounds are needed only for conversion to I_m. The endpoint singleton slices are treated separately in the older result.

Filmus, [1406.0142v2](https://arxiv.org/pdf/1406.0142v2), Lemmas5.5–5.6 were read at the displayed proof. The transposition Laplacian degree-d eigenvalue d(M+1−d) gives the exact factor1/(2M) in the unordered-pair Poincaré convention. This confirms the primary interface already used by I60. It does not make the transfer new. The later r110 actual screen also records that older route. Initial extension feasibility preceded the operative I60 read; this late antecedent was found before any freeze. No rescaled or endpoint variant was proposed.

## 206: exact full-lattice synthesis remains the old missing operation

The source characterization's `f:criterion` includes a global condition over all edge sets and admissible maps, in addition to local separation and triangle conditions. That condition ensures that all congruences, not only named congruences, occur in the given lattice. Its proof builds the algebra with all admissible unary maps. The full graph and Diophantine sections were read.

The circuit-template construction `n:circuit-template` uses a positive solution to specify literal weights. For circuit syntax length t it has a computable lattice-size ceiling Φ(t). The source's reading lemma recovers a positive solution bounded by60^m m! from a representation on m elements. The undecidability proofs `n:undecidable` and `n:interval-undecidable` use those exact contracts. They do not supply one fixed, solution-independent lattice table whose representability is equivalent to the circuit's solvability.

The strongest compatible reduction was already derived in structural r18's actual candidate: ask the finite representation oracle on the bounded finite list of lattice tables, then search for finite representations only for affirmative answers. A positive instance has its literal template on the list; the recovered representation-size bound makes the final search for circuit solutions finite. This is a bounded-use oracle reduction. It need not halt on arbitrary false YES answer strings, so it is not automatically a total truth-table reduction. The earlier full one-output many-one target remains unclosed. Its generic computability example also blocks inferring many-one completeness just from bounded-use completeness plus Boolean operations.

Two tempting syntheses are already excluded in that actual body. A concrete interval in a finite subgroup lattice always has a finite coset representation, including when the intended circuit is inconsistent. A finite meet/join diagram can embed in a finite partition lattice without exhausting it; local named gadgets therefore do not supply the global fullness condition. r68's actual working question tries two-unary expansion and exact recovery of the entire congruence lattice, a different still-unbuilt operation. The initial oracle idea here preceded reading the full r18 candidate. It is not a fresh result, and no modified one-output target was frozen.

## 184: nonuniform weights still live on a global maximum-degree scale

The correspondence-coloring `rounds.tex` one-round statement and setup use k=ceil(CΔ/log Δ), τ=Δ^(−.10), ξ=Δ^(−.14), and entry weights between Δ^(−3) and Δ^(−.99), for the original common maximum-degree parameter Δ. The completion proof uses the same Δ throughout: accumulated Tξ=o(1), residual degree at most Δ^.96 and available palette mass at the Δ^.99 scale. This is a nonuniform-entry mechanism, not a theorem allowing a different arbitrary d(v)/log d(v) palette at every vertex with no degree floor.

Davies et al., [1812.01534v2](https://arxiv.org/pdf/1812.01534v2), §7 Proposition11 and its recursive construction were read. It forces a fresh color by attaching copies whose old lists are already forced, while preserving bipartiteness and allowing arbitrarily large minimum degree. The actual r114 screen already applies this construction to any fixed proposed local constant. Thus the no-floor local-palette lead is already obstructed at the exact primary level. This is a particular stronger assertion's failure, not a defect in the stipulated source. The companion independent-set introduction was acquired initially but was not a proof input; it is omitted from retained bodies. No new floor optimization was selected.

## Narrower early exits: 180,181,256

180: the source's P4 closing corollary and proof already extend Hamiltonicity from planar graphs to cubic three-connected bipartite Pfaffian graphs through the stated decomposition. The large Hamiltonicity history has further operations. Only the indicated source passage and history search hits were inspected in this branch; this was not a fresh complete Hamiltonicity-proof or literature audit. No nonplanar restatement was proposed.

181: the source `thm:main` gives linear cycle/edge partitions of arbitrary finite simple undirected graphs. Its Eulerian corollary and quasirandom asymptotic conclusion were read. Structural r33's actual checkpoint already studies the balanced directed fold and private-subdivision compiler. Source deletions do not automatically respect directed balance, and directed expansion of an undirected part does not supply the missing small decomposition. A quadratic-size directed example diagnoses the attempted expansion, not the full directed conjecture. No new balance-preserving mechanism was built.

256: the nonsingular-systems introduction explicitly treats arbitrary coefficient groups and independent exponent-sum rows, with an arbitrary-system extension via finite relations. It promises a solution in some overgroup, not a torsion-free solution overgroup. Earlier nonsingular/Kervaire history hits indicated that parameter-only consequences had already been considered. Only the introduction and search excerpts were read in this branch; unused proof sections acquired too early were removed before sealing. This is not a full-source or primary exclusion. No overgroup-class preservation theorem was frozen.

Navigation also inspected catalogue entries178,203,210,247,250 and related titles. Those are not operative screens or clearance claims. The decisive record consists of the actual operations above and the source243/259 route notes.
