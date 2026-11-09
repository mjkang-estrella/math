# Dormant Sol formal plan — 346033
NOT dispatched. No Lean/compiler/checker execution in this lane. No formal acceptance prediction. Ordinary proof: FULLCANDIDATE.md. Journal/prior/significance gates remain HOLD. GPT-6.1 Sol high/default only for any later separately authorized continuation.

## Literal endpoint contract
Define a finite connected metric graph as the metric quotient of finitely many closed intervals [0,L_e], L_e>0 finite real, with endpoint identifications from finite origin/terminal maps, admitting loops and parallel edges. Define continuous vertex-matching edgewise H^2 functions and the actual continuity-Kirchhoff Laplacian on the graph L^2 space. Define mu_2 as the smallest strictly positive eigenvalue (equivalently index one in a multiplicity-counted spectral list with simple zero), not as an arbitrary supplied phase parameter. Define RealSecondEigenfunction(G,u) by membership in its operator domain, u!=0 and -u''=mu_2(G)*u on every edge with the stated vertex conditions. Eigenfunction conditions must be derived from the operator, with proof of equivalence to classical edge ODE form; they cannot simply be replaced by a trig-family field in the graph structure.

The intended Lean-shaped endpoint, after these definitions are implemented, is:
  forall G : FiniteConnectedMetricGraph,
    (connectedComponents (globalSecondHotSpots G)).Finite
    and ((globalSecondHotSpots G).Finite
         or not (globalSecondHotSpots G).Countable).
Here components are those of the SUBSPACE M, not ambient Gamma; globalSecondHotSpots includes all real nonzero second eigenfunctions and all global max/min points. Actual Lean namespace/signatures cannot truthfully be asserted before inspecting the pinned dependencies. Negation closure proves equivalence to the maxima-only definition.

No assumptions finiteDimensionalSecondSpace, trigRepresentation, semialgebraicM or finiteComponentsM may be left in the final endpoint. Any use of an abstract finite-chart theorem must be discharged for this graph operator.

## Infrastructure inventory: existing versus missing
This assignment supplied no pinned Lean/mathlib checkout or declaration statement bodies in its own input copies. Input author-MANIFEST records artifacts, not a verified library API. Protected or parent dependency trees were not read. Therefore ZERO relevant pinned declaration signatures are verified here. This is an evidence limit, not a claim that mathlib lacks these subjects. General familiarity with its reals, polynomial roots, finite-dimensional algebra, ODE and topology APIs is not a pinned availability audit.

Existing VERIFIED artifacts: primary ordinary spectral statements in Kennedy-Rohleder; Marker Theorem 3.5/Corollary 3.7 ordinary bodies; the explicit polynomial formula and finite-piece topology proof in this lane. None is a kernel certificate. No newly assumed axiom is permissible.

Required next statement-only inventory, if separately authorized: exact Lean/mathlib revisions; connected-component subtype and Set.Countable APIs; polynomial finite real roots/sign constancy; finite basis/linear independence and coefficient sphere; real trig derivatives, tangent half-angle and atan inverse/monotonicity; interval homeomorphisms/continuous images; first-order ordered-ring syntax and semantics, real-closed fields and a PROVED QE theorem with parameters, or semialgebraic projection. Check exact theorem conclusions and imported axioms before scheduling implementation. Missing verified support is not to be filled with a guessed theorem name.

## Dependency order and missing implementations
A. Metric quotient and analysis: finite interval disjoint union with endpoint equivalence; quotient topology equals path metric topology; all points represented including vertices; L^2, Sobolev domain, Kirchhoff traces and self-adjoint compact-resolvent spectral setup, zero simplicity for connected graphs, existence/positivity of mu_2 and finite real eigenspace. This is a substantial foundation unless a matching verified library already exists. An elementary alternative may define the finite Cauchy-data matching equations and prove complete equivalence with the source Laplacian spectrum; that equivalence is itself required, not a shortcut assumption.

B. Edge representation: regularity from weak H^2 equation to classical C^2, ODE uniqueness/energy identity, sinusoidal formula, finite basis and coefficient normalization. Could avoid full spectral finite-multiplicity proof via injectivity into R^(2E), but existence and identification of the first positive eigenvalue still need payment.

C. Finite atlas: Archimedean subdivision depending on k,L; shifted sine/cosine vectors; strict pole margin; closed finite t-intervals; inverse tan/atan; original vertex and loop endpoint matching; jointly surjective graph maps.

D. Real algebra: instantiate a finite tuple of real parameters, encode all vector sums and finite chart conjunctions in an actual finite ordered-ring formula, prove its realization iff graph-global maximum, clear strictly positive denominators, invoke kernel-proved QE uniformly in free parameter variables, then specialize. A semantic black-box assertion that 'this set is semialgebraic' is not a certificate. Implement QE if no matching proven library exists, or first supply a fully proved alternate polynomial projection/one-dimensional finiteness route. Neither an external CAS certificate nor an arbitrary-real oracle is authorized.

E. Topology: univariate sign decomposition using finite polynomial roots, map its connected pieces into Gamma, prove finite connected components of their finite union with endpoint identifications, and use the metric distance map to prove the countability dichotomy. Many general lemmas may exist but no names are verified here.

F. Fidelity/acceptance: separate source-definition review against literal raw record and source pages; no narrowing to simple spectra or algebraic lengths; pinned dependency lock; clean extraction/rebuild; transitive #print axioms limited to propext, Classical.choice, Quot.sound; no sorry/admit/axiom/unsafe/native_decide. All source-model and semantic bridges must be included. Parent must independently adjudicate prior/significance before costly execution.

## Feasibility judgment
The ordinary formula has finite size for each fixed graph, but the universal theorem and formal spectral/real-algebra foundations are large. A short final statement would conceal considerable infrastructure. Without a verified QE/projection theorem and a matching quantum-graph model this is not a small formal execution task. Do not dispatch on the strength of an abstract chart lemma alone. The current exact missing infrastructure, not proof length, is the reason the plan remains dormant.

