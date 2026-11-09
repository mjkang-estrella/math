# Dormant plan for349070; no dispatch

Use GPT-6.1 Sol high/default only if the root later authorizes formal work. No compiler, Lean tool, solver, formal API or child was invoked in this discovery lane.

First have root resolve the significance/routine objection and bounded prior-art gaps in FULLCANDIDATE.md. Do not spend formal effort merely because the algebra is short. Freeze the eventual Lean/mathlib revisions at that later stage; no installed dependency or available lemma is assumed here.

Literal intended endpoint: for every n:Nat, G:SimpleGraph(Fin n) with G.Connected, and x:Fin n -> Real with forall i,0<x i, define B i j=(if G.Adj i j then1 else0)+(if i=j then1 else0), s i=sum j,B i j*x j, and y i=x i/s i. Prove sum i,sum j,y i*B i j*y j <= sum i,abs(y i). A reviewer must confirm the chosen Connected convention on n=0 and match the exact source; the stronger finite symmetric-matrix identity can avoid all graph connectedness dependencies internally.

Required bridges, all included rather than axiomatized: (1) adjacency symmetry/zero diagonal; (2) B nonnegative and diagonal1; (3) s_i>=x_i>0 using the diagonal summand; (4) positivity of y and conversion of abs sum to ordinary sum; (5) two finite-sum reindexings by symmetry; (6) clearing each denominator using its nonzero proof; (7) exact square expansion; (8) nonnegativity of the double sum; (9) equivalence of the explicit double sum with the source matrix/vector expression. Prove the generic identity first using finite sums and field algebra; prove the literal graph theorem as its corollary. No convergence theorem or strictness correction is required for the endpoint.

Expected cost is a small finite-sum development, plausibly one module, but no verified line/time estimate is available. Do not infer that required graph and matrix conversions already exist in mathlib. All logical statements here are a plan, not checked Lean syntax.

Later acceptance still requires independent fidelity and significance reviews, adversarial proof review, pinned dependencies, #print axioms closure restricted to propext/Classical.choice/Quot.sound, no sorry/admit/addedaxiom/unsafe/native_decide, fresh source-only strict rebuild and paper. Root alone may dispatch or accept. Zero credit now.
