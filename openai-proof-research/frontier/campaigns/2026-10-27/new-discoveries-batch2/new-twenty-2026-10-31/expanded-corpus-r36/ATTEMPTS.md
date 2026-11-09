# r36 mathematical work, 2026-11-01

No result is nominated for acceptance. All diagnostics below are ordinary exact programs, not formal theorems.

## 343459 — full-scope finite refutation mechanism, parked for prior art

Read arXiv1908.03513 definitions in §2, Theorems2.8–2.9 and their proofs, Conjecture2.16/Observation2.17; published counterpart Conjecture12. The graph is simple and undirected; von(S) means odd neighbor parity, not the cellular-automaton neighborhood. All nonzero messages x yield codewords (x,xA) over F2. Their weights are |supp x|+|von(supp x)|, so enumerating all 1023 nonzero messages establishes the full minimum distance for this one graph, not a cutoff on possible codewords.

Zero-based adjacency row masks:
308,1004,667,710,485,403,282,574,115,142.
S={3,9}, von(S)={3,6,9}, minimum weight=5. The intersection equals S and the sets differ. `verify_diagnostics.py` independently computes every parity coordinate by arithmetic sums, rather than the search's XOR recurrence, and verifies symmetric zero-diagonal adjacency and all nonzero weights. See diagnostic-verification.json for the weight histogram. This is a genuine mathematical negation of the universal conjecture if the computations are certified; neither a domain repair nor a neighboring question.

Search found it after 3000 random graphs each at n=5,...,9 and 915 at n=10 (seed343459); this is not minimality evidence. Before Lean investment, live search located Brandon Dennis, *Kode linier biner dari graf sederhana*, ITB2023, repository72980. Its primary repository abstract explicitly says ChapterV §2 supplies counterexamples to the Mallik–Yildiz conjecture. The linked abstract PDF returned404, the repository landing returned200 and was saved. The full ChapterV proof body was not exposed by the public record (one public abstract file). No denied-route retries or author contact. This is a material old-source gap, so STOP this discovery route: do not claim a newly solved problem, and do not spend effort formalizing a potentially already answered family. The abstract is an explicit same-question prior lead, not an audited prior proof. Exact missing item: inspect the thesis ChapterV §2 and compare its conjecture and witness scope. No Lean packet.

## 344325 — curvature mechanism beyond degree-two diagonalization

Read §4 Proposition1 symbol coarsening (5), §5.2 projector(11), §7.1 original FEM-symbol description, the degree-two calculation, and Conjecture3. For d=deg, e the all-ones vector, D=I+(z-1)ee*/d, p_z(t)=(1+cos t)D. The exact coarsening is
F(theta)=1/2 [p_z(theta/2)* f(theta/2) p_z(theta/2)+p_z(theta/2+pi)* f(theta/2+pi) p_z(theta/2+pi)].
The alias term vanishes to fourth order. Thus F(theta)=2 D f(theta/2) D+O(theta^4), with its first two derivatives agreeing with that simpler function.

A conditional ordinary lemma: if f is a C2 Hermitian family, f(0)>=0, ker f(0)=span(e), and its least eigenvalue lambda has lambda(0)=lambda'(0)=0, then lambda_F''(0)=z^2 lambda_f''(0)/2. To verify the potentially dangerous eigenvector derivative term, normalize u=e/sqrt(d), write relative to u and u-perp:
f(t)=[a(t), b(t)*; b(t), C(t)].
At t=0, a=b=0 and C(0)>0. For the unique small eigenvalue, the Schur complement identity gives
lambda(t)=a(t)-b(t)*C(0)^(-1)b(t)+o(t^2).
D=diag(z,I), hence the congruence D f(t) D has scalar Schur coefficient z^2[a(t)-b(t)*C(0)^(-1)b(t)]. Scaling t=theta/2 and the whole matrix by2 gives precisely z^2/2. This handles nonzero b'(0); merely differentiating e*f*e would miss it. F(0)=2D f(0)D again has the same one-dimensional kernel, so iteration gives c_deg(z^2/2)^j whenever the base properties and positive base curvature are established.

Remaining full-scope bridges: recover the exact arbitrary-degree Lagrange basis/block convention from cited Garoni–Serra-Capizzano–Sesana reference16; prove kernel exactly span(e), positive complement and C2 least-eigenvalue selection at every level in that convention; establish positive base curvature; and certify the Schur expansion and iteration in Lean. The source only prints degree2 coefficients. Its inequality comparing lambda_min to 2-2cos(theta) ensures quadratic size but alone does not identify a simple kernel or prove differentiability. Do not treat it as an axiom for the missing bridges. Degree1 alias behavior works (scalar f=2-2cos theta), so no endpoint defect is being claimed.

Relevant later primary manuscript2403.02139 retrieved. Its aggregation strategy is different; the search found no occurrence of `conjecture` or `second derivative` in its extracted text. This is a bounded text nonfinding, not a full proof-body exclusion. No claim of novelty or routine consequence: the all-degree bridge and later symbol-analysis body comparison remain open. Potential formalization is substantial matrix perturbation/FEM work, not a 2x2 surrogate endpoint.

## 344115 — two distinct cube definitions and separator route

Read Definitions1.0.1–1.0.2, the original/imitative distinction, and final Conjecture5.0.4. O-codes have successive ones separated by >=p positions, with at most r consecutive gaps exactly p. I-codes have literal runs of <=r ones and zero gaps >=p between runs. Edges flip exactly one bit. Original length indexing is n-p in the initial arithmetic coding definition; the source thereafter uses n for word length. No replacement by generalized single-forbidden-word Fibonacci cubes is valid without a bridge.

The diagnostic builds both literal word languages and computes vertex connectivity by vertex-split unit-capacity max flow for every nonadjacent pair, capped at minimum degree. It checks 108 (n,p,r,kind) instances with n=2,...,7 and p,r=1,...,3: all have kappa=delta. This algorithm is not formalized; these are finite nonfindings. A first run failed because networkx was absent; retained failure log, then replaced it with a standalone exact flow implementation rather than altering the environment.

Beyond enumeration: O-codes form a downset under deleting ones. A deletion cannot shorten a gap between surviving ones, and cannot create a new chain of exact-p gaps. Thus deleting any set of ones gives a path to zero. This supplies connectedness and natural recursive coordinate fibers, but downset alone cannot prove maximal connectivity: two 2-cubes meeting only at zero have delta2 and kappa1. For I-codes, the downset step fails outright when deleting a middle one from a run leaves fewer than p zeros between the surviving runs (e.g.111 ->101 when p>=2). Deleting an endpoint of a run preserves admissibility and still proves connectedness. A successful induction must handle the zero-prefix fiber, the one-prefix/run fibers, and their cross-edge boundary, not assume the I-language is hereditary.

Precise missing lemma: for every admissible n,p,r and every deleted vertex set X with |X|<delta, the coordinate-fiber decomposition has a surviving cross-edge joining every surviving fiber component, including I-run boundary states. No uniform lower bound on these boundary sizes or Menger fan construction was obtained. Park; larger sweeps do not close this gap. No Lean endpoint or source-resolution assertion.

## Other actual primary reads

343537: source Conjecture1 and resolving-multiset definitions read. Public2607.28813 Theorem1.1 and Proposition3.1 with proof/table read: it supplies an11-vertex graph where only V resolves. Independent exact BFS/all2048-subsets reproduction passed. This settles the exact universal conjecture negatively before this work, so excluded for credit. The public proof delegates the proper-subset check to computation; this pass does not certify its exhaustive minimality search.

343558: source Definition1, Conjectures2–3, gadget Definitions4, Lemmas5–6 with proofs, Theorem7 proof and Corollary8 read. Theorem7's H'' is subcubic and has no good coloring. Thus its counterexamples to Thomassen also refute Barát's stronger assertion; the MathDB status caveat is unnecessary. Existing source result, zero credit.

344511: source Conjecture1.2, Theorem1.3, and final proof via Proposition3.5/open cover/compactness read. Primitive weights are not pairwise coprime. Exact full theorem already present. Supporting Lawrence and local-group lemmas not independently audited in full; no new proof claimed.

344734: Theorems1–2, Lemma1's closed-neighborhood bound, Lemma2 counting proof, Lemma3 binomial concentration, and final induction read. Exact triangle statement already proved in the source's published2020 version. No formalization needed for this exclusion.

343487: Definition2.1, ratio(2.3), scalable-space bridge Proposition2.9 context, Proposition6.4 proof and Conjecture6.5 read. The Hilbert snowflake embedding bound only gives sqrt(2), not 2^(alpha/2). Missing global powered four-point inequality for all Euclidean quadruples; no proof or exact counterexample obtained. No novelty clearance.
