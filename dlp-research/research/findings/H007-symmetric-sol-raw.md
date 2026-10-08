# H007 symmetric equation proposals: raw T3 Sol report

Unverified initial hypotheses, not experiment evidence or accepted complexity claims. Root synthesis and independent reviews determine scope. No numerical test authorized.

**Two mechanisms survived the distinctness screen.** A third would have repackaged prior compact-segment circuits, polynomial joins, or reusable Gröbner compilation. Both cards below remain speculative; neither establishes improvement over the classical \(q^{1/2}\) baseline.

I read the research instructions and earlier hypothesis titles, with targeted reads of the earlier constraint proposals. I did not read other H007 initial proposals, edit files, run experiments, perform numerical scratch work, or launch children.

Here \(E/\mathbb F_p\) is ordinary, \(P\) has prime order \(q\), and \(Q=[k]P\) has a full-range unknown scalar. Costs include setup, unsuccessful attempts, elimination, extraction, memory, and final verification.

**Card 1 — Solve unordered decompositions through a divisor polynomial**

**Operation.** Generate \(B=q^\beta\) random known scalars \(a_i\), retaining points \(A_i=[a_i]P\), and discard duplicate \(x\)-coordinates. Construct

\[
H(T)=\prod_{i=1}^{B}(T-x(A_i)).
\]

For each random shift \(R=Q+[u]P\), seek four distinct dictionary abscissae whose signed points sum to \(R\). Replace the four ordered unknowns by the coefficients of

\[
F(T)=T^4-e_1T^3+e_2T^2-e_3T+e_4.
\]

The exact equations are:

\[
H(T)\bmod F(T)=0,\qquad
\Phi(e_1,e_2,e_3,e_4,x(R))=0,
\]

where \(\Phi\) is \(f_5(X_1,X_2,X_3,X_4,x(R))\) expressed in elementary symmetric functions of its first four variables.

The four remainder coefficients impose \(F\mid H\). Since \(H\) is square-free, every solution represents four distinct dictionary entries. Compute those remainder equations by repeated modular reduction of powers of \(T\), retaining their arithmetic DAG; then apply an explicitly bounded sparse elimination procedure to the five equations in four coefficient variables. Record all polynomial expansion and matrix work. Increasing the elimination bound is paid work, not a solver oracle.

**Extraction of \(k\).** Factor the recovered degree-four \(F\), look up each root’s known scalar, and check the sixteen sign choices. A verified decomposition gives

\[
k=\sum_{j=1}^{4}\epsilon_j a_{i_j}-u\pmod q.
\]

No unknown factor-base logarithms or relation matrix are needed. The dictionary is generated and charged during the attack; it is neither external advice nor a restriction on \(k\).

**Source of possible gain.** The proposed saving is in solving the *divisibility-constrained invariant system*. It must be substantially cheaper than enumerating triples or constructing pair-sum tables. Removing \(4!\) permutation copies alone supplies only a constant.

Under a random-dictionary coverage heuristic, a shifted target is decomposable with probability \(\Theta(B^4/q)\) when \(B^4\ll q\), up to fixed sign and permutation constants. Let:

- \(A(B)\) be construction and compilation work;
- \(C(B)\) be average work per shifted target, including empty systems;
- \(M(B)\) be peak memory.

Then the single-target estimate is

\[
W=\widetilde O\!\left(B+A(B)+\frac{q}{B^4}C(B)\right).
\]

Writing \(A(B)=q^{a+o(1)}\) and \(C(B)=q^{c+o(1)}\), the exponent gate is

\[
\max\{\beta,a,1-4\beta+c\}<\tfrac12.
\]

For example, at the **proposed parameter choice** \(\beta=1/5\), elimination must cost \(C(B)=o(B^{3/2})\), with compilation below \(q^{1/2}\). This is a budget threshold, not a measured prediction.

**Setup, memory, restarts.** Building the points and \(H\) costs \(\widetilde O(B)\) operations, apart from scalar-multiplication logarithmic factors. Store \(O(B)\) dictionary entries plus the actual elimination representation. Random shifts provide repeated trials against the same dictionary. If its coverage is unexpectedly poor, regenerate it and charge that restart. Coverage concentration is an additional assumption; a mean representation count alone does not justify the restart estimate.

**Primary prior-art distinction.** Semaev decomposition and elementary-symmetric reduction are established techniques. [Symmetrized Summation Polynomials](https://www.iacr.org/archive/eurocrypt2014/84410158/84410158.pdf) explicitly uses symmetric invariants and additional small-torsion symmetries. Those extra rational torsion symmetries are not assumed here. Known-log decomposition also needs comparison with [Amadori–Pintore–Sala’s prime-field method](https://eprint.iacr.org/2017/609).

The candidate-specific question is whether representing dictionary membership as **\(F\mid H\)** changes elimination complexity compared with four separate membership equations. I make no novelty claim for that encoding.

**Unsupported assumption.** The high-degree remainder equations admit elimination materially below the \(B^{3/2}\) gate. Their compact construction does not establish compact elimination: expanding them or eliminating their DAG auxiliaries could recreate an enormous system. The finite membership variety contains \(\binom B4\) possibilities, so ordinary dense quotient-algebra methods are an especially poor default.

**Cheap decisive falsifier.** Compare the divisibility encoding with the ordered-variable encoding on increasing small random dictionaries, separately recording unsuccessful target systems. Count remainder construction, expanded terms, elimination rows, extraction, and peak memory.

Reject the chosen implementation and \(\beta=1/5\) budget if unsuccessful trials already require \(\Omega(B^{3/2})\) charged work, or if compilation exceeds the square-root budget. A four-variable appearance or a \(24\times\) symmetry saving is insufficient. Small tests can reject this implementation; they cannot establish an asymptotic exponent.

**Disposition:** worth a tightly bounded algebraic screen. This uses a random scalar dictionary and invariant elimination, rather than structured factor-base tensor contraction.

**Card 2 — Target-conditioned inconsistency certificates inside the scalar circuit**

**Operation.** Encode the complete binary scalar map as a polynomial system over \(\mathbb F_p\):

\[
T_0=O,\qquad
T_{j+1}=T_j+[b_j]([2^j]P),\qquad
b_j(b_j-1)=0,\qquad T_n=Q.
\]

Use exact addition formulas with explicit infinity and exceptional-case branches. Normalization or inverse constraints must prevent denominator clearing from creating spurious solutions.

Search assignments of the scalar bits. At each node, specialize the assigned bits and run degree-capped sparse F4 elimination on the **whole remaining system, including \(T_n=Q\)**. Prune only when it derives an exact inconsistency certificate, such as \(1\) in the ideal. Otherwise branch again. Reuse symbolic preprocessing and valid reductions between sibling nodes, charging maintenance and specialization.

The algorithm always has an executable fallback: enumerate remaining assignments. The hypothesis concerns how much enumeration exact, cheaply obtained certificates remove.

**Extraction of \(k\).** A surviving complete assignment gives \(k=\sum_j b_j2^j\bmod q\). Verify \([k]P=Q\). Using \(n=\lceil\log_2q\rceil\) can yield duplicate representatives; reduction modulo \(q\) handles them without narrowing the original secret.

**Source of possible gain.** Incorrect partial assignments have no valid completion, but recognizing that may be as difficult as finishing the search. The opening is that many wrong branches might have low-degree inconsistency certificates that F4 finds before most bits are assigned.

This requires a quantified survival profile. Let \(N_t\) be the number of depth-\(t\) assignments retained by the capped test, and define the descriptive pruning quantity

\[
I_t=t-\log_2 N_t.
\]

Let \(C_t\) be average charged work for testing a child at depth \(t\). Binary branching gives the work gate

\[
W\;\lesssim\; A+\sum_{t=1}^{n}2N_{t-1}C_t
+\text{extraction and verification}.
\]

If \(C_t=q^{a_t+o(1)}\), the corresponding necessary exponent budget is

\[
\max_t\left\{
\frac{t-1-I_{t-1}}{n}+a_t
\right\}<\tfrac12,
\]

along with setup below \(q^{1/2}\).

This prevents a misleading claim based on the final system having only one solution. Certificates must prune early enough, and cheaply enough, across the entire tree. Numerous late contradictions do not help.

**Setup, memory, restarts.** Precompute the \(n\) public doubling points and construct an \(O(n)\)-size circuit. Charge every symbolic monomial, sparse matrix entry, reduction, and cached certificate. Depth-first traversal can limit live search state; algebraic caches may nevertheless dominate memory.

Randomizing bit order or elimination order is permissible, but each unsuccessful schedule and restart counts. Retain only certificates whose validity under specialization is established. No probabilistic rejection of potentially valid branches is allowed.

**Primary prior-art distinction.** Truncated Gröbner computation and solving variables during F4 are known; [Middle-Solving F4](https://arxiv.org/abs/1310.2332) is relevant methodological prior art, although it studies systems over \(\mathrm{GF}(2)\).

Earlier project proposals considered forward-coordinate interpolation and inverse-walk prediction. This card instead asks for **exact target-dependent contradictions from the full scalar circuit**. It neither predicts a bit from coordinates nor assumes a precomputed inverse table. Sparse Gröbner methods are also established; their existence does not imply favorable behavior on this circuit. [Sparse Gröbner Bases](https://arxiv.org/abs/1402.7205)

**Unsupported assumption.** Wrong prefixes usually admit certificates at degrees and matrix sizes that satisfy the survival/work gate. Constant circuit width does not establish this: eliminating intermediate states can produce constraints involving nearly all remaining bits. Extension-field solutions of a relaxation may also postpone contradictions, making the capped test weak even when it is sound.

**Cheap decisive falsifier.** For small representative prime-order curves, freeze the circuit, bit order, degree cap, and matrix budget. Traverse the actual tree and record \(N_t\), \(C_t\), certificate sizes, and all work. Compare against a matched square-root solver.

Reject a frozen configuration if low-cost tests retain almost every branch until late depths, while stronger tests consume the square-root budget before producing useful pruning. Do not count polynomial evaluation speed, isolated forced bits, or final uniqueness as success.

**Disposition:** higher risk than Card 1, but a distinct direct attack with a precise failure test. It requires no factor base, decoding, lattice reduction, or additive-combinatorial projection.

**Current assessment.** The supported estimate remains the square-root baseline, with **verified improvement: NONE**. Card 1 has the clearer next decision: determine whether divisor-polynomial membership reduces *unsuccessful* elimination cost enough to approach its \(B^{3/2}\) gate. Card 2 should proceed only with a frozen certificate budget and complete search-tree accounting. Neither relies on tensor trains, and neither is disposed of by the dense random-\(V\) TT obstruction.
