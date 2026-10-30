# r58 — Alofi–Dukes lacking-polynomial conjecture: unresolved

Status: zero credit, no nomination, no PROOF.md, no Lean or paper. One fresh target screened and sustained; no other full target pursued. Counts remain 6 additional / 36 total, subject solely to root acceptance. This family is stochastic sandpile rank enumeration, not bootstrap spanning-set counts, polyomino area formulas, or any accepted family.

## Source and scope

A. Alofi and M. Dukes, *A note on the lacking polynomial of the complete bipartite graph*, arXiv:2411.02667v1, 4 November 2024, published Discrete Mathematics 348(2) (2025), 114323, DOI 10.1016/j.disc.2024.114323. Original PDF fully read, including Definitions 1/3, Theorem 2, Propositions 4/7/9, Theorems 8/10/12 and Conjecture 13 (PDF p9). Live arXiv metadata lists only v1; author publication list links the journal citation back to that preprint. This is an expert/published author conjecture, not a registry-generated question. **Published-body comparison remains HOLD:** no VoR body obtained. A guessed ScienceDirect PII request returned403; its identity was NOT established, so it is not evidence that the actual article itself was fetched. No repeated publisher requests, challenge bypass, or alternate account access.

Literal scope, paraphrased: for every pair of integers m,n>=2, the coefficients of L_{m,n} are (i) log-concave and (ii) unimodal. The sink belongs to the first part of K_{m,n}; swapping m,n changes the polynomial. Define N=m+n-1 non-sink vertices, with A of size m-1 and B of size n. A stable configuration has 0<=c_v<d_v, and is stochastically recurrent iff some edge orientation satisfies indeg(v)>=d_v-c_v for every non-sink v. Set l_v=d_v-c_v-1. Then L_{m,n}(x)=sum over DISTINCT feasible l of x^{sum l_v}. Orientations are witnesses, not multiplicities. Source degree is R=(m-1)(n-1). Required inequalities are a_k^2>=a_{k-1}a_{k+1} for 1<=k<R. No equality classification is asserted or silently needed for the non-strict source question. A full stronger strict result would require separate equality analysis.

Source-known special cases: a_k=sum_{i<=k} binom(n,i), 0<=k<n, for m=2; a_k=sum_{j<=k}(k-j+1)binom(m-1,j), 0<=k<m, for n=2. Their log-concavity follows by repeated partial summation (Theorem12). Source explicitly already rules out the stronger root-sector criterion via L_{2,4}; that is not our discovery.

## Closest bodies and bounded prior screen

* Chan–Marckert–Selig, arXiv:1209.2038v1, orientation characterization Theorem3.2, actual proof pp12–14, Definition3.4, deletion/contraction Theorem3.9 and its different contraction convention. Read actual bodies. Their original stable convention is shifted by one; Alofi–Dukes explicitly translates it. Their recurrence is x L_{G\\e}+L_{G.e}, not ordinary Tutte deletion/contraction.
* Selig–Zhu, arXiv:2409.11811v1 (the live unversioned PDF still identifies v1), Theorems2.1–2.2 and full forbidden-subconfiguration/linear-time characterization proof pp4–6 read. Their graph notation has m non-sink top vertices, hence m there is m-1 here. Their Theorem3.2 is a sorted Ferrers-pair bijection; it is not a proof of unsorted coefficient log-concavity. The needed permutation weights must be retained.
* Eur–Huh–Larson, *Stellahedral geometry of matroids*, arXiv:2207.10605, actual Corollary1.14 and surrounding Theorem1.12, plus integral polymatroid §3, read. It proves log-concavity of q^r T_M(q^{-1},1+q). No identity with the source L is available: direct subgraph expansion gives, at K3,3, [1,4,10,20,35,47,48,30,9,1], whereas L has [1,5,15,30,39]. Runnable exact check tutte.py. This excludes identification of these two exact polynomials; it does not exclude all sophisticated uses of their theorem.
* Chan–Pak, *Log-concave poset inequalities*, JAMR2(1)(2024)53–153, actual pp61–64 Theorems1.20–1.24 and §11 proof read. Counts are sum omega(l)/prod l_v!, or t^{sum binom(l_v,2)} times those counts for 0<=t<=1. They are not source unit-weight coefficients. Their factorial weights cannot be canceled by choosing fixed multiplicative omega: l=e_i forces omega_i=1, whereas l=2e_i would then have weight1/2, not1.

Current public registry attempt happened BEFORE numerical/method investment. Omega dev HEAD retrieved at actual 2026-10-29T15:49:51.882004Z: 6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3, commit time15:49:17Z. This differs from supplied r56 head3b4135… and r54 baseline0169726…. Full delta NOT obtained. Four following distinct head requests failed shared GitHub API rate limit403; no API retry or alternate authentication was used. This leaves current broad coverage INCOMPLETE. Cached r56 D5/Problems scopes (12554/1551, complete only at their old revisions), Omega main, OpenAI preprints, AIM and Count trees were copied with hashes; lexical results are in registry-screen.json. No global absence from filenames or stale caches is claimed.

The directly relevant public Omega Problems/alofi-2024-stochastic-sandpile-bipartite-half.md and full15909-byte Lean body were fetched/read at BOTH immutable baseline0169726… and current6c27b0…. Bytes match. They resolve Question6 of this SAME paper: recurrent states <=half of stable states, equality iff m=2. Its proof sums grain lower bounds and uses complement involution. It does NOT establish Conjecture13 rank log-concavity. Its note identifies preregistration issue10704 but does not give original commit chronology; that chronology remains unverified. No freshness claim against Question6 is made. A cached OpenAI common-polymatroid-bases geometry proof body was read: enlargement/counting estimates for an FPRAS are not an exact unweighted rank-sequence theorem. Current four other registry heads remain unverified. Web searches are bounded discovery aids, not global priority clearance. Exact HTTP URLs, actual UTC, bytes and SHA256 are retained.

## Route 1: exact Hall inequalities and discrete polymatroid structure

The following is an ordinary elementary reduction, NOT a solution or nominated new theorem.

For any connected graph with sink, let E(S) denote all edges incident to a non-sink subset S (each edge counted once). A nonnegative integer l is feasible iff

    l(S) <= f(S):=|E(S)|-|S|  for every non-sink S.                 (1)

Proof of necessity: each vertex in S needs at least l_v+1 incoming edges, which must be distinct edges in E(S). For sufficiency, form a bipartite matching graph with l_v+1 slots for vertex v on the left and graph edges on the right, each slot adjacent to incident edges. For any left-slot subset with vertex support S, its size is <=sum_{v in S}(l_v+1)<=|E(S)|; its neighborhood is E(S). Hall gives a matching saturating all slots. Orient each matched edge into its matched vertex and orient all other edges arbitrarily. Singleton inequalities give l_v<=d_v-1, so c is stable. This proves precisely the source orientation existential, without counting its witnesses.

For K_{m,n}, write l=(a,b). If a_i^down,b_j^down are decreasing rearrangements and A_i,B_j their prefix sums, (1) is exactly

    A_i+B_j <= i n+j m-i j-i-j
          for 0<=i<=m-1, 0<=j<=n.                              (2)

There are i n+j m-i j incident edges. For fixed cardinalities, largest l-sums use the largest coordinates, proving both directions of (2). This independently recovers the companion forbidden-subconfiguration characterization with c=d-1-l and the correct m-1 parameter shift.

Moreover f is integer-valued submodular: incident-edge cardinality is a coverage function and |S| is modular. It is nonnegative: choose a rooted spanning tree; the parent edge of each v in S is a distinct edge incident to S. Set g(S)=min_{T superset S} f(T). Then g is normalized, monotone, integer, submodular. Indeed minimizing supersets T,U give g(S)+g(H)=f(T)+f(U)>=f(T union U)+f(T intersect U)>=g(S union H)+g(S intersect H). Nonnegative l satisfies (1) iff l(S)<=g(S): the nontrivial direction follows l(S)<=l(T)<=f(T) for every T superset S. Thus feasible vectors form an integral polymatroid.

For completeness the discrete exchange bridge can be proved directly, so it is not an unproved formal assertion. If feasible x,y satisfy |x|<|y| and x+e_j were infeasible for every j with x_j<y_j, choose a tight f-set T_j containing j (integrality gives x(T_j)=f(T_j)). Tight sets are closed under union: modular x and submodular f force equality for union and intersection. Their union U is tight and contains all deficit coordinates. Hence y(U)<=f(U)=x(U), while y_i<=x_i outside U, contradicting |y|>|x|. Thus exchange holds.

Where the route stops: this does NOT turn unweighted ranks into Chan–Pak factorial-weight ranks. Cloning each coordinate into two labels at K3,3 weights a vector by product binom(2,l_i), also not1 (exact counts retained). Exchange alone provides existence of augmentations, not a counting injection. No theorem claiming all integral polymatroid unit-weight rank sequences are log-concave has been established here.

## Route 2: ordinary Lorentzian obstruction

Let F(x0,x1,...,x5)=sum_{l feasible on K3,3} x0^{4-|l|} x^l, with coefficient1. Every degree2 monomial in x1,...,x5 is feasible: singleton bound2 and all two-vertex bounds>=3 suffice, and all larger f bounds>=2. Therefore the restriction of partial_{x0}^2 F to x0=0 is 2 h2(x1,...,x5). Its Hessian has diagonal4 and off-diagonal2, i.e. 2I+2J. On the sum-zero subspace its eigenvalue is2 (multiplicity4); on the all-ones vector it is12. Thus it has five positive eigenvalues. The Hessian is a principal submatrix of the full quadratic derivative Hessian, so the latter cannot have at most one positive eigenvalue. The usual ordinary Lorentzian sufficient condition fails already at this genuine source instance. Normalizing coefficients changes the object and leads back to the factorial mismatch. This is a method refutation, not a counterexample to Conjecture13.

## Route 3: pair-sum fibers and balanced allocations

For w>=0 integral and |w|=2k define

    F_w={x integral : x>=0, w-x>=0, x and w-x satisfy(1)},
    C_w(t)=#{x in F_w : |x|=t}.

Then C_w(t)=C_w(2k-t) by complement. More importantly,

    a_k^2 - a_{k-1} a_{k+1}
       = sum_{w:|w|=2k} [C_w(k)-C_w(k-1)].                     (3)

Both sides count ordered pairs by their coordinate sum; every pair belongs to exactly one fiber. Consequently the uniform central-fiber inequality C_w(k)>=C_w(k-1) would prove full log-concavity and hence source(ii). This is the exact remaining sufficient inequality, not an assertion that it holds.

For this family, inequalities for F_w are explicit lower/upper subset constraints:

    w(S)-f(S) <= x(S) <= f(S),  0<=x<=w.

A necessary step is balancing odd coordinates without breaking a tight subset. Simple lexicographic midpoint rounding fails on K3,3. With w=(0,3,3,1,1), floor(w/2)=(0,1,1,0,0); giving the first half of odd coordinates their ceilings yields x=(0,2,2,0,0). Its second A and first B coordinate sum4 exceeds their incident bound3. Nevertheless x'=(0,2,1,1,0) and its complement (0,1,2,0,1) are both feasible and balanced. So failure is specifically the tie-breaking construction, not nonexistence or the conjecture.

The graph from level k-1 to k joins x to x+e_j whenever both points lie in F_w. Exchange above gives at least one outgoing edge whenever |x|<|w-x|: choose j with x_j<(w-x)_j and x+e_j feasible; the other component loses e_j and remains feasible by heredity. This does not prove Hall's condition for that bipartite graph. For w=(0,0,2,2,2), k=3, there are6 left and7 central points. Left degrees are2(three times),3(three times); right degrees are2(six times),3(once). Thus the crude min-outdegree >= max-indegree shortcut fails, though a matching can still exist. An injection or a stronger Hall/flow argument needs genuinely additional work.

## Computation and falsifiers

check.py uses integer arithmetic, sorted-coordinate orbits and exact multinomial multiplicities. It checks33 rectangles with2<=m,n<=7, m+n<=12; all full coefficient sequences in checks.json are log-concave. It reproduces all displayed source table rows in this range and both source closed forms. Independent enumeration of all2^9 orientations and all compatible l agrees exactly for K3,3; a separate2x4 orientation check agrees too. These are validation of the reduction/code, not a proof for all m,n.

Pair fibers were fully enumerated for K3,3 (8100 ordered pairs,953 fibers), K3,4 (236196 pairs,10080 fibers), K4,3 (288369 pairs,11214 fibers). No nonunimodal fiber was found. This finite support proves neither the uniform fiber inequality nor even the next rectangle. fiber.py certifies the two explicit route obstructions; tutte.py certifies the exact polynomial mismatch. All helpers run under copied AS512MiB/CPU210s/wall230s/BLAS1/process-group RSS512MiB guard; no cap raised. Reproduce: `sh run.sh python3 check.py`, `sh run.sh python3 fiber.py`, `sh run.sh python3 tutte.py`, then `sh run.sh python3 verify.py`.

Strongest mathematical objection: (3) is only a sufficient reduction and no uniform central-fiber comparison has been proved. A counterexample to that comparison would refute this proposed proof route, NOT necessarily the source since other fibers may compensate. A source counterexample must instead give actual m,n,k and exact full a_{k-1},a_k,a_{k+1} violating the source inequality. Unimodality would remain a separate issue after such a log-concavity refutation.

Strongest provenance objection: live broad registries and actual published target body are not cleared. Even a later complete proof would require these holds resolved and substantive/classical-subsumption review. No novelty, eligibility, priority, full proof, formal certificate, or source resolution is claimed.
