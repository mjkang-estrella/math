# Technical investigation — no accepted result

## 340297: surviving hypothesis, not a solution

Primary: Bian, arXiv:1809.01769v1, §2.1–2.4, Conjecture 3 and Theorem 2. Read directly from the existing r482 cache, not a recursively copied evidence tree. Source takes distinct anchors in the unit square including the origin. For an involution permutation pi, write sorted coordinate arrays x and y and anchors (0,0), (x_i,y_pi(i)). Reflection symmetry is x=y when both arrays are strictly increasing. Reflection preserves the optimal value; it does not imply symmetry of each minimizer.

Historical r482 disposition for neighboring ID340296 parks the precise universal area bound because it entails Freedman's half-area conjecture. This is not a prior review or resolution of ID340297. The current r729 coverage dictionary contains none of our three shortlisted IDs. Historical text/ID scans found no target-specific mathematical rejection for the entropy or axial candidates; corpus inventories and long numeric diagnostic lists are not mathematical reviews.

Finite diagnostic: all 42 involutions of lengths 2 through 5, three deterministic-seed SLSQP starts each; largest endpoint-form set 19376. Enumerate grid-ended empty rectangles and compatible choices, then minimize their maximum area. This is a heuristic model: no Lean proof of grid discretization or exhaustive treatment of degenerate coordinate ties has been supplied. Removing zero rectangles is only justified for strictly distinct interior coordinates. Boundary/tie outputs are not certificates.

Strongest pattern pi=(4,2,5,1,3), six anchors including origin. A strictly interior asymmetric candidate has
x=(.35749162991891403,.49022033942254684,.6699528832721766,.7172681767424933,.8786594105842866),
y=(.35749162991892147,.4984072087827534,.6490568711412705,.7292468328425786,.8682676509394881),
model area .6470149607523377. Symmetric stationary candidate has model area .6471555870727481. Both are numerical; the second is not a certified global symmetric optimum. Other asymmetric outputs often have coordinate ties or worse objective.

Beyond the initial sweep: extracted the eight active packing forms at the symmetric candidate; found nonnegative weights summing to one with near-zero gradient. The resulting quadratic has negative eigenvalues (about -1.35 and -.99); it is not a lower-bound certificate. A further constrained eigenvalue optimization is recorded in symmetric-dual.json and did not establish a positive-semidefinite certificate. Numerical optimization status is not mathematical evidence of global optimality or impossibility.

Next concrete hypothesis: prove that every symmetric configuration for this pi has optimal packing area at least 6471/10000, while a rational rounding of the asymmetric candidate has area below 6471/10000. Needed: rigorous complete packing discretization and zero/tie treatment, a global symmetric bound (possibly a finite case split using active packing forms), and exact rational witness verification. A strict gap plus compactness must still produce a distinct-anchor global minimizer; compactification can introduce collisions, so existence cannot be silently inferred. Alternatively prove a universal upper bound on symmetric minimizers' transverse stability. No claim of a counterexample until those bridges close.

## 340478: full elementary argument, defeated by known same-object capacity

Primary Gu, arXiv:1809.07364v1, §5.2 Conjecture5.8 and Proposition5.9, including actual derivative/smoothing proof, read. Proposition5.9 already proves the identical-distribution Shannon case. A parameter-only formalization of that fact is not eligible.

For finite Sidon A, index A by 1..q. Sidon means unordered pairs with repetition have distinct sums. Therefore X+Y has exactly the entropy of the unordered pair {I,J}, with independent laws p,q (here q as a vector is temporarily written v). Natural logarithms change only the entropy unit.

A useful elementary symmetrization proof was derived here. Let r=(p+v)/2, d=(p-v)/2. For u in [0,1], put output masses
s_ii(u)=r_i^2-u*d_i^2,
s_ij(u)=2*r_i*r_j-2*u*d_i*d_j (i<j).
These are nonnegative probability masses: each is affine between the two valid endpoint laws. On the common positive support of r, h(u)=-sum s(u)log s(u) is concave. At u=0 all masses on that support are positive; differentiation gives
h'(0)=sum_i d_i^2(log(r_i^2)+1)+2*sum_(i<j)d_i*d_j(log(2*r_i*r_j)+1)
       =-log(2)*sum_i d_i^2,
since sum d_i=0 cancels the log r_i and constant terms. Coordinates with r_i=0 have p_i=v_i=d_i=0 and are removed. Concavity and continuity at zero endpoint masses imply
H(p,v) <= H(r,r)-log(2)*sum_i d_i^2 <= H(uniform,uniform),
the final step being precisely Gu's already-proved Shannon part of Proposition5.9. This ordinary argument closes the finite source claim but is not a Lean certificate and is not a discovery.

Subsumption screen found Jiang–Polyanskii–Vorobyev, arXiv:1804.08599v2 (5 December2018), §1 pp1–3: the same channel outputs {x1,x2}; it reports the exact no-feedback average capacity
R(E)=1-(q-1)/(2*q*log_2(q)),
attributed to Chang–Wolf, IEEE TIT27(1)(1981)41–48, DOI10.1109/TIT.1981.1056304. Twice this rate in base-q entropy units is exactly the uniform unordered-pair entropy 2-log_q(2)*(1-1/q). For this deterministic MAC the maximum sum rate equals the maximum output entropy over independent inputs: the individual constraints are H(X),H(Y), and the sum constraint H({X,Y}); the latter is at most H(X)+H(Y). Hence the reported known capacity subsumes the finite Sidon claim after the explicit sum/union bijection. This is an inferential bridge, not a claim that the old paper mentions Sidon sets. The 2018 primary definitions and capacity statement were read; Chang–Wolf's 1981 proof body was NOT obtained/read, and the 2018 coding-theorem dependencies were NOT independently reproved. This is sufficient to block novelty clearance, not to claim a new formal proof.

No Lean investment into a known theorem. The entropy symmetrization inequality itself may be a useful helper, but helpers and routine consequences receive no separate credit.

## 340561: primary obstruction

Khasraw–McInroy–Shpectorov arXiv:1809.10132v1: definitions of the graph and Conjecture6.2, Lemma6.11, Theorem6.12, Corollary6.13 and Theorem6.14 with proofs read. Distinct components have zero products between axes. This only makes a component lie in A_0(a) for an axis a outside it. Zero eigenspaces are subalgebras by the Seress law, but annihilation by axes is not annihilation by arbitrary nonassociative products. The source proves annihilation by the spine (right-nested monomials) and obtains the result if all but at most one component is slender. Restricting to slender algebras would just formalize a known partial theorem. No new example satisfying every Monster fusion rule was constructed.

Live successor Gorshkov–Shpectorov arXiv:2606.30048, Definition3.10 and Problem3.11 pp10–11, directly read. It repeats the broader primitive-axial decomposition question. This provides current context, not proof that no subsumer exists. No feasible full universal proof or fusion-consistent finite counterexample survived this pass.

## Registry and access limits

Current openai/math head 4eaee87548250b2682affda7d05d947c05554bae, committed2026-10-30T00:35:35Z; pinned CONTENTS retrieved and keyword screened. No exact relevant entry found; this is catalogue screening, not all proof-body clearance. Palomar documented public browse/index.json and API v1 results?q=anchored/Sidon/axial each returned HTTP403; no bypass or repeated request to those URLs. Historic successful revision651 does not certify today's access or results. Source receipts include UTC retrieval date, URL, response status, bytes and SHA256. No browser tabs, git, posting, subagents, or shared-ledger edits.
