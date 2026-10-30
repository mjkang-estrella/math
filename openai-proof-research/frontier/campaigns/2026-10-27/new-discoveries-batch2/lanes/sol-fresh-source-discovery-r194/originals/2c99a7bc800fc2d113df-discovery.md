# r96 — full melonic log-concavity remains unresolved

Research only, 29 October 2026. Credit 0; accepted counts remain 8 additional/38 total. No PROOF.md: the full ordinary source conclusion is not proved. No Lean, paper, git, shared, candidate, ledger, account or external-posting operations.

## Early all-date screen and four attributed claims

Before mathematical investment, `audit.py` read and SHA-256 inventoried 5,918 all-date files under openai-proof-research whose names contain SUMMARY, discovery, FINDINGS, PROOF, review or ledger (case insensitive; md/json/txt). None matched the selected four families' names/identifiers. See duplicate-audit.json for exact scope and fingerprints; filenames alone were not used to establish novelty. An initial Aluffi–Chen–Marcolli moduli-space lead was immediately retired after the existing r59 discovery body disclosed Berczi–Kiem's exact public theorem. It is not a fifth invested claim.

1. Brändén–Ferroni–Jochemko's question whether log-concavity without internal zeros of a nonnegative gamma polynomial implies the same for its symmetric h polynomial, for every degree and every such gamma sequence. EXCLUDE: Ferroni–Panova–Venturello, latest arXiv:2502.08948v2, Theorem 1.3 proves exactly this. Read its Section 3 coefficient decomposition, Lemma 4.1 weighted-sign argument and Section 4 Theorem 4.2 lattice-path reduction; this is a public full-proof body, not an abstract/badge judgment. AMS VoR URL guessed from bibliographic information returned 404; no source clearance beyond arXiv claimed.
2. Harper–Kohli–Song–Tahar arXiv:2509.16868v1, Conjecture 1.8: for every alternating link L, all integer i,j,k,l satisfy |a_(i+k,j+l)| |a_(i-k,j-l)| <= |a_(i,j)|^2 for LG(L), and its support has no interior lattice holes. Latest abs reports v1, while the fetched v1 body itself is dated August 24, 2026; preserve that discrepancy. Source Definitions 1.2/1.7, Sections 5.2–5.4 and Proposition 5.4 read. Torus links and twist knots are already covered, with the latter proof explicitly omitting remaining coefficient cases. No all-link proof located in this bounded screen; not selected because the required invariant computation and arbitrary alternating-link bridge are substantially less controlled. No claim that its public finite cases prove the universal statement.
3. Stephanie Chen, latest arXiv:2503.16296v2, Conjecture 3.9: for every m>=4 and every 4<=j<=m-2, both f_m=((1+s)^m-(-1)^m)/(s+2) and h_m=f_m+(-1)^m strictly fail the degree-(m-1) ULC inequality. EXCLUDE FROM INVESTMENT: live MathDB367609 contains a full public proof claim by Shivam Patel (reply id77502153-cc94-4ccc-85d4-a3ba72777da5, posted August 2026). Actual whole proof read, including parity-binomial coefficients, quadratic F_(j,t), the affine parity-step barrier, two exact polynomial identities, positivity after j=4+u and both parity base cases. This is an existing full-scope proof claim, not independently certified here; do not label the mathematical conjecture definitively settled on a badge alone. Chen's Proposition 3.8 already proves overall non-ULC, so that cannot be rebadged. Publisher Chen body returned403; no retries.
4. SELECTED: Aluffi–Marcolli–Qaisar, *Motives of melonic graphs*, Ann. Inst. Henri Poincaré D10(2023),503–554, Conjecture 3.1, printed p24 of the fetched publisher file; repeated as Chen v2 Conjecture 2.3. For **every** melonic graph G constructed from one edge by repeated replacement of edges by strings of parallel-edge bananas, write the literal affine Kirchhoff-hypersurface complement class U(G)=sum a_j S^j, S=[A1]-2. Claim: a_j^2>=a_(j-1)a_(j+1) for every internal j. No restriction on construction depth, banana orders or valences. The actual publisher conjecture and Section3.5 were read. Published version reports verification through15 edges, versus13 in the preprint; this is only evidence, not a proof.

## Closest primary proof bodies and classical limits

Chen v2 Theorem3.4 proves LC of f,g,h,b, while Proposition4.2 proves only clasped necklaces. Its proof factors out LC bananas and linear factors, reduces to p_(m,n), and uses p_(m,n)=(s+1)p_(m-1,n+1)+(n-1)(-1)^(m-2) plus explicit low-degree checks. This does not supply a coupled induction for arbitrary nested replacements. Chen Proposition2.5 records classical convolution preservation of LC sequences without gaps; the sum in her Eq2.12 requires additional cross inequalities. We do not credit convolution, the banana family, strings/products, or transfer helpers.

The original publisher Remark3.1 explicitly defeats the universal real-rooted route at the5-banana and the fixed120-degree root-sector sufficient condition at the31-banana; it also mentions a24-circle necklace. These are public obstructions, not findings of this lane. Geometric/Hodge language alone supplies no verified universal LC theorem here.

## Sustained full-scope route: two-terminal strata

Let A_G be the spanning-tree complement polynomial and B_G the separating-two-terminal-spanning-forest complement polynomial. For a single edge with variable x, (A,B)=(1,x). Under series and parallel composition of disjoint edge-variable sets:

- Series: (A,B)=(A1 A2, B1 A2+A1 B2).
- Parallel: (A,B)=(A1 B2+B1 A2, B1 B2).

These follow directly by partitioning spanning trees and separating forests according to their restrictions to the two components. B has degree one more than A. Let C=[A!=0,B=0], D=[A=0,B!=0], and H=[A=B!=0]. Simultaneous scaling of all edge variables changes B/A by the scaling parameter; consequently the both-nonzero stratum is **isomorphic**, not merely count-equal, to Gm times H. In particular U=C+(S+1)H. The edge state is (1,0,1).

Write T=S+1. Partitioning the ratios B_i/A_i at 0, nonzero, sum0 and sum1 gives the following uniform formulas, valid at arbitrary depths:

Series:
C'=C1 C2+T H1 H2;
D'=D1(C2+T H2)+(C1+T H1)D2;
H'=C1 H2+H1 C2+S H1 H2.

Parallel (exchange the tree/forest roles):
C'=C1(D2+T H2)+(D1+T H1)C2;
D'=D1 D2+T H1 H2;
H'=D1 H2+H1 D2+S H1 H2.

For example the parameter space for two nonzero ratios summing to1 is A1 minus{0,1}, whose class is S; for sum0 it is Gm, whose class is T. The remaining zero/nonzero cases give the displayed products. This explains positivity and provides a candidate universal induction. The geometric interpretation has not been independently reviewed; finite-field counts are checks of these formulas, not a replacement for the stratification argument or a new source result.

For n parallel edges the recursion gives H=f_n, C=n T^(n-1), and U=T f_n+n T^(n-1), exactly the source banana formula. Thus the two-terminal route contains the actual source objects rather than arbitrary sequences with matching first terms.

## Strongest falsifier of the attempted induction

Attempted invariant: C,D,H nonnegative LC with no internal zeros, pairwise synchronized (both mixed inequalities at every index), C>=H coefficientwise, and U=C+TH itself LC. It is **not preserved** by parallel composition.

Take ascending coefficient lists:
(C1,D1,H1)=((6,6),(3,3),(1,4)),
(C2,D2,H2)=((1,5),(6,1),(1,3)).
All three state polynomials in each input are linear, hence LC and pairwise synchronized; C_i>=H_i. Their U polynomials are (7,11,4) and (2,9,3), both LC. Parallel composition gives
C'=(46,100,92,38), D'=(19,29,22,12), H'=(9,38,20,12).
The H' coefficient defect at degree2 is 20^2-38*12=-56. This is an exact artificial-state cone obstruction. These triples have **not** been realized by graphs. The resulting U'=(55,147,150,70,12) is itself LC, so this is neither a source counterexample nor a refutation of a weaker direct-U induction. It shows precisely why proving only those state inequalities would not close the proposed stronger invariant.

In general, for F=sum F_r, its LC defect is the sum of individual defects plus mixed terms 2 F_(r,j)F_(t,j)-F_(r,j-1)F_(t,j+1)-F_(t,j-1)F_(r,j+1). The S H1H2 summand shifts indices. No preserved graph-realizable constraint controlling all those mixed terms was found. Also C'-H'=(C1-H1)(C2-H2) for series; that useful positivity identity alone does not control the parallel H defect, as the witness shows.

## Exact checks and remaining gap

`check.py`: all distinct state triples generated recursively through9 edges; counts1,2,4,8,16,34,71,158,359. Distinct U counts1,2,2,4,6,11,18,33,59 equal the actual publisher's list through9 edges. No U LC failure and no state-cone failure in this finite generated set. It checks H=f_n for30 successive parallel-edge states. No inference beyond these bounds.

`route.py`: exact artificial closure obstruction above and18 direct finite-field evaluations of paired tree/forest recursions at q=2,3,5, including a nested replacement. No floating point. The finite-field check uses numeric pair evaluation separate from the coefficient-polynomial implementation. It does not enumerate all source graphs or prove their all-degree inequality.

**Precise mathematical gap:** prove an all-depth invariant of the actual graph-realizable triples (or a direct mixed-defect inequality for U) preserved by both displayed bilinear operations and implying LC of C+TH. Pairwise synchronization plus individual LC and C>=H is insufficient for the chosen stronger state invariant. No complete ordinary proof/refutation exists here. Expanding the finite census would not supply that bridge.

## Freshness and scope

Fresh ordinary HTTP default HEAD reads on2026-10-29: Omega c80e3a31a64948bb3c8b407f9881aaf5b96d63b6; OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. The frozen complete root tree is at Omega1b999d9f / OpenAI7ef5c0cc. Live compare from both the supplied d2b0 baseline and the older frozen tree was retrieved; changed bodies are saved. No topic-specific filename hits in the baseline inventory. This is a bounded path and changed-body screen, not a semantic audit of all350k Omega files or a novelty clearance. No proof is nominated, so no acceptance or current-prior PASS is requested. Hashes and access failures are preserved. No403/429/challenge bypass or retry loop was attempted; the MathDB raw response included rendered content plus an unexecuted challenge script, and no challenge was executed.

**Strongest eligibility objection:** even a future successful transfer proof must be compared with classical series-parallel network strata and log-concavity preservation; the representation and finite checks are supporting helpers with credit0. Exact public Chen3.9 proof claims must remain excluded rather than recycled.

Coverage correction after the older-baseline fetch completed: that comparison spans97 commits and returns exactly300 files, the API file-list ceiling. Its file coverage may therefore be truncated. All300 returned bodies were saved and screened for the selected-family terms (no hits); this is not a body-by-body semantic proof audit, and missing changed files are not cleared. The shorter d2b0-to-c80 comparison returns7 commits/3 files. Neither filename nor term absence establishes novelty. The original publisher conjecture location above uses the PDF's internal page24, not journal page24.
