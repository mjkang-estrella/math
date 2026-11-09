# Independent review of MathDB 349070

Decision: the exact ordinary inequality and the candidate's sum-of-squares identity are correct. Recommend EXCLUDE_FROM_NEW_RESULT_CREDIT: an authenticated public primary proof already appears in Guigues, arXiv:2605.05330v1, Appendix F, Lemma 1, equation (8), pp.18–19, published 6 May 2026. This precedes this October–November 2026 campaign and the author's r404 candidate. Separately, the complete substitution into the earlier weighted graph Laplacian identity makes the routine-corollary objection concrete. This is an independent review recommendation, not root acceptance or a ledger change. Credit remains zero; campaign remains 55/60 beyond39,94total. No dormant next-Sol brief is warranted.

## Literal statement and source fidelity

The complete copied record inputs/records/349070.jsonl quantifies over a connected simple graph on n vertices and every strictly positive real vector x. It asks for y^T(A+I)y <= ||y||_1, where y=x oslash ((A+I)x). The record's status is an historical open label, not evidence of present novelty. The cached source is Guigues, Concerning Iterative Graph Normalization and Maximum Weight Independent Sets, arXiv:2012.07764v1, dated 14 December 2020. Section 2, p.4 specifies simple undirected graphs, binary adjacency and zero diagonal, strict componentwise positivity, and Hadamard division. Definition 2.1, p.5, eq.(1), explicitly gives N_i(x)=x_i/(x_i+sum_j A_ij x_j) on (A+I)x>0. Conjecture 8.1, p.24, eq.(19), matches the literal target. There is no matrix inversion and no activation function in this endpoint.

Appendix Theorem 8.1, p.31 continuing p.32, is a conditional scalar-norm statement. Its equation (27) gives a two-step scalar increment bound. I read it as context, not as a proof of the conjecture. Its stronger strictness wording needs the equality qualification below. The page24 text itself distinguishes scalar norm convergence from convergence of the vector. Neither the present result nor this review claims general dynamical convergence.

Fresh original arXiv metadata lists only v1, submitted Mon 14 Dec 2020 17:59:48 UTC, and no journal-reference field was found. Thus no later version is listed there at retrieval; this does not certify that no journal or other delivery exists. Fresh followup metadata similarly lists only v1, Wed 6 May 2026 18:02:40 UTC. Both delivered PDFs identify themselves as those v1 versions. This is a bounded version comparison, not worldwide final-publication clearance.

## Independent full proof and adversarial algebra audit

Let V be any finite index set, let A be the adjacency matrix in the literal endpoint, and put B=A+I. Then B is symmetric, entrywise nonnegative, and B_ii=1. For every i put s_i=sum_{j in V} B_ij x_j. Since all summands are nonnegative and the diagonal summand is x_i, s_i>=x_i>0. All reciprocals, products of denominators, and divisions below are legitimate. Set y_i=x_i/s_i>0. In particular |y_i|=y_i, so ||y||_1=sum_i y_i.

Consider the finite ordered double sum

D = (1/2) sum_{i,j in V} B_ij x_i x_j (s_i^{-1}-s_j^{-1})^2.

Every coefficient and square is nonnegative, so D>=0. On expansion the first square term is

sum_{i,j} B_ij x_i x_j/s_i^2
 = sum_i (x_i/s_i^2)(sum_j B_ij x_j)
 = sum_i x_i/s_i.

The second square term has the same value: exchange the two finite indices and use B_ji=B_ij and commutativity of real multiplication. This step requires symmetry; entrywise nonnegativity alone would not justify it. The mixed term is

sum_{i,j} B_ij x_i x_j/(s_i s_j)
 = sum_i y_i (sum_j B_ij y_j)
 = y^T B y.

The outer factor 1/2 cancels the two equal square contributions and the expansion's coefficient 2 on the mixed term. Hence

||y||_1 - y^T B y = D >= 0.

This proves the author's exact identity and the exact quantified inequality, with no unproved ordinary bridge. The diagonal terms in D vanish; each off-diagonal undirected edge appears twice in the ordered sum. No positive-semidefiniteness of B is assumed or needed: it is the associated Laplacian that is positive semidefinite. Connectedness and the off-diagonal binary restriction are not needed for this proof, but are retained in the target. I found no counterexample mechanism or hidden denominator, factor-of-two, norm, or transpose gap. All reasoning here is ordinary symbolic reasoning personally; no mathematical program was run.

If V is empty, there are no individual divisions, and both sums, the quadratic form and the norm are zero. Some definitions exclude the empty graph from connected graphs; either convention is harmless, and this extension is not additional credit. For a singleton, B=[1], s=x>0, y=1, and both sides equal1.

For a nonempty connected graph, D=0 iff s is constant. Indeed, every edge coefficient x_i x_j is positive, so a zero finite sum forces 1/s_i=1/s_j on each edge, hence s_i=s_j. Paths propagate equality to all vertices. Conversely constant s annihilates every square. If s=c 1, then By=B(x/c)=1, so N(y)=y. Conversely N(y)=y and y>0 give By=1, hence the deficit is zero, recovering constant s by the previous implication. Thus equality means that the FIRST NORMALIZED vector y is fixed, not that the initial x is fixed. On disconnected graphs the same argument works separately on each connected component, including isolated vertices.

For completeness of the source audit only, write t=By>0 and z=N(y). Direct algebra gives

sum_i(z_i-y_i) = sum_i y_i(1-t_i)/t_i
 = D + sum_i y_i(1-t_i)^2/t_i.

This uses (1-t)/t=(1-t)+(1-t)^2/t. It identifies the equality condition in the two-step increment as y fixed. The singleton with initial x=2 has y=z=1 although x is not fixed; thus the source's strictness sentence about the initial point is too strong. Also an arbitrary initial scale prevents an asserted increase starting at x itself. These observations are audit qualifications only, not new endpoints, credit, or a convergence claim.

## Actual earlier primary identity and COMPLETE bridge

The authenticated body sources/chung-lectures.pdf is Fan R. K. Chung, Lectures on Spectral Graph Theory, Chapter1. Read pp.3–4 (eq.(1.1), the unordered-edge convention), pp.11–13 (Section1.4, weighted graphs, weighted operator, eq.(1.13)). The body explicitly permits loops and any symmetric nonnegative real weight w(u,v); its degree counts a loop once: d_v=sum_u w(u,v). Its unnormalized operator is L=T-W with diagonal d_v-w(v,v), and (Lf)(u)=sum_v w(u,v)(f(u)-f(v)). Pairing that operator with f, symmetry gives the Dirichlet identity for EVERY real f on the finite vertex set:

f^T L f = sum_{unordered off-diagonal edges {i,j}} w(i,j)(f_i-f_j)^2
 = (1/2)sum_{i,j} w(i,j)(f_i-f_j)^2 >=0.

This is the operator/energy identity underlying the displayed variational formulas, not an application of the infimum in (1.13) to an inadmissible function. The constraint sum_i d_i f_i=0 in that variational characterization is NOT a hypothesis of the energy identity. Expanding the operator or pairing (i,j) with (j,i) proves this distinction directly. A loop contributes zero to the energy and cancels between T and W; there is no missing doubled-loop convention.

Here is the full application, uniformly for every literal A and every strictly positive x:

* Take the same finite V; define W_ij=w(i,j)=B_ij x_i x_j. It is real, symmetric and nonnegative. Its positive off-diagonal edges are precisely those of A, and its loop weights are x_i^2. Thus it is exactly an allowed weighted undirected graph with loops. If the target graph is connected, this weighted graph has connected off-diagonal support as well.
* Its degrees are d_i=sum_j W_ij=x_i sum_j B_ij x_j=x_i s_i>0. Thus T and any T^{-1/2} used in Chung's normalized formulation are defined. There are no isolated zero-degree vertices, even for a singleton.
* Take f_i=1/s_i, a legitimate real function since s_i>0. If a normalized vector is desired, take g=T^{1/2} f, so g^T(T^{-1/2}LT^{-1/2})g=f^T L f. For a nonempty set g is nonzero, so the ordinary Rayleigh denominator is positive. No spectral gap, mean-zero, regularity, integrality, stochasticity or eigenvector assertion is needed.
* Compute sum_i d_i f_i^2=sum_i x_i s_i/s_i^2=sum_i y_i=||y||_1. Compute sum_{i,j}W_ij f_i f_j=sum_{i,j}B_ij y_i y_j=y^T B y. Therefore f^T(T-W)f is EXACTLY the target deficit. The nonnegative weighted Dirichlet energy proves the target, with precisely the candidate's ordered double sum and factor1/2. Empty V is handled directly without a Rayleigh quotient.

The specialization requires only this explicit weight/function substitution and cancellation of row sums; there is no extra combinatorial or analytic lemma. This supplies an affirmative routine-corollary objection based on content, not on proof length or the mere presence of standard tools.

Chronology qualification: this is the primary author's book text hosted by CMU, not a secondary explanation. The CMU URL is in an F-07 course directory; the PDF metadata says created2001/modified2002. The work is bibliographically the 1997 AMS book; the live author's revision page reports older publication and a revision beginning2006, but its claim of a 1992 first edition conflicts with common 1997 bibliography. I do NOT silently repair that discrepancy, claim an authenticated scan of a specific first printing, or treat PDF metadata as immutable timestamp proof. The mathematical body and bridge are authenticated; exact edition archaeology is bounded. None of this weakens the separate, dated May2026 exact-public-proof exclusion below.

## Decisive exact public counterpart and chronology

Guigues, Graph Normalization: Fast Binarizing Dynamics for Differentiable MWIS, arXiv:2605.05330v1, Appendix F, Lemma1, eq.(8), pp.18–19, states a generalized inequality for any symmetric entrywise nonnegative matrix S with unit diagonal, positive v, and a positive image y_i=v_i z_i/(Sz)_i. Its proof groups the deficit into nonnegative edge squares. This is an actual primary theorem AND proof, not a search snippet or an inference from the abstract's convergence claims.

Complete specialization: for each literal graph and positive x, choose S=B=A+I, v_i=1 for every i, and z=x. Symmetry, nonnegativity, unit diagonal, strict positivity and all denominators follow as in the independent proof above; its y is exactly our y. Its conclusion becomes y^T B y<=sum_i y_i=||y||_1. There is no gamma>1 restriction on the independently stated matrix lemma, even though some surrounding algorithmic theorems use regularization. For the empty convention the endpoint is the trivial empty sum; this adds no substantive content to the already public nonempty theorem.

With d_i=(Sz)_i=s_i, its edge-square coefficient specializes to B_ij y_i y_j/(s_i s_j) times (s_j-s_i)^2. Substitution y_i=x_i/s_i makes this B_ij x_i x_j(1/s_i-1/s_j)^2, summed once over edges. That is the same identity as the candidate's half ordered sum. Its equality condition also concerns the output being fixed. Its proof is self-contained for this lemma; I do not endorse the broader convergence or binarization claims elsewhere in that paper.

Fresh primary metadata authenticates v1 submission 6 May2026 18:02:40 UTC; the PDF header agrees. This is later than the 2020 conjecture, but earlier than the 2026-10-27/31 campaign and this November review. Thus it is not a later independent counterpart to this campaign's work. It is already a public resolution in the target's exact scope. No claim about all other literature is required for that negative novelty conclusion.

## Strongest contrary significance case and disposition

The best case FOR the candidate is that the exact statement was a named main conjecture for a concrete normalization method; recognizing the right dependent weights W and reciprocal neighborhood function f is meaningful insight, and the transparent certificate explains positivity and equality beyond a bare citation. A short proof by standard tools can resolve a substantial open problem. An old general identity by itself does not prove that this exact application was already noticed. I have therefore not excluded it merely for being easy, short, or Dirichlet-based.

Nevertheless, after paying the full bridge, no additional mathematical assertion remains beyond a direct energy substitution; that supports a routine-corollary significance objection under this campaign's rules. More decisively, the precise application and same square decomposition have already been published by the conjecture's author in May2026. Even a generous significance assessment cannot turn its independent rediscovery into a new result under the explicit exclusions. Recommendation is exclusion, not a fabricated universal novelty veto or a HOLD for an unread matching claim: the matching lemma and proof WERE read. The copied cited approximation/normalization works (Kako et al., Sinkhorn–Knopp, Knight, etc.) were not acquired/read in full; I make no clearance claims for them. Those bounded unknowns are not needed to manufacture this exclusion.

## Gates and process limits

Source fidelity PASS in the strict-positive, unactivated literal scope. Ordinary mathematics PASS independently, equality qualification recorded. Prior gate EXACT_PUBLIC_PROOF_FOUND, with earlier identity bridge separately authenticated. Novelty FAIL for campaign credit. Significance ROUTINE_SUBSTITUTION_OBJECTION_SUPPORTED, strongest contrary case addressed; no assertion that the public work itself is insignificant. Formal gate NOT_EXECUTED/NOT_REVIEWED. Independent ordinary review COMPLETE. Acceptance NOT_AUTHORIZED/NOT_PERFORMED. No dispatch, child, mathematical program, compiler, Lean, solver, git operation, message, publication, or credit action occurred.

Only own-lane copied inputs were read for author material. The 200 author references were hash-only via the explicit standalone frozen verifiers; no protected active lane or historical formal body was opened. The first bootstrap and before receipts were preserved. The supplied runner/writer/GET guard were used unchanged. See inventories.json for exact read depth, search/access limitations and resource caveats; source-map.json for concrete anchors and hashes; MANIFEST.json and its terminal exclusions for completed receipts; frozen-after.json for the final234-binding check. This report does not claim universal enforcement or full literature coverage.
