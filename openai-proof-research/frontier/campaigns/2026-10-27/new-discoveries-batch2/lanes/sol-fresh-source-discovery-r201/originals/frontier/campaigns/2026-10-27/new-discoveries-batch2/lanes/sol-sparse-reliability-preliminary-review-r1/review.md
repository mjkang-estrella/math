# Independent preliminary adversarial review

Recommendation: retain the full ordinary sparse-range proof. SOURCE: qualified
PASS. MATH: PASS at the ordinary-proof level. SUBSTANTIVE: qualified PASS for
continued consideration. NOVELTY: HOLD. FORMAL-FEASIBILITY: plausible but
uncertified. This is no acceptance, count, final review, Lean certificate, or
authorization for manuscript/formal investment. Root alone adjudicates.

## Source and precise claim

I independently read the actual Romero body: definitions and related-work
discussion, full Lemma 20, Theorem 22, Lemma 23, the intervening structural
analysis, full Lemma 27 and the following question, and concluding remarks and
references. The materially closest complete endpoint proofs are Lemmas 23 and
27 themselves; neither establishes domination at intermediate probabilities.
The 2018 Networks paper and the 2025 proceedings body were not obtained or read.
Their contents are not inferred from metadata or from Romero's descriptions.

The pinned primary at https://arxiv.org/pdf/2610.36120v1 was independently
retrieved at 2026-10-30T05:23:10.594606+00:00. Its 479729 bytes have SHA256
9c42ee867de8f1fc0b57e5e76b6f6b3b67b28c7f96303b2b3b18d2a02b0c27f3,
identical to the frozen candidate primary. The frozen abstract history gives
v1, 26 October 2026 18:27:37 UTC. The current arXiv title-query feed likewise
returns v1; this bounded query is not an all-version/all-history clearance.
Actual retrieval timestamps take precedence over the environment's earlier
calendar date. Exact URLs, response hashes and failures are in retrieval.jsonl.

Definition 1 quantifies over every two-terminal competitor of the fixed order
and size and every failure probability rho in [0,1]. The paper's graphs are
finite, simple and undirected, and isolated vertices are allowed. Its question
immediately after Lemma 27 is the sparse H question, not just a terminal-universal
subclass. The candidate covers all n>=5 and 5<=m<=2n-3 with path length at most
three, uniformly for rho. It makes no dense-range assertion.

Printed Definition 9 is defective. For odd m, indices 3 through (m-1)/2 give
(m-5)/2 common neighbors and m-4 edges. The candidate therefore cannot literally
prove membership or optimality of that printed object in T_(n,m). Lemma 23's
proof explicitly uses floor((m-1)/2) two-edge paths and, for even m, one extra
edge between common neighbors. Those graphs are exactly the candidate's explicit
m-edge H. Qualified SOURCE pass means the intended/existential optimization
question is resolved by that explicit graph; the defective definition must
always be disclosed. Repairing its index receives no discovery credit.

The source reports an invalid deletion step in its earlier induction. I checked
that warning directly rather than relying on it: deleting s-to-one-endpoint of
the interior edge in H_(8,10) gives R_3(1/2)=413/512; H_(8,9) gives 431/512.
This refutes the stated equality, not the conjecture. Lemma 27 also contains
printed arithmetic/sign inconsistencies: its displayed 2^(m/2-2) is smaller
than 3*2^(m/2-3), contrary to the comparison sentence. Its description of the
number of length-two paths in H' changes by one. The candidate needs neither
that classification proof nor its printed comparison. No endpoint theorem is
silently promoted to a global inequality.

Crossref's title lookup newly authenticates a metadata DOI match for the
predecessor: https://doi.org/10.1016/j.procs.2025.10.297, Romero, *Most reliable
two-terminal graphs with distance constraints*, Procedia Computer Science 273,
185–192, publication year 2025. The record was created 2025-11-25 and deposited
2025-12-19; these are metadata timestamps, not exact publication dates. This
supersedes the candidate's then-correct statement that no DOI had been
authenticated. It does not authenticate the unread body. No Elsevier or
ScienceDirect route was requested. A distinct Udelar repository search returned
403 and was stopped. Crossref's second query returned 429 and was stopped.

## Mathematics: universal bridges

I find no unresolved mathematical bridge in the ordinary proof. Here is my
independent derivation and the points on which the verdict depends.

1. If st is missing, identify the bit of any removed edge with the bit of the
new st. For every successful old configuration, either a successful path avoids
the removed edge and persists, or that edge is live and the new st is live.
This bijection preserves the independent equal-p product law. Strictness and
coefficientwise optimization are unnecessary.

2. Suppose x is adjacent to s but not t and xy is interior. A simple s-t path
of length at most three using xy must be s-x-y-t; its reverse interior
orientation would require xt. Replace xy by xt with the same bit. Whenever
the former path succeeds the two-edge path s-x-t succeeds. Successful paths
avoiding xy remain. Exchange terminals for the other single type. The added
edge was absent, so simplicity and edge count are preserved. Each move removes
one interior edge and creates a double vertex, so repetition terminates.

3. An empty vertex cannot be interior to any path of length <=3. Thus its
incident interior edges can be deleted. After the preceding moves no interior
edge remains incident to a single vertex. A single terminal edge is then on
no successful path and can be deleted too. The retained vertices really are
isolated, not merely ignored; they are available later. Deletions give unused
budget, not a claim that the current graph still has m edges. The resulting
graph has st, a double vertices, core F and 1+2a+e<=m.

4. Write p=1-rho and work first with 0<p<1. Failure of each independent
two-edge terminal path has probability q=1-p^2. Conditional on all such
failures the terminal-edge pairs remain independent, since their original
edge sets are disjoint. The S-only and T-only probabilities each equal
p(1-p)/q=p/(1+p)=u, and N has mass (1-p)/(1+p)=1-2u.
For a core edge, the only possible three-edge successes have opposite S/T
endpoints, in either orientation. Integrating its independent bit multiplies
failure by rho precisely in that case. Hence U=rho*q^a*Z(F), with no missing
path event or extra normalizing factor.

5. In order T<N<S the interaction matrix is
[[1,1,rho],[1,1,1],[rho,1,1]]. Its nine ordered 2x2 minors are nonnegative.
The association induction is valid: conditioning on the last site only
changes positive one-site weights. For last-site values z<z', TP2 makes the
ratio of conditional unnormalized weights an increasing positive product of
one-site functions. Inductive association implies E(hr)>=E(h)E(r), so the
normalized conditional laws are stochastically ordered. For f depending on
the last site, its pointwise increase plus that stochastic order makes its
conditional expectation increasing. Total covariance and the one-site identity
complete the induction for arbitrary increasing f,g. The ratio's normalizing
constant is handled by division by E(r). This needs neither independence of
the tilted sites nor a tree structure.

6. Conditional weights at x are u*rho^b, 1-2u, u*rho^c for S,N,T. If A=rho^b,
B=rho^c, then A+B<=2, and u(A+B)/(1-2u+u(A+B))<=2u. The division is legitimate
and the inequality follows by multiplication by the positive denominator.
The measure has simultaneous global S/T symmetry, giving equal unconditional
marginals and hence each <=u. It does NOT have invariance under independently
flipping a single site, nor equal conditional S/T probabilities. Association
of 1_(S_x) and -1_(T_y) gives P(S_x,T_y)<=P(S_x)P(T_y)<=u^2. The reversed event
is disjoint for distinct x,y, so their union has mass <=2u^2.

7. Crucially all these statements apply to the reduced graph F0 after any
k<=2 chosen edges have been removed. Under its normalized measure,
Z(F)/Z(F0)=E[product(1-p*I_opposite)]. Pointwise the product is >=1-p*sum I,
even when the removed edges share an endpoint. Consequently this ratio is
>=1-2k*p*u^2>=1-p^2: the last inequality follows from
p^2-4*p*u^2=p^2*(1-p)^2/(1+p)^2>=0. There is no substitution of mu_F for mu_F0.
An isolated new double vertex multiplies failure by q independently, so
replacing k interior edges and 2-k budget units by that vertex's two terminal
edges cannot increase failure. Normalization is positive throughout.

8. While e+t>=2 choose k=min(e,2). Budget suffices, a increases by one, and
2a+e+t=m-1 is preserved. Before a move, a+1<=(m-1)/2<=n-2; hence at least one
of the fixed n-2 nonterminals is isolated and available. At termination odd m
leaves e=t=0; even m leaves e+t=1. In the latter case either the sole core edge
remains or the last budget unit can be spent on a missing edge between two
double vertices. There are at least two such vertices since even m>=6. This
gives exactly the claimed H in both cases, with exactly m edges and n vertices.
At p=0 all reliabilities vanish; at p=1 H succeeds. No limiting denominator
argument at the endpoints is needed.

These are all-order arguments. They do not prove coefficientwise domination,
uniqueness, or dense-range optimization; those are not claimed.

## Independent diagnostics and candidate checker audit

I read both candidate exact checkers and their evidence. The subset-zeta checker
counts cardinality-indexed successful subgraphs using bounded BFS; its separate
direct path predicate allows walks but, at length <=3 with distinct terminals,
this is equivalent to a simple successful path. The integer state weights in
the correlation checker are consistent with the normalized model. Their stated
26,471 graphs and finite correlation totals remain diagnostics, not proof.
I did not merely rerun either script.

My runnable independent_check.py uses a three-status enumeration of every
possible edge on five vertices and a frontier BFS to test the survival-bit
couplings. Its core oracle enumerates the original 2a terminal-edge bits,
excludes successful two-edge paths, and integrates the interior failures with
integer weights before normalizing. This checks the conditional calculation
from the original experiment, rather than assuming the candidate's state
probabilities. Results in independent-evidence.json: 105,930 successful coupling
outcomes; 228 core/probability models through four core vertices at p=1/5,1/2,4/5;
2,460 ordered opposite-pair bounds; 1,581 deletion/replacement comparisons;
646,995 principal-upper-event association comparisons; 223,712 legal abstract
budget states for n<=40. The exact deletion countermodel is independently
recovered. Principal-upper-event checks are not a full association test for all
increasing functions. No finite result is used to infer an unbounded theorem.

## Substantive and classical-adaptation assessment

The strongest objection is that the entire proof is an application of classical
positive association plus elementary couplings and an edge budget. Its COMPLETE
applicable bridge is precisely steps 1–8 above: reduction to a three-state
ferromagnetic chain model; finite TP2 association; global symmetry plus bounded
occupancy; opposite-pair probability <=2u^2; the two-edge deletion ratio >=q;
and fixed-vertex budget induction. No general association theorem by itself
states the target graph optimum, and invoking FKG without the occupancy,
reduced-measure and budget steps would leave essential gaps.

I therefore do not recommend rejecting this as a mere definition correction,
endpoint repair, short proof, or immediate quoted corollary. The new content
under review is the uniform conversion of arbitrary cores into isolated
two-edge paths while preserving the available fixed-order budget. It resolves
an explicit all-probability optimization question, rather than supplying an
example or correcting a label. Classical ingredients and the index repair get
zero separate credit. SUBSTANTIVE qualified PASS is my recommendation for this
ordinary candidate, subject to root's eligibility judgment and the novelty hold.

Strongest countercase to my recommendation: a specialist may regard the full
eight-step bridge as routine once TP2 is recognized, or an unread proceedings
or classical reliability body may already give an equivalent valid replacement
argument. The source itself says an earlier induction attempted the same target.
The numerical failure of one deletion equality does not rule out another valid
proof in that predecessor. If a prior body supplies the full applicable
optimization bridge, campaign credit must be denied even though this proof is
correct. Conversely, familiarity of the ingredients alone does not demonstrate
that countercase. I found no complete externally published subsumer in the
bodies actually read, and make no claim to have ruled one out elsewhere.

## Novelty and formal feasibility

NOVELTY remains HOLD. The DOI metadata discovery narrows the missing-source
identity, but the 2025 body and the 2018 Networks body remain unread. Current
arXiv title coverage is explicitly bounded; it is not a current public-proof
registry body/head audit. The candidate's historical index is inherited,
bounded evidence, not an independently cleared all-history corpus. No parked
historical interval or merge-tree search was reopened. Denied GitHub,
ScienceDirect and Google challenge routes were not used, nor were alternate
transport, proxy, account or TLS workarounds. There were no browser actions,
MathDB edits, external messages, uploads or posts.

FORMAL-FEASIBILITY is favorable in principle only: all objects can be finite
graphs, finite product probabilities and rational inequalities over real p.
The main costs would be the path-preserving bijections, finite association
induction with changing one-site weights, normalization identities, and the
budget invariant. No analytical infinite-volume theorem is needed. None of
those Lean bridges is certified here. No Lean commands or manuscript work were
performed. No formal-investment gate is cleared by this review.

Scientific originals and their lane-local copies are bound by freeze-before.json
and verified again after final scientific writes in freeze-after.json.
Administrative NEXT/ledger/context are snapshots only, with no live mutable
scientific dependency. final-manifest.json explicitly excludes itself and
manifest-verification.json; a separate guarded verification checks the final
manifest and the original/copy freeze. Counts remain 9 additional / 39 total,
next 40. No shared file or git state was changed.
