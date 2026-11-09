# r94 — symmetric entropy after Gaussian smoothing: unresolved

29 October 2026. No source resolution, nomination, Lean, paper, or credit. Work solo; only this lane written. The shared tally remains 8 additional / 38 total. Active MMPP and finite/arithmetic r93 are untouched.

## Early screening and source scope

Before mathematical investment, context.py inventoried 5,545 all-date report/ledger files under openai-proof-research, including every name containing SUMMARY, discovery, FINDINGS, PROOF, review, or ledger, case-insensitively. The exact author/title/id screen found three hits, all concerning Lamkin–Tkocz or a reference to it. Inventory and hits are retained. This is project duplicate coverage, not a literature priority certificate. Ancestor/batch AGENTS, ledger, NEXT, prior-campaign-context, upstream identity and manuscript catalogue were read; their byte hashes are in context.json. r91/r92 summaries and current root freeze registry context were also read. No old hold is silently cleared.

Four exact attributed claims were screened:

1. Ball–Nayar–Tkocz, arXiv:1509.05926, Conjecture 1, PDF p3: for every symmetric log-concave random vector, exponentiated differential entropy of one-dimensional projections is a norm. Equivalent planar assertion: exp h(X+Y) <= exp h(X)+exp h(Y), allowing dependence. Not selected: substantially broader geometric assertion; neither the classical Ball section-norm bound nor the source's Proposition 1 removes the factor e. This is distinct from the independent two-copy question.
2. Same paper, Conjecture 2, PDF p6: for every iid log-concave real pair, h(sqrt(t)X+sqrt(1-t)Y) is concave on [0,1]. EXCLUDE PUBLIC REFUTATION. Luo arXiv:2609.11418v2 (14 September 2026), Theorems 1.1 and 1.2, supplies asymmetric and symmetric counterexamples respectively. The actual latest PDF is v2, despite search snippets describing only v1's asymmetric result. Its symmetric theorem already covers every signal fraction q>4/7. No rediscovery of that interval.
3. Lamkin–Tkocz, arXiv:2001.06439, Conjecture 1, PDF p2: all iid nonnegative laws and real p>1 have log-convex moments of sample averages. EXCLUDE DUPLICATE AND PUBLIC PROOF. r44 already records Gonçalves–Madrid–Ramos arXiv:2608.00813v1 (1 August 2026), Theorem 1, Corollaries 2–3. Their product convex order for block partitions (n,n) majorized by (n+1,n-1), tested with z^p, gives exactly b_n^2<=b_(n-1)b_(n+1). Original Remark 6 explains why classical joint convexity alone fails; the successor's actual averaging construction/application body was read.
4. SELECTED: Luo v2, Section 10, Problem 10.1, PDF p15: classify all q in (0,4/7] such that Gaussian smoothing with signal variance fraction q gives a concave two-copy weighted entropy curve for **every symmetric log-concave density of variance one**. Let S_q f be the density of sqrt(q)X+sqrt(1-q)G, with independent standard Gaussian G. The curve is F_(S_q f)(t)=h(sqrt(t)X_q+sqrt(1-t)Y_q), with iid smoothed copies. No q or input instance is promoted as a full solution. The q=0 trivial Gaussian case is outside this source interval.

## Actual nearest proof bodies and chronology

The original BNT Conjectures 1–2 and Proposition 1 proof were read from the downloaded PDF. Its Ball/Busemann section-norm mechanism bounds reciprocal density maxima, while entropy/max-density comparison loses e; it does not prove the sharp entropy norm claim.

Eskenazis–Gavalakis, actual author PDF of *On the entropy and information of Gaussian mixtures*, Section 2, Theorem 2 proof, formulas (20)–(24), establishes concavity using the entropy variational principle, Gaussian variance mixing, and concavity of -log g(sqrt(x)). That mechanism applies to variance mixtures and does not cover all symmetric log-concave densities. The nonlinear Gaussian-mixture representation is indispensable to its Jensen step.

Luo's actual v2 Theorems 1.1–1.2, Section 10 and Appendix F proof were read. Theorem F.1 proves an interpolation bound exactly when s<=sqrt(2r(1+r))-r; at r=q/2,s=q this is q<=4/7. Corollary F.2 blocks the existing small-Lebesgue-L2 perturbation dominance strategy in this range. The Fock-space Gaussian kernel comparison controls term sizes, not entropy curvature. Accordingly it cannot be promoted to a positive solution of Problem 10.1. The source explicitly distinguishes these tasks. Latest public abstract HTML confirms v1 10 September / v2 14 September 2026. Searches for Luo + 4/7, exact arXiv id and Problem 10.1 did not locate a later solution; this is bounded coverage only.

## Mathematical work beyond screening

Use probabilists' Hermite polynomials H_n and standard Gaussian density phi. Consider

    f_a(x)=phi(x) r_a(x),  r_a=1+a H_4(x),  0<a<=1/222.

This is an even, strictly positive probability density of mean zero and variance one, by Hermite orthogonality. Positivity follows from H_4=(x^2-3)^2-6. It is globally strongly log-concave, not just sampled as such: r_a''=12a(x^2-1), and

    r_a-24a x^2 = a(x^2-15)^2+1-222a >=0.

Therefore (log f_a)''=-1+r_a''/r_a-(r_a'/r_a)^2 <= -1+12a x^2/r_a <= -1/2.

This family is outside the known Gaussian variance-mixture mechanism. If f_a were the law sqrt(V)G, its even moment ratios would force

    E V^j = 1+4j(j-1)a, j=0,1,2,3,4.

Consequently E(V-1)^4=0 but Var(V)=8a>0, impossible. Thus the known positive theorem does not directly settle even this test family.

Gaussian smoothing and conditional Hermite identities give the **exact** convolution density ratio, with b=a q^2,

    R_t=1+b A(t)H_4+b^2 B(t)H_8,
    A=t^2+(1-t)^2,  B=t^2(1-t)^2.

All ratios represent genuine convolution densities and have variance one. Since Gaussian cross-entropy is fixed,

    F(t)=h(G)-integral phi R_t log R_t,
    F''(t)=-integral phi [R_t'' log R_t+(R_t')^2/R_t].

For each fixed admissible positive a, differentiation is justified by Gaussian tails, polynomial bounds, and a uniform positive lower bound on R_t from the input ratio r_a>=1-6a. At t=1/2, R_t'=0 and

    R_1/2=1+(b/2)H_4+(b^2/16)H_8,
    R_1/2''=4b H_4-b^2 H_8.

The second-order expansion about a=0 has curvature

    F''(t)=-192 a^2 q^4(3t^2-3t+1)+o(a^2),

for fixed q,t. This coefficient is strictly negative for every q>0 and t in [0,1]. It makes this elementary near-Gaussian construction a poor counterexample route. There is no uniform remainder theorem here.

More generally, the quadratic entropy term for a finite, mean/variance-preserving even Hermite perturbation sum_(m>=2) c_(2m) H_(2m) is

    -(a^2/2) sum_(m>=2) (2m)! c_(2m)^2 q^(2m)
                         [t^m+(1-t)^m]^2.

Each squared bracket has nonnegative second derivative: 2[(A')^2+A A''], with A>=0 and A''>=0. Thus this linearized strategy has the concave sign mode by mode, for every q. Higher-order perturbation effects, and perturbations whose degree grows as amplitude shrinks, are exactly what this argument fails to control. The existing public high-degree counterexamples illustrate why a fixed-mode expansion is insufficient.

## Bounded checks, objection, and remaining gap

Run `bash run.sh` from this lane. Every Python helper is invoked through the exact improved packet/helper_guard.py specified by the assignment: AS/group RSS 512 MiB, CPU210, wall230, nominal40ms, BLAS1. No raises. Offline checks use no network. Symbolic checks verify 15 actual conditional Hermite polynomial identities at rational orthogonal rotations, the global curvature certificate, and 19 square-derivative identities; quadrature uses 96 and 192 Gaussian nodes on 2,600 parameter triples per resolution. Of those, 1,820 per resolution have q<=4/7; the rest are controls in the already-refuted general-source interval. All tested curvatures are negative. These are unvalidated floating quadratures, not interval certificates, and are not a proof of any full source claim. Earlier combinatorial generating-coefficient checks in check.py are only sanity checks; exact.py carries the nontrivial polynomial identities.

**Strongest objection/falsifier:** the selected question quantifies over every symmetric log-concave density. A quartic Hermite family and fixed-degree second variation cannot settle it, even if the family were proved concave for all a,q,t. A single admissible symmetric f and q<=4/7 with F''(t)>0, or a strict three-weight Jensen reversal, would refute a proposed positive q guarantee. No such witness has been found here. Conversely, positive resolution requires a uniform nonlinear estimate for the displayed entropy Hessian (or another method) across the entire source class. Even the sign of the exact quartic-family integral for all admissible a,q,t remains unproved in this lane. These are explicit mathematical gaps, not novelty or source-label gaps.

## Public registry coverage and holds

Current public `commits/HEAD`, not stale main: Omega d2b0ee6e958cf646530d3476088494e349570b46; OpenAI 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a, fetched 29 October around19:15 UTC. This advances beyond the assigned 19:01 Omega2130 baseline. Baseline complete trees have 350,197 /174,524 entries. Omega base-to-head comparison reports90 commits but only300 changed files: coverage is incomplete. A latest recursive API tree was genuinely truncated (55,878 paths); it is explicitly NOT a complete current tree. The first parser expected formatted JSON and failed; saved bytes were subsequently parsed offline, with no HTTP retry. Current pinned bodies of the two closest lexical hits were read: Hirche binary Rényi combining and trace-class quantum entropy concavity. Neither is this continuous weighted-sum question. No semantic all-body or full new-delta clearance is claimed. This coverage hold survives. No source acceptance or full novelty PASS follows from these screens.

Exact fetched source bytes, API bytes, failed URLs and hashes are retained. CMU aliases returned404; alternate primary arXiv PDFs succeeded. No403/429/challenge bypass, browser, account, messaging, posting or upload occurred. PROOF.md is intentionally absent because no full ordinary source proof/refutation was obtained.
