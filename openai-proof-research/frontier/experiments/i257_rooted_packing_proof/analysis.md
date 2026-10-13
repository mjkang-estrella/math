# I257 independent mathematical proof gate

Date: 2026-10-12. **Verdict: PASS for mathematical correctness**, including the bounded-component application under its stated hypotheses. There is no required mathematical repair. The additional details below reconstruct abbreviated arguments in the submitted proof; they do not change its theorem or require an author revision. No contribution, substantiality, priority, prominence, or acceptance verdict is given.

Reviewed input: `frontier/experiments/i248_combinatorial_structure_discovery/analytic-attempt.md`, all 167 lines, SHA256 `47a0fa44fdc57a1c2009da17f14a6dab8aa6d05fec63d49e55f013d49487886b`. This is the exact unchanged candidate specified by the user. The final report, original discovery brief, failure record, input authentication, and source literature record were also read in full. This is an independent I257 reconstruction; I254's unfinished files were neither read nor overwritten, and its provisional conclusions supply no evidence here.

All pinned OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. Reading their statements and arguments below identifies contracts and comparisons, not an upstream truth audit. The target remains twenty substantial findings and the accepted count remains ten. Requested execution: GPT-6.1 Sol/high/Standard, directly in this restarted session; no subordinate or delegated task and no service-tier change was initiated.

## 1. Exact statement, scope, and typical classes

Fix an integer d≥2. For all sufficiently large n depending only on d, let 1≤s≤10 log n be an integer, let 0<r<1, and assume r^b≥n^(−1/100), where b=ds+binom(d,2). Put L=64d, τ=1−(1−r)^2, and p=1−(1−r)^(2L). The classes D and E depend on n,r,s,d. Their probability errors have one bound depending only on n,d, tending to zero. This is uniformity over parameter choices, not one class or one simultaneous event for the continuum of all r.

For every G∈D, H∈E, root set Y⊆[n] with |Y|≤n^(2/3), and rooted pattern family R, set N=n−|Y| and a=floor(N/(16d²)). A pattern is (A_1,…,A_d,F), with A_i⊆Y, |A_i|≤s, and F a simple graph on labelled slots [d]. A compatible unordered d-subset of [n]−Y has a realizing slot order satisfying those edge-presence requirements. The packing rank counts disjoint nonroot subsets, with no limitation on reuse of roots. Then

    ν_R(H;Y) ≥ min{2d ν_R(G;Y), a}.

R is a family of types from a finite universe. Duplicate types can be discarded without affecting rank; repeated root neighborhoods across slots or across different patterns are allowed. No root-root edge, nonedge constraint, or nonroot candidate list is part of a pattern. No hypothesis fixes R before G or H is observed. Sections 8–9 below verify this adaptive quantifier and the Cartesian product D×E rather than a coupled-host claim.

## 2. Bernoulli compression on the correct coordinate space

For fixed Y use

    Ω_Y = ([d]×Y) ⊔ binom([d],2).

The ordered incidence (i,y) represents the edge between the vertex in slot i and root y. Even if several A_i contain the same root, their coordinates are distinct because the nonroot vertices are distinct. The internal coordinates represent the unordered slot pairs. All these physical graph edges are distinct for any injective realizing tuple. A support T corresponding to a pattern has |T|≤b. This is the domain needed for product Bernoulli compression; treating roots themselves as the coordinates would have been incorrect.

Close R under the action of S_d on Ω_Y. This changes no unordered compatibility event. For Z distributed as an independent Bernoulli-r subset of Ω_Y, start with Q_0 empty and add a support T∈R whenever

    P(Z contains some member of Q_0 | T⊆Z) < 1/2.

The event T⊆Z has positive probability r^|T|, including probability one for T empty. The increment in the probability of satisfying Q_0 is strictly greater than r^|T|/2≥r^b/2. The process therefore makes fewer than 2r^(−b) additions; an already added support cannot be added again. For a nonempty original family at least one is added. At termination the conditional probability is at least 1/2 for every original support. The conditional law is exactly T∪Z with a fresh independent Bernoulli sample: coordinates in T are forced and every other coordinate retains its original product law. Consequently, for every S containing an original support,

    P(S∪Z satisfies Q_0) ≥ 1/2.

This follows from monotonicity, not independence between original patterns. Empty supports, nested supports, and duplicate root requirements cause no exception. The pinned `lem:compression` excludes empty supports; the candidate explicitly proves this extension rather than silently citing an inapplicable hypothesis.

Close Q_0 under S_d to obtain Q. It has at most

    M = d! ceil(2r^(−b))

members, all from the closed R, and its satisfaction event contains that of Q_0. The bound 1/2 persists. Q need not lie in the unclosed written list of original patterns, but its members are permutations of such patterns, so every Q-compatible unordered block is R-compatible. This is precisely the subordination needed at the end.

## 3. Weighted maximum packing and expectation directions

For an unordered d-set U outside Y, transport its local present edges in G to Ω_Y using any slot order. Define w_Q(U;G) as its probability of Q-compatibility after independent Bernoulli-r addition on those local edges. Because Q is permutation closed and the product law is invariant under slot permutations, the value does not depend on the chosen order. It lies in [0,1]. It depends only on root edges incident to U and edges inside U, not on root-root edges or edges from U to other nonroots.

Let W_Q(G;Y) maximize the sum of these weights over all vertex-disjoint d-sets, including the empty packing. Finiteness ensures a maximum exists. Every block of an R-packing in G has weight at least 1/2 by Section 2, hence

    ν_R(G;Y) ≤ 2W_Q(G;Y).                         (A)

Let μ_Q=E ν_Q(K;Y) for K∼G(n,τ). If G,G' are independent G(n,r) graphs, G∪G' has exactly this law. Conditional on G, a fixed packing P satisfies

    ∑_{U∈P} w_Q(U;G)
      = E[∑_{U∈P} 1{U Q-compatible in G∪G'} | G]
      ≤ E[ν_Q(G∪G';Y) | G].

Linearity gives the equality. It requires no independence between compatibility events; global G' is the correct addition law. The right side does not depend on P, so taking the maximum on the left is valid, even when the maximizing packing is selected from G. Averaging gives

    E W_Q(G(n,r);Y) ≤ μ_Q.                        (B)

This is max of conditional expectations ≤ conditional expectation of a maximum. Reversing this inequality would invalidate the source control; the submission uses the correct direction.

For every nonempty Q, fix one of its patterns with e≤b requirements, partition floor(N/d) nonroots into fixed disjoint d-blocks, and impose its fixed ordering on each block. Each realizes the pattern at density τ with probability τ^e≥r^b. Their compatible subcollection is a packing for each outcome, so expectation and linearity yield

    μ_Q ≥ floor(N/d) r^b.

For sufficiently large n, N≥n/2 and N≥2d, hence

    μ_Q ≥ n^(99/100)/(4d).                        (C)

No-edge patterns have realization probability one and satisfy this bound. This lower bound applies to every nonempty test Q, not only families arising from one particular compression procedure.

## 4. Vertex-block Lipschitz assertion and concentration

Order the N nonroots. For each nonroot v expose one coordinate block consisting of all edges from v into Y and all edges vw with v earlier than w among the nonroots. These blocks partition the relevant independent graph-edge variables. Edges within Y can be omitted since neither functional uses them. The same decomposition works at density r or τ.

If a coordinate block at v is resampled, a candidate d-set U not containing v is unchanged: a root edge vy could matter only if v were a slot image, and a changed internal edge vw could matter only if both v and w were in U. In any vertex-disjoint packing at most one set contains v. Delete that set from an optimum before resampling; its loss is at most one and every remaining term is unchanged. This proves the one-sided difference ≤1. Delete from an optimum after resampling to obtain the other direction. Thus both ordinary ν_Q and maximum weighted W_Q have block oscillation ≤1. Shared roots, overlapping candidate blocks, and dependence between their indicators do not alter this deletion argument.

The product-block Doob martingale has conditional increment range length at most one. Indeed, two choices of the exposed block can use identical independent future blocks in their completions, and the functional differs by at most one in each coupled outcome. For a mean-zero increment with conditional range length one, the conditional Hoeffding bound gives E(exp(λΔ) | past)≤exp(λ²/8). Iterating over N blocks and optimizing the exponential Markov bound at λ=4t/N gives each one-sided bound

    P(Z−EZ≥t), P(Z−EZ≤−t) ≤ exp(−2t²/N).

The two-sided bound follows by addition. With (B), source-test failure is bounded by

    P(W_Q>9μ_Q/8) ≤ exp(−μ_Q²/(32N)).             (D)

At density τ the size-test failure is

    P(ν_Q<μ_Q/2) ≤ exp(−μ_Q²/(2N)).               (E)

These statements use independent coordinate blocks, not independent hyperedge indicators and not an unjustified one-edge Lipschitz count over n² variables.

## 5. Uniform count of compressed tests

Choose Y in at most (floor(n^(2/3))+1)n^(n^(2/3)) ways. For a fixed Y, the labelled pattern universe has size

    P_Y = 2^binom(d,2) (∑_{j=0}^s binom(|Y|,j))^d,

with binomial coefficients zero when j>|Y|. Since ∑_{j=0}^s binom(|Y|,j)≤(s+1)n^s, this is valid also when Y is empty or s>|Y|. It follows that log P_Y≤C_d(log n)² in the permitted s-range. Since r^(−b)≤n^(1/100), M≤3d! n^(1/100). Families of at most M patterns number at most (M+1)P_Y^M, with harmless overcounting if M>P_Y. Thus all nonempty tests (Y,Q) have total number T obeying

    log T ≤ K_d[n^(2/3)log n + n^(1/100)(log n)²] =: A_d(n).

We can count all families of this size, not just closed families. In D and E it suffices to require all nonempty permutation-closed such families. Overcounting only enlarges the error bound. A family produced by Section 2 is always among the tests, even when selected after observing either host.

Define D by W_Q(G;Y)≤9μ_Q/8 for every such test. Using (C), (D), and N≤n,

    P(G(n,r)∉D) ≤ exp(A_d(n)−n^(98/100)/(512d²)).

For every G∈D and compressed Q from any nonempty R, (A) gives

    ν_R(G;Y) ≤ 9μ_Q/4.                           (F)

## 6. Conditional exchangeability, trimming, and the filtration

Fix one deterministic test (Y,Q) for this section. Draw L independent graphs H_i∼G(n,τ). In each choose uniformly among all maximum Q-packings, independently across layers conditional on the hosts. Write K_i for the cardinality. Under every permutation of [n]−Y fixing Y, the host law is invariant, the compatibility hypergraph transforms equivariantly, the set of optima transforms bijectively, and uniform selection on that set transforms equivariantly. Therefore the joint law of (H_i, chosen packing) is invariant. Conditional only on K_i=k, the selected packing has an invariant law on k-edge d-uniform matchings. The permutation group acts transitively on this finite set; invariance forces the law to be uniform on it.

This uniformity is after averaging over the host. It is not uniformity conditional on a particular host; most abstract matchings may be incompatible in that host. Nothing below conditions on a fixed host or on the final class E.

Let S_i={K_i≥μ_Q/2} and S=∩_{i=1}^L S_i. Equation (E) gives

    P(S^c) ≤ L exp(−μ_Q²/(2N)).

The layer objects and auxiliary randomness are independent. S_i depends on layer i alone. For product events, conditioning on S preserves the product law: the conditional probability of ∩A_i is the product of P(A_i | S_i). No conditioning on a joint union-host event is used.

Put q=floor(min{μ_Q/2,a}). It is deterministic for the fixed test and at most a≤N/d. On S_i, trim the chosen optimum uniformly to q of its edges using independent randomness. Conditional on K_i=k, the trimmed law is invariant on all q-matchings and thus uniform, independent of k. Mixing over k subject to S_i remains uniform. Therefore under S the trimmed matchings P_1,…,P_L are independent uniform q-edge d-matchings.

Use the filtration generated by previously processed trimmed matchings and their retained subpackings, under this conditioned product law. Tie orders for retention can be chosen by a deterministic rule on finite labelled matchings. At step i, if the accumulated packing has already reached a, no further success condition is required. Otherwise its occupied vertex set B is measurable in the past and

    |B|≤d(a−1)<N/(16d).

Conditioned on that past, P_i remains uniform on q-matchings. It is not chosen after learning B. All edges of P_i avoiding the pre-round B are mutually disjoint, so retaining them introduces no within-round conflicts. Retain only as many as needed if the cap would be reached. This makes the claimed stopping rule precise.

## 7. Permutation martingale and all floor/cap cases

Generate a uniform q-matching by a uniform permutation π of the N nonroots, grouping its first dq positions into q blocks of size d and forgetting their orders. Every unordered q-matching has the same number q!(d!)^q(N−dq)! of generating permutations. A fixed positional block is a uniform d-set, so it hits B with probability at most d|B|/N≤1/16. If X_B is the number of blocks avoiding B, then E X_B≥15q/16. Independence between positional blocks is unnecessary.

Swapping any two entries of π changes at most two blocks' avoidance indicators, hence changes X_B by at most two. Expose π sequentially. Given a prefix, conditional completions for two choices x,y of the next entry are bijectively coupled by swapping x and y at the next position and the later position holding the other entry. The prefix is unchanged. The coupled final X_B values differ by at most two, so the corresponding conditional expectations differ by at most two. Each martingale increment consequently has conditional range length at most two, and in particular absolute value at most two.

For the weaker absolute-increment argument, |Δ|≤2 and conditional mean zero give E(exp(λΔ) | past)≤exp(2λ²). Iteration and exponential Markov optimization at λ=t/(4N) give exp(−t²/(8N)) for the lower tail. Thus with t=7q/16,

    P(X_B<q/2) ≤ exp(−49q²/(2048N))
                ≤ exp(−q²/(64N)).                 (G)

The conditional range bound gives a stronger constant, but is not needed. Inequality (G) holds for every permissible B, so it holds conditional on each random past; no union bound over vertex sets B and no assumption of uniform fixed-host optima is present.

Increase N_d so that μ_Q≥6, N≥32d², and a≥2, all uniformly in the parameters and tests. If μ_Q/2≤a, then q=floor(μ_Q/2)≥μ_Q/2−1≥μ_Q/3. If μ_Q/2>a, q=a. From N≥n/2 and the floor bound a≥N/(32d²), these cases imply

    q ≥ n^(99/100)/(64d²).                        (H)

In particular q grows and (G) has a uniform exponent of order n^(98/100). A round is successful if stopped already or if X_B≥q/2. Conditional union bounds give probability at most L exp(−q²/(64N)) for any unsuccessful processed round, conditional on S. In a successful round that does not reach the cap at least ceil(q/2)≥q/2 blocks are retained.

If the cap is reached, the accumulated packing has a edges. Otherwise after L rounds it has at least Lq/2. In the case μ_Q/2≤a,

    Lq/2 ≥ (32/3)d μ_Q > 8d μ_Q.

In the case μ_Q/2>a, q=a, and two successful rounds already retain at least 2ceil(a/2)≥a unless stopped sooner. Thus a no-cap outcome is impossible in this case. The boundary μ_Q/2=a is covered by the first case (and also has q=a). There is no rounding loss left in the conclusion

    ν_Q(∪_i H_i;Y) ≥ min{8d μ_Q,a}.               (I)

Every retained block belongs to some layer's compatible trimmed packing. The union preserves its required present edges. Nonedge requirements would break this implication, which is why they are excluded.

## 8. Deterministic E, exact density, Cartesian product, and adaptive R

For this fixed test, failure of (I) in the union host implies failure of the above witness procedure for every auxiliary choice. Therefore its marginal host failure probability is at most

    L exp(−μ_Q²/(2N)) + L exp(−q²/(64N)).

The argument does not infer a host property merely because auxiliary success has some probability conditional on that host. It uses the inclusion of host failure in witness failure. Different tests can be bounded separately in the same host distribution and then union-bounded; no simultaneous exchangeability claim after conditioning on all test successes is required.

Independent layers have union density

    1−(1−τ)^L = 1−(1−r)^(2L) = p.

Different physical edges remain independent in that union. Also p≤2Lr=128dr by the ordinary union bound, whether or not this upper bound exceeds one.

Define E to be the deterministic set of hosts satisfying (I) for every nonempty closed test (Y,Q). Using (C), (H), N≤n, and the test count,

    P(G(n,p)∉E)
      ≤ 2L exp(A_d(n)−n^(98/100)/(262144d^4)).

For both classes a common permissible error is

    ε_d(n) = min{1, (1+2L) exp(A_d(n)−c_d n^(98/100))},
    c_d = 1/(262144d^4).

This tends to zero because n^.98 dominates n^(2/3)log n and n^.01(log n)². All constants and all cutoffs depend only on d. These estimates make the submission's unspecified positive constants and uniform error explicit.

Now fix arbitrary G∈D, H∈E, Y, and nonempty R, in any order and with any dependence on those hosts. Select its compression Q. It is one of the enumerated tests and is subordinate to R as an unordered compatibility family. Equations (F) and (I) therefore imply

    ν_R(H;Y) ≥ ν_Q(H;Y)
               ≥ min{8d μ_Q,a}
               ≥ min{2d ν_R(G;Y),a},

since 2dν_R(G;Y)≤(9/2)dμ_Q<8dμ_Q. Empty R has rank zero in both hosts. No coupling between G and H appears: separate deterministic inequalities with the same fixed μ_Q prove the entire Cartesian product statement. Source and target choices of Y or R may be fully adaptive because every test was imposed beforehand.

## 9. Exact Aharoni–Haxell application

The external theorem contract used is the following: an indexed family L_1,…,L_t of d-uniform hypergraphs on the same finite vertex set admits disjoint representative edges e_i∈L_i if, for every nonempty I⊆[t],

    ν(∪_{i∈I}L_i) > d(|I|−1).

This is Theorem 2.6 in Ferber–Luh–Nguyen, arXiv:1606.05923v3, explicitly citing Aharoni–Haxell Corollary 1.2. The union matching can use several edges of the same L_i; it is not already a rainbow matching. Repeated identical L_i are allowed as indexed demands. Root labels are outside their common hypergraph vertex set. The theorem therefore imposes no disjointness condition on the roots. The original Aharoni–Haxell topological proof was not accessible and was not read; the complete FLN §2.4 argument and the exact reproduced theorem were read. The rank theorem in Sections 1–8 uses no Aharoni–Haxell input.

Let J⊆G have vertex set Y∪W, no edges within Y, |Y|≤n^(2/3), |W|≤n/(1000d³), root degree at most s at each nonroot, and all components of J[W] of size at most d. If W is empty the identity on Y suffices. Otherwise let there be t≤|W| components. Pad each to d nonroots with distinct isolated placeholders. The total padded nonroot count is dt≤d|W|≤n/(1000d²)<N for large n, so there are enough unused source vertices. Only dt−|W| new vertices are required. Required edges on all padded components are edges of J and hence of G; extra G-edges touching the placeholders do not matter because embedding is noninduced.

Let L_i be the d-uniform hypergraph on [n]−Y of blocks realizing component i's padded labelled pattern. For every nonempty I the disjoint padded source components form an R_I-packing of size |I|, even if their types repeat. Further, for sufficiently large n,

    a≥n/(64d²)≥2d|W|≥2d|I|,

where the middle inequality uses 2d|W|≤n/(500d²). Thus the rank comparison supplies

    ν(∪_{i∈I}L_i) = ν_{R_I}(H;Y)
                  ≥ 2d|I| > d(|I|−1).

All hypotheses of the exact criterion are met. Take a disjoint representative block for each component, choose its realizing slot order, and discard the placeholder images. The resulting map fixes Y, is injective on W, realizes each internal component edge and each root edge, and has no other edge obligation because no root-root edges or edges between distinct components of J[W] exist. Repeated types and overlapping A_i give no extra compatibility requirement. This is an application of the main theorem, not a second nomination.

## 10. Adversarial objections and their disposition

- **Unrestricted overlapping roots:** the coordinate space distinguishes slot incidences; Lipschitz deletion is indexed by nonroot vertices, and symmetry fixes Y. No probability step needs disjoint root neighborhoods, bounded root degrees, or independence of different candidate blocks. The threat does not expose a gap.
- **R chosen to exploit both hosts:** compression may depend on both hosts, but the resulting small Q lies in the finite pre-imposed test universe. Neither concentration nor exchangeability is invoked directly for this adaptively selected Q; the deterministic inequalities already hold for all Q. The threat does not expose a gap.
- **Uniformity asserted for a fixed host:** that assertion would be false. The actual proof averages over the exchangeable host and an invariant random optimum selection, then conditions only on cardinality/size. This is valid.
- **Conditioning on layer success or previous choices:** the success event factors by independent layers, and the sequential filtration exposes only past trimmed matchings. The next trimmed matching remains uniform and independent. Conditioning instead on the final host, final class E, or all adaptive pattern choices would be invalid, and is unnecessary.
- **Permutation dependence:** positional blocks are dependent, but the transposition coupling pays the martingale increment bound. No hypergeometric independence is claimed.
- **Large source ranks, isolated patterns, and floors:** the cap precludes impossible multiplicative growth of a full matching; (C), (H), and the two q-cases pay all floor losses. Empty families and zero-edge supports have been addressed explicitly.
- **Padding and colors:** fillers require no edges, fit in the source, and are discarded only after the disjoint representative theorem. Union rank is used with the exact strict threshold, not confused with a colored maximum rank.
- **Lists, nonedges, growing d, or larger component support:** not part of the claim. Lists can destroy nonroot symmetry; nonedges fail under union; changing fixed d or the support cap would require a new analysis. These limits do not weaken the theorem as stated.

No counterexample or unresolved correctness bridge remains for the exact candidate. The conclusion is PASS, with optional exposition improvements only: spell out the product conditioning, the prefix-preserving transposition coupling, the marginal host-failure inclusion, and the padding inequality as done here. These are supplied by the submitted argument's existing hypotheses. Substantiality remains wholly outside this gate.

## 11. Source comparison and read boundaries

The actual pinned graph-decomposition `main.tex` was retrieved at the immutable URL, authenticated against its Git blob in `sources/preprints-tree.json`, and read in full, all 841 lines. The retained two excerpts split it at line 488 and together reproduce that single primary manuscript. `lem:compression` has the nonempty support domain noted in Section 2; `prop:transfer` uses smoothed scalar neighborhood sums, tests all small root sets and compressed requirement families, and uses ordinary Hall on individual nonroots. `prop:degree-embedding` uses successive independent-set layers with fresh bin exposures; it is a separate embedding bound, not the simultaneous rooted-block rank theorem. The complete final assembly was read and keeps the different piece embeddings separate. No duplicate rank comparison appears in these operations. This is a bounded contract comparison, not a worldwide novelty conclusion.

The pinned integral/fractional companion `consequences.tex` was independently retrieved, authenticated, and read in full, all 50 lines, including `cor:two-unions` and its proof. That operation concerns a two-set cover budget, not disjoint rooted block ranks. Other pinned companion proofs referenced by I248's broader discovery history were not read in this gate because they are not logical inputs to the self-contained rank proof; no claim about all companions or all literature follows.

FLN v3 was independently retrieved and its PDF hash and extracted §2.4 bytes match I248's record. Read all of §§1–2.3, including Theorem 1.6, Definition 2.2, the whole Lemma 2.3 proof, and the stated Riordan input; read all of §2.4, including the full Lemmas 2.7 and 2.5 proofs and Theorem 2.6. Their architecture already embeds blocks via independent rounds and compatible-block hypergraphs, proves union matching bounds by Janson and residual-set tests, and invokes hypergraph Hall. Definition 2.2(v) separates components by distance at least three within each batch, yielding W_ij∩W_i'j'=∅ for i≠i'. In the δ_2 calculation that removes common root-incidence edges between different block indices. The submitted unrestricted-overlap theorem cannot merely import that calculation; its weighted-packing and exchangeable-layer argument supplies a different proof. This comparison makes no claim that the latter is substantial.

FLN §3 and its references were not systematically read; a failed extraction-boundary diagnostic displayed part of them, but none is a proof input or retained excerpt. The original Riordan proof was not read or used. The original Aharoni–Haxell PDF and download link redirected to the publisher abstract page; no original topological proof was obtained. The arXiv 2609.20864v2 primary record was read: it records withdrawal and describes overlap/repetition in neighborhood lists. Its v1 proof was not read and supplies no trusted theorem here. No MathDB lookup was undertaken in this correctness gate, and no prominence or score is assigned. Exact provenance and all output hashes are in the authentication file and the detached final hash list.
