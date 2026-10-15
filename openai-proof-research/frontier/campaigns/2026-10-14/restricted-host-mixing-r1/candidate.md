# D3 restricted-host augmented dynamics: UNRESOLVED

2026-10-14. **Original-scope research gap report; no solved frontier target, substantial nomination, acceptance, or publication.** Pinned OpenAI theorem truth is stipulated at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; every deduction below is checked independently. The supporting reductions and finite obstructions are technical only.

## 1. Full target and fixed proposal convention

For every n, every matching M in E(K_n), and every feasible labelled degree vector d, let Omega(d,M) be all simple labelled realizations of d using only host edges K_n minus M. No degree stability, regularity, minimum-degree, density, or positivity condition is imposed.

Here is one fixed natural local chain P on exactly that state space. With probability 1/2 hold. Otherwise choose k=2 or k=3 with equal probability. Choose an ordered tuple of 2k distinct vertices uniformly from all such tuples, regard it as a cyclic order, and flip its 2k cycle edges if they alternate present/absent and every inserted edge belongs to the host. Accept either alternating phase. If n<2k, that category holds; any other rejected proposal holds. This handles all n without changing the kernel by state or degree. Feasible spaces on n<4 are singletons.

A distinct accepted length-L cycle transition, L=4 or 6, has rate

    p_L = L/[2(n)_L],

because its undirected cycle has 2L ordered representations and the category probability is 1/4. Its reverse has the same rate. Thus the uniform law is reversible and the chain is at least half lazy. These facts alone do not give irreducibility. Every nonzero transition has probability at least 2/n^6. A singleton has mixing time zero.

The requested theorem is that this chain is irreducible for every feasible (n,M,d), and that there are absolute constants C,K with worst-start total-variation mixing time

    t_mix(eta) <= C n^K [log n + log(1/eta)]

for all 0<eta<1/4, with concrete polynomial control. **Neither this theorem nor a counterexample to it is established here.** In particular all-n irreducibility is not inferred from finite checks or from the directed subclass below.

## 2. Exact scope reduction: arbitrary directed degree sequences occur as fibers

Let r_i,c_i be the out- and in-degrees of any feasible loopless simple directed graph on [m], where opposite arcs are allowed. Take distinct physical vertices A={a_1,...,a_m}, B={b_1,...,b_m}, put n=2m, and forbid the perfect matching a_i b_i. Prescribe

    d(a_i)=m-1+r_i,  d(b_i)=c_i.                         (2.1)

**Technical lemma.** Realizations of (2.1) in K_(2m) minus that matching are in exact bijection with the loopless directed realizations of (r,c). Every such undirected realization has A complete and B independent. The bijection sends the arc i->j to a_i b_j. It preserves the uniform law and identifies the accepted 4/6 moves with the alternating 2/3-arc swaps in the diagonal-zero bipartite representation.

**Proof.** The degree-sum difference is m(m-1), since sum r_i=sum c_i. If e_A,e_B count the internal A and B edges, cancellation of cross edges gives

    2e_A-2e_B=m(m-1).

Since e_A<=binom(m,2) and e_B>=0, equality forces e_A=binom(m,2), e_B=0. The remaining cross degrees are exactly r,c, and the missing matching enforces absence of loops. Conversely every such directed adjacency matrix gives the required host realization. An accepted cycle cannot change a forced clique edge or forced nonedge, so it lies entirely in the bipartite cross graph; the converse is immediate. QED.

Thus even perfect forbidden matchings in D3 contain the full directed mixing problem. This is a statement about actual degree fibers, not a projection of an approximate sampler or a conditioned complete-host chain. The construction is standard in spirit; it is supporting scope evidence, not a new result slot.

### A polynomial comparison to switches plus directed-triangle reversals

For clarity the additional arbitrary 3-arc swaps do not remove that directed difficulty by a radically different move set. On any loopless directed realization space define Q as follows: half hold, then choose category 2 or 3 equally. In category 2 choose two ordered distinct source labels and two ordered distinct target labels independently and flip their alternating 2-by-2 rectangle when all entries are allowed. In category 3 choose three ordered distinct labels and reverse their induced directed triangle if the reverse three arcs are absent. Invalid choices hold. For m below a category's size it holds. This is a fixed half-lazy symmetric standard switch/triangle chain.

Every 3-arc swap is either a directed-triangle reversal or a path of at most two valid 2-arc switches. To prove it, write the removed entries as x_i y_i and the added entries as x_i y_(i+1), i modulo 3. The three other rectangle chords are x_i y_(i+2). If x_0 y_2 is allowed and absent, perform

    {x_0 y_0,x_2 y_2} -> {x_0 y_2,x_2 y_0},
    {x_0 y_2,x_1 y_1} -> {x_0 y_1,x_1 y_2}.

If the chord is present, perform these two switches in the reverse order. They restore the chord and change exactly the intended six entries. Cyclically relabel to use any allowed third chord. If all three are forbidden, diagonal-zero restrictions imply y_0=x_1, y_1=x_2, y_2=x_0; the swap is exactly the directed-triangle reversal. All steps avoid loops and preserve the given margins, with no assumptions on entries outside these cells.

There is also a deliberately loose explicit comparison. Let P_s be the D3 chain on the split fiber above. Choose the first available third chord in a deterministic label ordering to define each length-at-most-two path. Q's nonzero off-diagonal rates are

    q_2=1/(m)_2^2, q_3=3/[2(m)_3],

and hence at least m^(-4), for m>=3. For each directed Q edge (U,V), paths using it first are determined by a P_s neighbor of U, and paths using it second by a P_s neighbor of V. A state has fewer than (2m)^6 distinct 4/6-cycle neighbors. Thus at most 2(2m)^6 routed P_s transitions use that directed edge. Cauchy–Schwarz costs at most two for path length, and p<=1 suffices for all P_s rates. With the same uniform law and the usual directed-edge Dirichlet normalization, this proves

    E_(P_s)(f) <= 256 m^10 E_Q(f),
    gap(Q) >= gap(P_s)/(256 m^10).                      (2.2)

There is no exponential state-count factor in this comparison. The route is uniquely assigned to each ordered P_s transition, so the crude incidence count is sufficient here; this is a comparison between neighboring local moves, not an all-pairs congestion construction.

If D3 supplied t_mix(P_s,1/4)<=B(2m), then laziness and the eigenfunction TV lower bound imply gap(P_s)>=1/[1+B(2m)/log 2]. Indeed a centered eigenfunction with supremum norm one gives worst-start TV at least lambda^t/2, forcing lambda^t<=1/2 at time B. Thus (2.2) would yield

    gap(Q) >= [256m^10(1+B(2m)/log 2)]^(-1),

and a concrete polynomial TV bound follows by multiplying its reciprocal by

    (m(m-1)/2)log 2 + log(1/(2eta)).

So a full affirmative D3 theorem would, by explicit operations, also resolve the all-degree directed switch/triangle mixing formulation. This comparison proves no lower bound on the presently unknown D3 gap. Primary precedents already discuss these directed moves; no worldwide novelty is claimed for the reduction.

## 3. Two exact failures of the unchanged source mechanism

### Pair heat baths cannot control the restricted state space

The source-131 pair fiber records all edges away from {i,j}, edge ij, and each outside vertex's number of neighbors in that pair. In a matching-deleted host, outside singleton vertices whose one possible reassignment is forbidden become forced. Removing these forced labels leaves a uniform subset slice; at most two outside labels are forced by the missing matching. Thus the individual free-slice comparison is still elementary.

However the global kernel identification is false. In the supplied six-vertex example, M={01,23,45} and d=(3,1,3,1,3,1), degree sums force A={0,2,4} to be a triangle, B={1,3,5} independent, and cross edges to be one of the two three-object derangements. Hence exactly two realizations exist and their symmetric difference is a six-cycle. Every pair fiber is a singleton: a nonconstant subset fiber admits an exchange of two labels, which would be a valid four-edge switch to a third or to the other realization, impossible here. Therefore every source pair projection E_a is the identity and

    H_pair=sum_a(I-E_a)=0

on a two-point space. For its centered sign function f, Var(f)=1 but <f,H_pair f>=0. A source-style Poincare inequality with this operator is impossible, regardless of a proposed bound on its squared generator. The augmented chain does connect these two states, at off-diagonal rate 1/240 and gap 1/120 under Section 1's convention. That finite repair does not establish all-n mixing.

### The sharp three-row inequality fails after diagonal deletion

Take the uniform law on the two 3-by-3 permutation matrices with zero diagonal. Every row alone determines which matrix was chosen. Let xi be +1 on one and -1 on the other, and let f_i(S_i)=xi for each row. Then

    Var(f_1+f_2+f_3)=9,
    2 sum_i Var(f_i)=6.

Thus source `row:variance`, whose support is the entire fixed-margin binary-matrix space, does not hold unchanged on this diagonal-zero subspace. Equivalently all three conditional row projections fix xi, so their squared norms sum to 3||xi||^2, rather than at most 2||xi||^2. This is an obstruction to a new restricted analogue, not a contradiction of the stipulated source theorem. The example uses only degree-one margins; a generic lower bound on degrees would not address the full assigned target.

A whole-triple heat bath can change this two-state cell. A proof based on such enlarged blocks would still need a new uniform global Poincare estimate for their interactions; source `mix:H-square` is a pair-indexed identity and does not supply one. No such enlarged-block estimate is proved here.

## 4. Exact unpaid bridge and failed approaches

Let L_46 be the unnormalized graph Laplacian of distinct valid four- and six-cycle neighbors in Omega(d,M), with the uniform inner product. A sufficient full-scope bridge would be constants C_0,K_0 independent of n,M,d such that

    Var(f) <= C_0 n^K_0 <f,L_46 f>                       (4.1)

for every real function f on every feasible fiber. This also forces irreducibility. Since p_min>=2/n^6, it would give gap(P)>=[2/(C_0 n^(K_0+6))] and worst-start mixing at time at most

    ceil[(C_0/2)n^(K_0+6)
          {binom(n,2)log 2/2 + log(1/(2eta))}].

No bound (4.1), no equivalent all-pairs polynomial congestion bound, and no all-n irreducibility proof is supplied. The task remains unpaid in its original scope.

The attempted transfers fail at precise points:

- Complete-host source-131 mixing controls a different support. Rejection/conditioning on avoidance of all forbidden pairs has no proved polynomial comparison; forbidden-edge avoidance may be exponentially rare. It is not used.
- The source's pair-fiber subset calculus survives after forcing a few labels, but its global operator has the wrong kernel, as above. Merely substituting the restricted slices into the source proof cannot work.
- The three-row fixed-block argument uses unrestricted label partitions and the exact factorial count law. The diagonal-zero two-state example refutes its unchanged sharp constant before any global sum.
- The source perfect-matching companion gives counting and approximate sampling on arbitrary unweighted hosts by a constant-fiber Tutte gadget and enlarged matching machinery. It gives no intertwining or congestion comparison to this fixed chain. No approximate sampler is offered in place of dynamics.
- I19's exponentially slow positive-weight example varies binary activities on a complete host, whereas D3 is unweighted with augmented moves. I77's complete-host fixed-strength weighted target is still unpaid; its matching flow and bounded-defect conditional interface do not supply the host-restricted all-degree routing. Neither old construction is renominated.
- A route through an arbitrary canonical hub can concentrate exponentially many endpoint pairs even if its diameter is polynomial. No bounded-congestion encoding for the host, including occupied/common pivot chords and forbidden chords, was obtained. Directed P-stable encoding bounds from the literature retain their count-ratio hypothesis.

No actual slow-mixing or disconnected full-target fiber was found. This is not evidence that either is impossible. The finite diagnostic in Section 5 does not decide (4.1).

## 5. Diagnostics, source boundary, and disposition

`exact_checks.py` independently enumerates the supplied six-vertex fiber, checks its 15 singleton pair fibers, verifies the row-variance witness, and checks specified occupancy cases of the two-switch six-cycle decomposition using exact sets and fractions. No numerical eigenvalues enter a proof.

`connectivity_diagnostic.py 7 3` exhaustively enumerates all 262,144 subgraphs of K7 minus a fixed maximum matching. It groups them into 38,912 labelled degree fibers, constructs the 211 distinct valid host cycle masks of length four or six, and unions 1,490,944 undirected transitions. No disconnected fiber is found. This bounded enumeration is a diagnostic only: it is neither a proof of all-n connectivity nor a mixing estimate, and it covers only matching size three at n=7. A preliminary C++ compilation failed because g++ is unavailable; the successful implementation uses the Python standard library.

Read extents, immutable source URLs, and comparisons with actual Greenhill–Sfragara and Erdős et al. primary statements are recorded in sources.md; hashes and source-tree authentication are in provenance.json. Source-131's lower proof operations are stipulated within their actual complete-host quantifiers; the restricted analogues above are independently tested and rejected. The arbitrary-host counting companion and known directed three-edge moves are credited. The rooted-packing I248/I258/I267/I268 technical dispositions and relevant ledgers were consulted and nothing from them is counted again.

**Disposition: original D3 UNRESOLVED.** The exact directed embedding/comparison and the two source-method failures are supporting technical work. They are not a narrower completed substitute, a new substantial theorem, or a counterexample to the corrected target. Further work needs a genuine full-scope inequality such as (4.1), a paid congestion/encoding mechanism, or a rigorous counterexample to the actual augmented chain.
