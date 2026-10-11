# I174: prism attachments, survivor saturation, and a local defect criterion

Research iteration, 2026-10-10. **Technical result only. Eight accepted
findings remain eight; two remain.** All OpenAI theorems at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true.

## Outcome

The proposed order-32 graph exists with the specified genuine $(3,3)$
octagon and initial loss **3**. Its first lexicographic permitted surgery
has loss **0**, with an explicit full survivor basis. All **six** bounded
first-stage histories, two for each ordered attachment type
$(P_4,P_6),(P_6,P_4),(P_6,P_6)$, saturate. Consequently **zero second-stage
surgeries** are attempted. None of the nine new initial/first-stage graphs
is a brace: an untouched tight cut remains after each first surgery.
There is no new high-loss brace, inequality counterexample, or acceptance
nomination.

The structural conclusion is stronger than a loss-zero table, but has
explicit hypotheses. **A vertex attachment cannot restore a survival
defect when survival is determined on the exterior, all three exterior
survivor port types occur, and the full compatible attachment fibres are
available.** The defect equals the exterior defect exactly. This remains
true for an attachment with deficient affine span. For our six histories,
contracting the untouched attachment gives four distinct exterior
constructions whose survivor spaces are already full. Thus changing
only that untouched attachment cannot repair these particular exteriors.
This does not cover a later operation that breaks its cut.

## 1. Assignment, source contract, and authentication

The full original saved brief
`iteration174-prism-gadget-survival-brief.md`, project `AGENTS.md`,
`sources/upstream.json`, relevant catalogue entry 180, manuscript tree,
I173 report, parent disposition, and parent receipts were read before the
mathematical work. The actual pinned manuscript statement
`cor:pfaffian-paths`, lines 812–828 of
`frontier/sources/i164_structural_graph_discovery/upstream-paper.tex`,
was read. Its finite simple cubic 3-connected bipartite Pfaffian
hypotheses and prescribed-three-edge-path conclusion are retained.
No upstream theorem was audited for truth.

The three detached I173 anchors match:

| Object | SHA-256 |
|---|---|
| Report | `e06169dc4b72c42da7a26797eb73f8368222dc9e7d87290c909af7c243c52fc2` |
| Seal | `6b824bffc72019f3c75dee02c70c1f0173b557cffc4275177f35bcb76356e609` |
| Verifier | `0d3db09c92da4b5c59a164a97daf05039660c16702096b95a9c8bf43e7f4778a` |

The complete owned-file set has **62** files. All **205 non-context
external** bindings and the inventory/successful-prevalidation control
chain match. The **four separate contexts** give **209 external/context
bindings**, not 205. Only the four shared ledgers have inherited drift.
Their old and present hashes are recorded in
`frontier/sources/i174_prism_gadget_survival/authentication.json`.
No mathematical input is exempt.

The parent replay receipt authenticates PASS in **268.718492 seconds**,
six byte-identical payloads, eight blocked probes, empty stderr, and
unchanged bindings. Its independent certificate receipt and integration
disposition were also read. Integration changed shared ledgers after that
replay. These are historical receipts, not I174 execution times.
The parent's full-rank minor modulo the prime 1009, together with the
rational degree-kernel upper bound, proves exact rational rank; it is not
an unexplained modular estimate.

Ancestor Python is opaque hashed evidence. No ancestor executable was
executed, imported, or copied as implementation. I174's graph toolkit,
enumerators, rational linear algebra, surgery reconstruction, certificate
checker, packaging, and replay guard were written independently. No further
agent, shared-ledger edit, staging, commit, or publication was used.

**Explicit pre-seal parent-document transition.** The first inventory build
correctly stopped because the live, unsealed parent disposition changed
during this task. The only addition was a 504-byte note about the parent's
staged whitespace warning in its authenticated profiler capture.
Removing that exact inserted note reproduces the initially bound 6,035
bytes and SHA-256
`013f3423ad3dc3a35f7e51a2e25e012f4288b8386fb5dbe4bcda38b50ae2e5bc`.
The reviewed 6,539-byte version has SHA-256
`6ad8204171fb900bf38fe2a3787088979b2d8f1c080d3ffb8164b057ea086dc6`.
Both exact versions, the inserted note, failed-build source/report
snapshots, empty stdout, and captured assertion stderr are preserved.
The final inventory binds the reviewed live version and the recovered
authenticated initial snapshot. No sealed ancestor changed, no
mathematical content changed, and this is **not** a fifth context exemption.

## 2. Definitions and mandatory first tests

Coordinates are sorted undirected edges and all vector spaces are rational.
For facial order $u,v,\ldots,y,x,\ldots$, delete $e=uv,f=xy$.
The seven families are $N_{00},N_{10},N_{01},N_{11},P_{ux},P_{vy},D_{11}$.
The last family has exactly two spanning path components paired $u-v,x-y$;
isolated cycles are forbidden. Let
$$
S=N_{10}\cup N_{01}\cup N_{11},\quad
L=\operatorname{diff}(S),\quad
L_0=\sum_{ij\ne00}\operatorname{diff}(N_{ij}),\quad
V=\operatorname{diff}(N_{00}),
$$
$$
U=\operatorname{diff}(P_{ux})+\operatorname{diff}(P_{vy})
  +\operatorname{diff}(D_{11}),\quad
\ell=d(G)-\dim L,\quad t=\dim(L+U)-\dim L.
$$
With actual representatives $A,B,C,N,P,Q,D$ in the corresponding
nonempty families and $C_0\in S$, retain the vectors
$$
b=P+Q+D+2e+2f-3C_0,\qquad
\beta=P+Q+D+2e+2f-A-B-C,\qquad c=N-A-B+C.
$$
The bridge increment is
$\eta=\dim(L+U+\mathbb Qb)-\dim(L+U)$.
For the alternating sums $q_A,q_B$ on the complementary odd arcs, use
$q_J=q_A,q_B,q_A+q_B$ respectively. Compatibility means actual membership:
$$
F_J=\{N\in N_{00}:N-q_J\in J\}.
$$
Anchor at a translated compatible member if one exists, otherwise an
actual member of $J$. Let $V_{\rm good}$ be the sum of the within-$F_J$
difference spaces, and $R$ the sum of the residual-minus-anchor spaces.
The exact checks verify $U=V_{\rm good}+R$, and
$$
\delta_V=\dim(L_0+V)-\dim(L_0+V_{\rm good}),\qquad
\delta_R=\dim(L_0+V_{\rm good}+R)-\dim(L_0+V_{\rm good}),
$$
$$
\epsilon=\dim(L_0+V+\mathbb Qc)-\dim(L_0+V),\qquad
\ell-t=\delta_V+\epsilon-\delta_R.
$$
Both $b$ and $\beta$ give the same $\eta$; their difference is checked
in $L+U$. No false containment involving $V$ is assumed.

The first mathematical run, before any new scan, used exactly
`0,520,522,524,527,528,530,533,534,536,539,431`, then C171,
then I172 $G_6,G_{10}$, then the first lexicographic first/second I173
histories at $m=6$. Every development diagnostic repeats this prerequisite.

- Indices 0 and 431 give $(\ell,t,\eta)=(1,0,1)$; the ten high-loss
  indices give $(7,6,1)$. Whole seven-family sets, residual sets, exact
  $\beta,c$, and the difference between independently selected bridges
  are checked, not merely counts.
- C171 at `[1,1,3]` has 110 cycles. The prescribed switch $F=N+s$
  is checked coordinatewise and differs from the generic factor $T$.
  The original functional kills every fresh $L,V$ direction and gives
  $w(N-C_0)=1$, $w(F-C_0)=1/14$, $w(T-C_0)=-1/2$.
  Both factors have exactly two components. All **1,032** disjoint edge
  pairs have independently generated perfect-matching extensions.
- At 431 the separator kills all of $L+U$, has value 10 on the bridge,
  and absolute value 8 on the old difference. All compatible families
  are empty. The old-direction sign depends only on the explicitly
  recorded order.
- Fresh formula constructions of $G_6,G_{10}$ have losses **3,7**.
  Their graph edges and actual face embeddings agree with the evidence.
- The first I173 histories are `[[0,0,6]]` and
  `[[0,0,6],[4,1,5]]`. Fresh square operations reconstruct their edges
  and unoriented face sets. Saved face numbering is data for the second
  declared triple, not executable construction code. Complete independent
  seven-class enumerations reproduce loss zero for both.

## 3. Independent I173 audit, with separate scope verdicts

### S172: PASS ORIGINAL

At a splice vertex outside the prescribed square, the switched factor and
its source Hamiltonian cycle have identical cut coordinates. For a signed
affine certificate let $a_i$ be coefficient totals by omitted port.
The three cut equations, together with coefficient sum one, force
$(a_1,a_2,a_3)$ to be the unit vector of the source cycle's omitted type.
Choosing one attachment cycle of each type, with the actual lifted
attachment cycle on that distinguished type, makes the glued signed sum
equal the prescribed factor on every core, cut, and attachment coordinate.
Protected deletion statuses, and hence the lost-class total, are unchanged.
Negative individual coefficients remain allowed.

The twelve retained remote cases receive fresh reconstructions, complete
seven-class comparisons, signed coordinate identities, and individual
port-total checks. This validates the original signed remote-splice
statement. It does **not** prove coefficientwise positivity or exclusion
for an arbitrary brace-internal prescribed square.

### K172 and R172: PASS ORIGINAL

The cube-splice family remains non-brace. The port-path bijection for a
three-edge splice cut follows by cutting a Hamiltonian cycle into two
spanning paths and restoring the punctures. Each cube type has two paths;
the kernel from both attachments has dimension six and occurs already
among survivors. This gives the original dimension/loss formula, with
the prism's explicitly exhausted cycle list as its core input.

The original path-class argument also pays for endpoints: parity makes a
gadget with one endpoint use one available cut edge; the prescribed
pairing excludes the cut edge that would terminate prematurely. The
gadget restriction must be a spanning path, not a path plus a cycle.
The inverse gluing gives **four**, not one, lifts in all seven classes.
Fresh enumeration verifies every projected family at $m=4,6,8,10$.
The cube family's full Hamiltonian-difference space reaches the degree
kernel, so its ambient kernel argument is legitimate for that family,
not a typed or universal fullness premise.

All compatible old families are empty in these four checks. The alternative
rerouting is reconstructed explicitly: hold the second cube route
`4-5-1-2-6-7-3` fixed, change the first from
`1-5-6-2-3-7-4` to `3-7-6-2-1-5-4`, and remove cut edge $1a_1$.
There are exactly $m-3$ fixed-route old cycles and $m-4$ independent
differences. Adding the single displayed offset gives actual $P_{ux}$
members for every one. This is not the failed binary boundary toggle.
Exact seven-class residual and $b,\beta,c$ tests reproduce the original
$(\ell,t,\eta)=(m-3,m-4,1)$ in the finite checks. The infinite scope
rests on the original exhaustion, port, kernel, and offset argument,
not these four rows.

### Q173: PASS in precisely its finite certificate scope

All **236** records were independently checked without rerunning the
ancestor search: **24 first-stage plus 212 second-stage labelled histories**,
distributed $6/8/10$ and $40/68/104$ at $m=6/8/10$.
These are not isomorphism classes.

For every record the fresh checker verifies simplicity, cubic
bipartiteness, connectivity after every two-vertex deletion, oriented
sphere embedding, and the genuine protected $(3,3)$ face. It checks
every displayed surviving Hamiltonian cycle and its anchor. Two exact
rank algorithms show that the displayed survivor differences have rank
$D=|E|-|V|+1$.

For a connected bipartite graph the unsigned incidence matrix becomes
an oriented incidence matrix by bipartition row signs, so its rational
rank is $|V|-1$. Therefore
$$
D\le\dim L\le d(G)\le\dim\ker B=D,
$$
and every loss is zero, independently of completeness of the ancestor
cycle list.

Every one of **328,920** explicit perfect-matching witnesses is checked
for its fixed edge pair, graph membership, and exactly one incident edge
per vertex. Coverage equals the entire set of disjoint edge pairs.
There are **26,076** successes and **72** failures at stage one;
**302,844** successes and no failures at stage two. The 72 failures are
exactly the three pairs in each remaining tight cut. Its punctured side
has colour imbalance one and all cut endpoints in the majority class,
forcing any perfect matching to cross once. Thus all **212** second-stage
outputs really are braces; absence of an old cut is not the certificate.

All **1,500** rational absorption identities are checked coordinatewise
against the displayed basis, with zero remainders. The certified directions
are also linked to the actual lexicographically selected old/path extension
pairs, rather than treated as unattached vectors. Every recorded extension
belongs to its claimed family. The **six** empty canonical second-stage
transports are retained in the I174 certificate payload with their original
indices, histories, and empty extension data.

The independent check does not repeat I173's exhaustive three-edge-cut
scan or its complete 236 cycle/path enumerations. Those are authenticated
ancestor evidence; two representative surgeries are freshly exhausted.
In particular, the ancestor's “no relocated cuts” observation is not
silently promoted to a new independent enumeration. Its displayed
survivor and matching certificates suffice for the loss and brace claims.

The corrected separator schema failure is preserved through immutable
external bindings: I173's `audit_refinements-attempt-01` has its exact
`.py.disabled` snapshots, empty JSON capture, and
`ValueError: Invalid literal for Fraction: 'L_and_U_zero'`; attempt 02
correctly reads `w` and passes. Neither source stage was altered.

## 4. New construction and port computation

Use core $P_6$ with labels $0,\ldots,11$. For attachment rim lengths
$k_a,k_b$, set $A=12$, $B=12+2k_a$. Attachment labels are $A+i,B+i$;
omit their local vertex 0 and core vertices 0,7. The three pieces have
disjoint labels. The cut maps are exactly
$$
1a_1,\ 5a_{k_a-1},\ 6a_{k_a};\qquad
1b_1,\ 6b_{k_b},\ 8b_{k_b-1}.
$$
The protected face is
$$
1,a_1,a_{k_a+1},a_{k_a},6,b_{k_b},b_{k_b+1},b_1,
$$
with $e=a_{k_a}6$, $f=1b_1$.
For $(6,6)$ it is the exact labelled octagon
`[1,13,19,18,6,30,31,25]`, of order **32**.
The short routes are $1-(k+1)-k$ inside each punctured prism.

The embedding is established through oriented dart successor maps, not
inferred from the suggested face. Starting with oriented prism faces,
the first attachment's unreversed local rotation has Euler characteristic
**0**, not 2. That rejected rotation, including its full graph and face
list, is retained. Reversing the first attachment's local rotation gives
Euler characteristic two. The second attachment uses its unreversed
rotation relative to the chosen core orientation. This implements opposite
boundary orientations on each gluing. Every final directed edge occurs
exactly once in each direction and every vertex has one cyclic link.
The claimed octagon occurs as an actual face. No change to the proposed
edge identification was necessary.

Fresh degree, bipartition, every-two-vertex-deletion, and sphere checks
certify admissibility. The initial graphs have two genuine tight cuts,
so they are not braces.

### Port dimensions, not borrowed cube constants

For a prism punctured at 0, group its complete Hamiltonian cycles by
omitted port:

| Attachment | Omitted port | Paths/cycles | Within-type dimension |
|---|---:|---:|---:|
| $P_4$ | 1, 3, 4 | 2, 2, 2 | 1, 1, 1 |
| $P_6$ | 1, 5, 6 | 2, 2, 4 | 1, 1, 3 |

The combined kernels have dimensions **3** and **5**, respectively;
the full affine dimensions are **5** and **7**. Independence of the
combined within-type spaces is checked, not obtained by merely adding
individual ranks. Thus two P6 attachments have a ten-dimensional kernel,
not the cube family's six-dimensional one.

Every class projection to core $P_6$ is independently checked on full
sets. Fibres are not uniformly four:

| Attachments | $N_{00}$ | $N_{10}$ | $N_{01}$ | $N_{11}$ | $P_{ux}$ | $P_{vy}$ | $D_{11}$ |
|---|---|---|---|---|---|---|---|
| $(6,6)$ | $8,8,8$ | $4$ | $8$ | $4,8,8$ | $4,4,4$ | $16,16,16$ | $8,8,8$ |
| $(4,6)$ | $4,4,4$ | $4$ | $4$ | $4,8,8$ | $4,4,4$ | $8,8,8$ | $8,8,8$ |
| $(6,4)$ | $8,8,8$ | $4$ | $8$ | $4,4,4$ | $4,4,4$ | $8,8,8$ | $4,4,4$ |

Entries are the multiset of fibre sizes over the actual core members,
not an identification of every class with one common product size.
The larger rung-omitted class in $P_6$ supplies the extra two port
directions. Complete vectors, projected offsets, and fibres are saved.

All three initial graphs have
$$
(\ell,t,\eta)=(3,2,1),\qquad
(\delta_V,\delta_R,\epsilon)=(2,2,1),
$$
and all compatible old families are empty. For $(6,6)$,
$d=17,\dim L=14,\dim L_0=12$; for each mixed type,
$d=15,\dim L=12,\dim L_0=10$.

## 5. Exact bounded protocol and outcomes

Face lists are oriented, rotated to their lexicographically least numeric
label sequence, and sorted. A surgery triple is `(face,i,j)`, $i<j$,
in that canonical list. Candidate edges must be internal on opposite
sides of the first attachment cut, disjoint, and outside the protected
perimeter; the expansion must remain bipartite.

Actual evaluation order is $(6,6)$ first and second choices, then $(4,6)$
first and second, then $(6,4)$ first and second. The first $(6,6)$ history
is the explicit first experiment and is **not counted twice** in the
bounded refinement. Its history is stopped immediately when saturated;
the second choice starts afresh from the initial graph.
The bounds are at most two valid first surgeries per type, and at most
four second surgeries only when the first child has $\ell\ge2$.

There are 10, 6, and 10 valid first triples for $(6,6),(4,6),(6,4)$,
respectively. Only the first two of each are executed. The respective
cross-cut candidate skips are 10/6/10 bipartite-orientation failures and
8/8/8 protected-perimeter failures. Every skipped cross-cut triple,
its two edges, and its reason are retained; non-cross-cut pairs are not
members of the declared candidate set. All untested valid triples are
also listed. None is implicitly reported to fail.

| Attachments | First triple | Order | Hamiltonian cycles | $d=\dim L$ | Loss | Untouched kernel | Exterior rank |
|---|---|---:|---:|---:|---:|---:|---:|
| $(6,6)$ | `[0,0,6]` | 36 | 132 | 19 | 0 | 5 | 14 |
| $(6,6)$ | `[0,0,8]` | 36 | 140 | 19 | 0 | 5 | 14 |
| $(4,6)$ | `[0,0,6]` | 32 | 100 | 17 | 0 | 5 | 12 |
| $(4,6)$ | `[0,1,5]` | 32 | 72 | 17 | 0 | 5 | 12 |
| $(6,4)$ | `[0,0,6]` | 32 | 96 | 17 | 0 | 3 | 14 |
| $(6,4)$ | `[0,0,8]` | 32 | 96 | 17 | 0 | 3 | 14 |

For the explicit first experiment, face 0 is
`[1,2,3,4,5,17,16,15,14,13]`, so the deleted surgery edges are
$1-2$ and $16-15$. The new square vertices are 36,37,38,39.
The original protected octagon is untouched.

Each row retains the complete graph and oriented embedding, all seven
families, all exact residual/bridge offsets, and an actual surviving
anchor plus a full independent survivor basis. Every row has
$(t,\eta,\delta_V,\delta_R,\epsilon)=(0,0,0,0,0)$.
The initial P6/P6 surgery increases ambient dimension by two but survivor
dimension by five, absorbing all three missing directions.

Every disjoint edge pair was tested by an independent augmenting-path
matching algorithm. Across the three initial and six first-stage graphs,
there are **9,324 successful matching certificates** and **36 failed
pairs**: six per initial graph and three per first child. Each first child
still has the second attachment's tight cut. No final brace is claimed
and there are no second-stage candidates eligible under the rule.
No exhaustive three-cut census was needed or performed for these new
graphs.

The stop is a bounded search decision. It does **not** prove that a later
cut-breaking operation cannot restore loss, nor that the other 20 valid
first triples fail, nor that all prism attachments behave this way.

## 6. Structural result: exterior-controlled survivor defect

### Proposition S174 (conditional local splice criterion)

Let $H,A$ be finite simple cubic graphs with a vertex splice $G$ at vertices
$z,h$. Assume their three incident edges are bijectively matched and all
three omitted-port Hamiltonian classes $\mathcal A_i$ of $A$ are nonempty.
Let $\mathcal S_H$ be a nonempty subfamily of Hamiltonian cycles of $H$,
meeting **all three** omitted-port classes at $z$.

Define $\mathcal S_G$ to be **all** compatible spliced lifts of
$\mathcal S_H$, with membership depending only on the core cycle.
Let $D_X$ be the Hamiltonian-cycle difference space and
$L_X=\operatorname{diff}(\mathcal S_X)$. Then
$$
\dim D_G=\dim D_H+\dim D_A-2,\qquad
\dim L_G=\dim L_H+\dim D_A-2,
$$
and in particular
$$
\boxed{\dim D_G-\dim L_G=\dim D_H-\dim L_H.}
$$
If both full graph spaces attain their connected bipartite degree-kernel
dimensions and $L_H=D_H$, then $L_G$ attains that kernel too.
For the defect equality alone, **no degree-kernel fullness of $A$ is
assumed**.

**Proof.** A Hamiltonian cycle crosses the splice three-cut exactly twice:
the number is positive and even. Its restrictions are two connected
spanning paths; restoring punctures gives a compatible pair of cycles
of a common omitted-port type. Conversely every compatible pair glues to
one cycle. This is an exact product description separately for each type.

Let $\pi$ keep exterior coordinates and read cut coordinates as restored
$z$-incident edges. It maps $D_G$ onto $D_H$ and $L_G$ onto $L_H$.
Put
$$
K_A=\sum_{i=1}^3\operatorname{diff}(\mathcal A_i).
$$
For any zero-sum signed cycle combination on $A$, its type coefficient
totals $a_i$ satisfy $\sum a_i=0$. Zero incident coordinates require
$a_2+a_3=a_1+a_3=a_1+a_2=0$, hence every $a_i=0$.
Conversely totals zero in each type are exactly sums of within-type
differences. Thus $K_A$ is the zero-port kernel in $D_A$.
The three incident patterns $(0,1,1),(1,0,1),(1,1,0)$ have
two-dimensional affine span, proving $\dim K_A=\dim D_A-2$.
This does not say that an individual type is degree-and-port full.

If a zero-sum signed combination of spliced cycles projects to zero,
its cut equations force zero total in each type. Its internal attachment
part therefore lies in $K_A$; there is no extra cross-type kernel.
For the reverse inclusion, fix one core cycle in each active type and
vary its compatible attachment cycle. Because **every** such lift is
present, every within-type difference is already in the spliced space.
The all-three-type hypothesis applies this argument to both $D_G$ and
$L_G$, so both projection kernels are precisely the same embedded $K_A$.
Rank-nullity proves the two formulas and their difference.

This also pays for cross-type offsets: choose one representative in each
type. All differences are generated by within-type differences and the
two actual differences of these representatives. Their cut images are
independent, and any combination with zero port image has zero coefficient
on both. No arbitrary translation of representatives is discarded.

For the final saturation assertion, the splice has
$|V_G|=|V_H|+|V_A|-2$ and $|E_G|=|E_H|+|E_A|-3$, giving
$D_{\rm amb}(G)=D_{\rm amb}(H)+D_{\rm amb}(A)-2$.
The preceding dimension formula reaches this upper bound. ∎

### Application to these histories

Contract the untouched second attachment to restored vertex 7. The
protected interface becomes a $(3,1)$ hexagonal interface in the exterior
$H$, not a claimed $(3,3)$ brace. Survival of the original deleted edges
depends only on this exterior projection. Each exterior survivor family
meets all three ports, and every compatible attachment path is available.

Fresh independent enumeration and two exact ranks certify the two
affected-P4 exteriors (order 22, survivor rank 12) and the two affected-P6
exteriors (order 26, survivor rank 14). Each reaches its ambient degree
kernel. The six decorated applications include repeated exteriors under
different fresh square labels, not six unrelated reduced isomorphism
claims.

The computation independently projects **all seven classes** onto each
contracted exterior, not just cycles. It retains full fibre multiplicities,
the three active signatures, and exact differences of type anchors.
Holding the exterior fixed and varying the untouched attachment gives
local survivor directions. Their combined ranks are 5 for P6 and 3 for
P4; the exterior image ranks are 14 or 12 as in the table. Their supports
and projection prove zero intersection with any lifted independent image
basis. This gives a small kernel-plus-image certificate of saturation.

With cut coordinates ordered by sorted global edges, the untouched P6
type ranks are 1,3,1 for signatures $(0,1,1),(1,0,1),(1,1,0)$.
The middle signature omits the cut to local rung port 6; it is exactly
where the two additional independent directions occur. P4 gives 1,1,1.
The first surgery creates the missing **exterior** directions; the larger
untouched prism simply contributes its already available full port kernel.

Consequently **any** replacement of the untouched attachment in one of
these four exteriors, with all three nonempty attachment port classes and
the same exterior-controlled complete survivor fibres, still has loss
zero. Even a deficient untouched attachment does not escape this lemma.
If a genuine octagonal embedding is additionally wanted, it must be paid
separately by the appropriate length-two route and planar port reversal.
The statement does not apply after breaking this cut, restricting the
fibres, changing survival internally, or choosing a different exterior.

This is an elementary affine-splice consequence related to I165/I172,
not a demonstrated new-to-literature theorem. It identifies the relevant
search obstruction without asserting universal brace fullness.

## 7. Validation and evidence package

Only standard-library Python under `-I -B` is used.

- Hamiltonian cycles: complements of complete perfect-matching recursion
  versus rooted spanning-path DFS, compared as whole incidence sets.
- Paths and paired covers: vertex-saturation prescribed-degree enumeration
  versus independent path DFS and complementary second-path enumeration.
  Connectivity, endpoints, and exact pairing are checked.
- Ranks: gcd-normalized integer elimination with ascending pivots versus
  sparse `Fraction` elimination with descending pivots. Every requested
  rational rank agrees; no probabilistic or unqualified modular ranks.
- Embeddings: directed-dart coverage, one cyclic vertex link, and Euler
  characteristic two. Simplicity, cubic bipartition, and every two-vertex
  deletion are independently checked.
- Brace assertions: an actual extending perfect matching for **every**
  disjoint edge pair. A cut scan is never substituted.

Source snapshots, every development payload, and even empty successful
stderr files are retained. I174 has no failed mathematical diagnostic
attempt in development. It does have the failed packaging build and its
captured reproduction described in Section 1, before any inventory or
seal existed. The rejected genus-one rotation is retained as
an unsuccessful embedding construction, not filtered out. Both versions
of the extended ancestor certificate audit remain as source-stage evidence.
The inherited I173 schema failure and six empty histories remain
authenticated and unaltered.

Before final diagnostics the complete owned-file inventory binds this
report, authoritative sources, all source-stage artifacts, all payloads,
and the literature receipt. The only non-self-hashed controls are
`inventory.json`, `prevalidation.json`, and `seal.json`. The external set
includes the complete authenticated I173 chain, upstream inputs, original
brief, and parent receipts. The four named ledgers remain separately
identified context, never mathematical inputs.

The verifier authenticates all owned and external bytes into immutable
memory before loading either mathematical module. Only the two exact
owned source byte strings may compile; ancestor executable bytes remain
opaque. Subsequent filesystem reads and writes, mutation, subprocesses,
and network activity are blocked while diagnostics run.

The eight probes are: write, mutation, network, subprocess, unbound read,
outside compilation, outside execution, and forged bytes under an owned
source filename. The four deterministic replays are mandatory tests,
all I173 certificates, bounded experiments, and the structural applications.
Each must be byte-identical to its final bound payload. Before/after checks
cover every owned and external binding, control bytes, and the actual
current bytes of all four contexts.

The final order is inventory, successful prevalidation, **one exclusive
seal**, then read-only sealed replay. No report/source edit or reseal is
permitted afterwards. Detached hashes, successful replay runtime, actual
inventory counts, and probe results are returned outside the report to
avoid circular hash dependencies. Replay command:

```text
python3 -I -B /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/experiments/i174_prism_gadget_survival/verify.py
```

The guard is not OS sandboxing; the interpreter and standard library are
runtime dependencies. Clean-clone reconstruction was not tested. Final
validation receipts do not establish literature novelty or substitute for
the parent's independent review.

## 8. Limits and concrete next step

The primary-literature queries and returned selections are recorded in
`frontier/sources/i174_prism_gadget_survival/literature.md`.
They identify relevant matching-theory and another-Hamiltonian-cycle
papers, but provide only short selections/abstracts/metadata, not full
proof reads. Some polytope hits concern facet-Hamiltonicity of
associahedra, a different problem. No full novelty clearance is claimed.

D168's bounded bidirectional-transfer obstruction and M168's typed
fullness counterexample remain binding. The checks retain
$\rho(L)=\mathbb Q^2$, so no deleted-edge-only separator is introduced.
Neither $V\subseteq U$ nor $V\subseteq L+U$ is assumed; binary toggles
can isolate cycles. C171's negative generic $T$ is not its prescribed
$F$. S172 remains remote signed transport, not universal brace-internal
prescribed-factor exclusion.

No genuine high-loss brace was found, so there is no new nontrivial brace
on which to attack
$\delta_R\ge\delta_V+\epsilon-1$ or
$\delta_R+\eta\ge\delta_V+\epsilon$.
Their universal high-loss-brace forms, the target witness,
prescribed-square exclusion, (T), and Q164 remain open. There is no
acceptance increment.

**Concrete next step:** change the **affected first attachment**, not the
untouched one. On core P6 replace corner 0 by punctured P8 using
$1-a_1,5-a_7,6-a_8$ and its short route $1-9-8$.
Keep the other corner contracted to 7 initially. Test only the first two
perimeter-avoiding cross-first-cut surgeries on this smaller exterior
(order 30 after surgery), measuring the survivor deficit and all three
active port types before attaching P4 at 7. Attach it and attempt the
second cut only if a first exterior actually retains loss at least two.
This is a specific **unperformed** test; no survival or bracehood outcome
is predicted.
