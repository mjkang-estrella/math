# I166: The affine span of Hamiltonian cycles on cubic planar braces

**Date:** 2026-10-10. **Type:** research iteration (T3), sub-agent of the
Q164 programme. **Scope discipline:** this iteration writes only this
report, `frontier/experiments/i166_affine_span_braces/**`, and
`frontier/sources/i166_affine_span_braces/**`. No ancestor code was
executed; I165's payloads were consumed as immutable data. All pinned
OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are
stipulated true and used only as stipulated.

## 1. Task and summary of outcomes

I166 had three charges:

1. **Audit I165's new mathematical content independently**: the affine
   splice formula (AS), the brace reduction via GSW tight-cut
   decomposition, the counterexample-class certificates, the
   infinite-family arithmetic ($h=62m-44$, $h'=54m+32$, $n=2m+30$,
   gain $=76-8m$), the short-side injection, and the facial-toggle
   failure witness.
2. **Attack the live route's remaining gap**: prove $d(G)=n/2+1$ on cubic
   planar braces, or find a brace with $d<n/2+1$ (kills the affine
   route) or with $h<n/2+2$ (refutes Q164).
3. **Develop at least one genuinely different supporting angle.**

Outcomes, stated fully and only to the extent paid:

- **Audit: every audited I165 interface passes independent
  re-derivation** (Section 2). The I165 sealed replay also passes with
  the task-stated hashes (that reproduces sealed bytes; the mathematical
  verdicts come from my own re-derivation).
- **The brace theorem is not proved and no counterexample was found.**
  The computational attack is instead a large exact certificate:
  **452 diagnosed records covering 443 distinct graphs (438 distinct
  braces) of orders 8–64** — the nine duplicates are census graphs
  rediscovered by the walks, counted once per record —
  with every Hamiltonian-cycle enumeration performed exhaustively by two
  independent enumerators and every rank computed by exact rational
  elimination, **every graph satisfies $d(G)=n/2+1$** and **no graph
  violates Q164** ($h\ge n/2+2$); the Q164-tight graphs in the sample
  are exactly the even prisms (Section 4). The generation engine is
  anchored against the published census OEIS A007083 (exact match
  through order 20) and the splice/count formulas hold on 240
  independently built splices.
- **Supporting angles delivered three new structural facts**
  (Section 6): (i) the first certified smallest example that *brace-only
  C4-generation from the cube is false* — an 18-vertex brace every
  C4-reduction of which lands in a non-brace, certified three
  independent ways; (ii) a *proved* lemma that toggling a Hamiltonian
  cycle along any face on which it alternates always disconnects, so
  facial switches can never witness affine spanning (empirically
  0 of 5795 faces in the swept sample are toggleable); (iii) a
  quantified survival analysis showing the affine form of I165's
  obstruction is generic (in 136 of 142 expansion steps the cycles using
  an expansion edge do *not* span the parent affine hull, deficit up to
  5), which localizes exactly what a proof of the expansion inequality
  must supply.
- **Precise unresolved target** (Section 7): equivalent reformulations
  of the remaining brace theorem, including the constant-weight and
  switch-cycle-span forms and the exact dimension inequality needed at a
  C4-expansion step.

Q164 itself remains unproved and unrefuted. Nothing here is a ninth
substantial positive finding in the sense of the programme ledger; the
contribution classification is in Section 8.

## 2. Independent audit of I165: verdicts

Method. I166 wrote a fresh standard-library-only toolkit
(`experiments/i166_affine_span_braces/lib166.py`): oriented face-list
embeddings with a full certificate (simplicity, cubicity, bipartition,
3-vertex-connectivity by all deletion pairs, Euler characteristic,
rotation consistency), square (C4) expansion, cube expansion as a splice
with the cube, general splice, two *independent* Hamiltonian-cycle
enumerators (a pruned vertex-path DFS and a perfect-matching-complement
enumerator, asserted equal on every use), spanning-path enumeration
(plain and pruned, cross-validated), exact rational row rank, the
2-extendability brace test and an independent contraction/max-flow
nontrivial-3-cut screen (asserted in agreement on every use), and a
dart-rooted rotation-system canonical form. The toolkit is anchored by
`selftest166.py` on classical tiny facts (cube: $h=6$, $d=5$; even
prisms $L_m$: $h=m+2$, $d=m+1=n/2+1$; 52 expansion-identity checks;
splice sanity; canonical-form invariance anchors) — all PASS.

The I165 payloads (`decisive-03.json`, `amplification-01.json`,
`fallback-02.json`) were then read as data only and re-derived in
`audit_i165.py`; output `audit-01.json`. I165's own sealed replay was
also re-run once and PASSES with the task-stated seal/report hashes
(reproducing sealed bytes; that is provenance evidence, not the
mathematical verdict, which comes from my re-derivation below).

| I165 interface | I166 verdict | Independent check performed |
|---|---|---|
| Class certificates of the 50/54-vertex pair | **PASS** | Full certificates rebuilt from recorded face lists; all 1275/1485 deletion pairs |
| Recorded cycle sets (576/572) | **PASS** | Validity per cycle plus set-equality with two independent re-enumerations |
| Admissibility of the recorded step | **PASS** | Common 16-face, distinct terminals, odd residual arcs of lengths 3 and 11 |
| Boundary decomposition 138/52/38/44 | **PASS** | Recomputed from the recorded step; complete six-fibre identity on independently enumerated sets (Proposition E instance) |
| Base pieces $A$, $A'$: orders 32/36, $h=102/124$, ports $(34,62,6)$/$(36,54,34)$, ranks 17/19 | **PASS** | Independent construction, enumeration, port profiles, exact ranks |
| Prism $L_{10}$ profile $(2,8,2)$, $h=12$, $d=11$ | **PASS** | Independent |
| Family arithmetic $h=62m-44$, $h'=54m+32$, $n=2m+30$, gain $76-8m$ | **PASS, strengthened** | Direct construction and enumeration at $m=4,6,8,10,12$ give $(204,248)$, $(328,356)$, $(452,464)$, $(576,572)$, $(700,680)$, matching the formulas with gains $44,28,12,-4,-20$; splice/expansion commutation verified at **all five** orders (I165 checked fewer) via my canonical form |
| Affine ranks $26/28$ of the decisive pair, both full | **PASS** | Independent exact rational elimination |
| Facial-toggle failure witness on $L_8$ step $(1,3,7)$ | **PASS** | Unique lost cycle; both arc toggles split into two components, exactly as recorded |
| Short-side injection $P_{ux}=N_{00}$ | **PASS** | 138 bijection checks on $L_8$, $L_{10}$ and two independently grown graphs; plain-vs-pruned path enumerators cross-validated |
| (AS) as a proved statement | **Proof checked valid** (Section 2.1) | Plus 240 independent numerical confirmations (Section 4.1) |
| GSW brace-reduction contracts used by I165 | **PASS in stated scope** | Read against the actual GSW text (Section 2.2) |

### 2.1 The affine splice formula (AS)

I165 states and proves: if each of the three omitted-port classes is
nonempty in each piece, then $d(G_1\star G_2)=d(G_1)+d(G_2)-2$. I
checked the proof line by line. The two load-bearing steps are valid:
(i) within-class differences $U_i$ satisfy $\dim U_i=d(G_i)-2$ exactly,
because the quotient is generated by three class representatives whose
port projections $(0,1,1),(1,0,1),(1,1,0)$ have rank exactly two and
vanish on $U_i$; (ii) the identification of the six deleted port
coordinates with the three cut coordinates loses no rank, because on
compatible pairs the port coordinates of the two pieces coincide with
each other and with the cut coordinates. The nonempty-classes
hypothesis is paid by the stipulated family-180 edge-avoidance
corollary (every edge of a class member is avoided by some Hamiltonian
cycle), as I165 states. Verdict: **(AS) is a proved theorem in the
stipulated scope.** Consequence used below: since
$n=n_1+n_2-2$, maximal $d$ in both pieces gives maximal $d$ in the
splice, so $d=n/2+1$ for all class members reduces to braces; this is
also what I165 concluded.

### 2.2 GSW/HMM contracts re-read against the sources

All source contracts the audit or the attack relies on were re-read in
the actual texts (ranges in
`sources/i166_affine_span_braces/reading-ranges.json`):

- GSW §2: splice = reverse tight-cut contraction; planarity preserved.
- GSW Lemmas 4.1/4.2: in cubic 3-connected bipartite graphs every
  nontrivial tight cut is a 3-edge cut and contractions stay in the
  class — so tight-cut decomposition of class members ends at braces,
  and my contraction-based 3-cut screen is a legitimate second brace
  characterization (used as a cross-check, enforced everywhere).
- GSW Corollary 4.15: cyclically 4-edge-connected $\iff$ brace, within
  the class.
- GSW rigorous C4-expansion definition (common facial cycle, odd
  residual paths) matches `lib166.admissible_steps` exactly (even cyclic
  distance between the two edges).
- GSW Theorem 5.1 = HMM Theorem 4: a graph is cubic, 3-connected,
  planar, bipartite iff constructible from the cube by cube- and
  C4-expansions. I re-inspected HMM's page 294 (Theorem 4 statement and
  complete proof) visually: reductions are $R_0$ (4-face) and $R_4$;
  and for cyclically 4-edge-connected graphs, "at least one of the two
  possible applications of reduction $R_0$ to any 4-face produces a
  C3CBP". Two consequences I166 uses and verifies independently:
  (a) completeness of my expansion BFS; (b) the *two* applications per
  4-face, which my first contraction draft missed — see Section 6.1 for
  the direct verification of this HMM claim on every 4-face of every
  brace of order $\le 20$.
- GSW Lemma 5.2 (full proof read): C4-expansion preserves
  matching-covered and 2-extendable, hence *braces are closed under
  C4-expansion*. Cube expansion creates a nontrivial tight cut, hence
  its immediate result is never a brace.
- GSW §5.4–5.6 (Lemma 5.3, Theorem 5.4, Figure 4 discussion): a
  C4-expansion destroys exactly the laminar tight cuts separating the
  two expansion pairs; braces can therefore arise from non-braces, and
  GSW explicitly do *not* claim an all-brace generation. This caution
  is exactly what my B18 certificate makes concrete (Section 6.1).
- Family-180 (stipulated): `thm:main`, `cor:edge-avoidance`,
  `cor:pfaffian-paths` (the $P_4$-Hamiltonian contract), used only as
  stipulated.

## 3. The generation engine and its anchoring

`bracegen.py` performs exhaustive BFS from the cube over **all** class
members (not just braces) by square and cube expansions up to order 20,
deduplicated by the canonical form, recording the full expansion DAG.
By GSW Theorem 5.1 this is complete per order. Anchoring:

- **Census cross-check (published data).** The BFS counts at orders
  8, 10, 12, 14, 16, 18, 20 are $1,0,1,1,2,2,8$ — exactly OEIS A007083
  ("unlabeled trivalent 3-connected bipartite planar graphs", citing
  HMM 1985 and Brinkmann–McKay plantri). `census_check.py` enforces the
  match and re-certifies every generated graph. This simultaneously
  validates the expansion operations, the canonical-form dedup, and the
  certificates against published enumeration.
- **Round-trip anchors.** `c4reduce.py` inverts `square_expand` exactly:
  for every generated graph and every admissible step (636 in total),
  contracting the new gadget 4-face returns a canonically identical
  graph.
- **Canonical-form anchors.** Vertex-transitivity orbits of the cube's
  expansions collapse correctly; random relabellings are invariant;
  the prism $L_6$ equals the square-expanded cube; distinct order-16
  members stay distinct (all in `selftest166.py`).

Braces among the census: orders 8, 12, 14, 16, 18, 20 have
$1,1,0,2,1,5$ braces (10 total). Larger braces come from two seeded
random-walk batches over brace-preserving expansions: batch 1 (seed
166, from the cube and prisms $L_6$–$L_{14}$) found 273 distinct braces
of orders 12–48; batch 2 (seed 166002, from prisms $L_{16}$–$L_{24}$)
found 164 distinct braces of orders 36–64. Every walk graph is stored
with its full face list and expansion history.

## 4. The affine-rank campaign: exact results

Every generated graph was diagnosed by `bracediag.py`/`walk2.py`:
Hamiltonian cycles enumerated by **both** independent enumerators with
set equality asserted and enumeration exhaustion flags honored (visit
caps were set but never hit — all 452 enumerations are complete);
$d(G)$ computed by exact rational Gaussian elimination of cycle
differences; Q164 margin $h-(n/2+2)$; brace flag computed by both
characterizations with agreement enforced.

**Results (diag-01.json, diag-02.json):**

| Sample | Records | Orders | All $d=n/2+1$ | Q164 violations |
|---|---:|---|---|---|
| Exhaustive BFS census $\le 20$ | 15 (10 braces, 5 non-braces) | 8–20 | yes | none |
| Walk batch 1 | 273 braces | 12–48 | yes | none |
| Walk batch 2 | 164 braces | 36–64 | yes | none |
| **Total** | **452 records, 443 distinct graphs (438 braces)** | **8–64** | **yes, all** | **none** |

(Duplicates: 8 walk-batch-1 graphs are canonically census graphs, and 1
graph appears in both walk batches; all records were diagnosed
independently anyway.)

Further detail:

- $h$ ranges from 6 (cube) to 8946 (order-64 walk brace). The Q164
  margin $h-(n/2+2)$ is 0 exactly on the even prisms $L_m$ (canonical
  check: every tight sample graph is a prism) and grows quickly off the
  prism line (e.g. order 52: sampled margins $\ge 212$).
- The five non-braces of the census also have full $d$: fullness is not
  brace-specific in the sample, consistent with (AS) plus brace fullness.
- **Affine exchange (AE) holds on every tested step**: for all 142
  admissible expansion steps of census graphs of order $\le 16$,
  $d(H)\ge d(G)+2$ (in fact $d(H)$ is always full). For walk steps this
  is implied by fullness of both ends.

### 4.1 Splices: the count formula and (AS) on 240 fresh instances

`as_check.py` splices pairs of small census graphs over a spread of port
vertices and all (up to six) planar-certifying port alignments — 240
splices total, each fully certified, both enumerators asserted equal:

- I165's exact splice count formula $h(G)=\sum_i a_i b_i$ held in all
  240 (port class counts computed independently on each side).
- (AS) held in all 240: $d(G)=d(G_1)+d(G_2)-2$.
- Every splice had full $d$.

This is independent numerical corroboration of the proved (AS), and
confirms the reduction's gluing direction on generated data.

## 5. Where the direct proof stands: the survival obstruction

The natural induction for the brace theorem is: base cube ($d=5$), step
by HMM expansions, using (AS) for cube expansions (a splice with the
cube, $d$ rises by exactly 3) and a hoped-for **exchange lemma** for C4
expansions: $d(H)\ge d(G)+2$. I165 refuted the *counting* form of the
analogous statement (their $N_{00}=138/576$ family dies completely).
`survival.py` asks the affine form, which is what the transport half of
an exchange proof would need:

> (SURV) Do the Hamiltonian cycles *using at least one of the two
> expansion edges* span the full affine hull of the parent's cycles?

**Answer: generically no.** In 136 of 142 tested steps the cycles
through $e$ or $f$ span strictly less than $d(G)$; the deficit reaches 5
and the doomed class $N_{00}$ reaches 50% of all cycles. Yet AE holds in
all 142 steps. So the two extra dimensions in the child are *not*
carried by transported cycle classes alone; they must be supplied by the
spanning-path classes $P_{ux},P_{vy},D_{11}$. This quantifies precisely
why a transport proof of AE cannot work and where a correct proof must
look. In the constant-weight formulation, writing the expansion as in
GSW Figure 3b, a weight $w$ constant on all Hamiltonian cycles of the
child forces, with $K=G-e-f$:

1. $\hat w$ on $E(G)$ (aggregating the two length-3 gadget paths into
   $\hat w(e),\hat w(f)$) is constant $\gamma$ on $N_{10}\cup N_{01}$
   and constant $\gamma-\delta$ on $N_{11}$, where
   $\delta=[w(u'x')+w(v'y')]-[w(u'v')+w(x'y')]$ is the difference of the
   two square matchings;
2. $w|_K$ is constant on all spanning $u$–$x$ paths of $K$, and on all
   spanning $v$–$y$ paths;
3. $w|_K$ has constant sum over the two-path covers in class $D_{11}$.

The brace theorem via AE is exactly the claim that this system (plus
induction on $G$) forces $w$ to be a vertex potential. Neither the
induction hypothesis nor the path-constancy alone discharges $\delta$
and the $N_{00}$ directions; I did not find the missing global argument.
This is the sharpest form of the remaining gap I can certify.

## 6. Supporting angles: three new structural facts

### 6.1 Brace-only C4-generation from the cube is false at 18 vertices

GSW warn (their Figure 4) that a C4-expansion can destroy tight cuts, so
braces can arise from non-braces. I166 certifies the concrete
obstruction:

- **B18**, the unique brace among the two order-18 class members
  (history: cube, cube-expansion, then one C4-expansion), has **no
  generation from the cube through braces by C4-expansions**.
- Certificate 1 (DAG): reachability through brace nodes over the
  complete expansion DAG of the census (complete by GSW 5.1 plus the
  A007083 census match) reaches every brace $\le 20$ except B18.
- Certificate 2 (order argument): any C4-reduction of B18 lands at order
  14; the unique order-14 class member is a non-brace (a cube-expansion
  of the cube, which carries a nontrivial tight cut). Cube expansions
  are never the last step of a brace generation (their cut survives), so
  no order-12 brace parent exists either.
- Certificate 3 (direct contraction): enumerating all six facial
  4-cycles of B18 and **both** HMM $R_0$ pairings per face (12
  applications), every class-valid contraction lands on the same
  order-14 non-brace canonical form; none lands on a brace.
  (`c4reduce.py`; 6 faces, 12 applications, all recorded.)

Every *other* brace of order $\le 20$ does have a brace-preserving
C4-reduction (all the way to the cube), so 18 is the smallest order
where brace-only generation fails. The same contraction sweep verified
HMM's page-294 claim that *at least one of the two $R_0$ applications to
any 4-face of a cyclically 4-edge-connected class member stays in the
class*, on every 4-face of every brace $\le 20$.

Consequence: an inductive proof of the brace theorem cannot stay within
braces under C4 steps alone; it must either pass through non-braces
(where (AS) then applies to the tight-cut factors) or use a different
generation theorem. McCuaig's general brace generation (J. Graph Theory
38, 2001) is the natural candidate backbone and is recorded as an unread
lead.

### 6.2 A proved lemma: facial toggles always disconnect

**Lemma (face-toggle obstruction).** Let $G$ be a plane graph with a
face $F$ whose boundary is an even cycle of length $2k\ge4$, and let $H$
be a Hamiltonian cycle of $G$ that alternates on $F$ (uses every second
edge of $\partial F$). Then $H\triangle E(\partial F)$ is disconnected.

*Proof.* Alternation gives every vertex of $F$ exactly one $H$-edge
outside $\partial F$; hence $H\setminus E(\partial F)$ is a union of $k$
vertex-disjoint paths covering $V(G)$ whose endpoints pair up $V(F)$,
and no $F$-vertex is internal to a path. The paths lie in the closed
exterior of the face disk, so the induced pairing $\pi$ of the $2k$
boundary vertices is a non-crossing perfect matching (interleaving pairs
would force disjoint exterior paths to cross). Every non-crossing
perfect matching of $2k$ cyclically ordered points matches some
cyclically adjacent pair (take a pair of minimal cyclic distance; its
interior arc is even and internally matched, so minimality forces it
empty). Let $(i,i+1)\in\pi$. The boundary edge $i(i+1)$ lies in
$M_1=E(\partial F)\cap H$ or in $M_2=E(\partial F)\setminus H$. If in
$M_1$, then $H$ contains the closed subwalk (boundary edge $i(i+1)$ plus
the exterior $i$–$i+1$ path), a cycle avoiding the other $2k-2\ge2$
vertices of $F$ — contradicting $H$ Hamiltonian. Hence $i(i+1)\in M_2$,
and the same closed subwalk is a proper component of the 2-regular
spanning subgraph $H\triangle E(\partial F)$, which is therefore
disconnected. $\square$

Applicability: in our class, face boundaries are cycles
(3-connected planar) and even (bipartite), so the lemma covers every
face of every class member. It explains the empirical finding
exactly: across the 288 diagnosed graphs of orders 8–48 for which the
switch sweep was run (every face × every Hamiltonian cycle), **0 of
5795 faces admit a Hamiltonian toggle** (5786 alternate and always
split; 9 faces of large walk braces are never even alternated). Two
consequences:

- The affine hull cannot be witnessed by single facial switches; any
  spanning argument must use non-facial alternating cycles (already for
  the cube, whose 4-cycles are all facial, spanning must come from
  6-cycle switches).
- The right reformulation of the brace theorem in switch terms is:
  **the signed alternating vectors of HC-to-HC switch cycles span the
  cycle space of every cubic planar brace** (equivalently: a weight
  balanced on every Hamiltonian switch cycle is a vertex potential;
  balance on *all* even cycles would give potentials by the
  cycle/cut-space duality, and switch cycles are the Hamiltonian ones).

### 6.3 Sample-scale observations worth stating

- Tightness for Q164 in the sample is exactly the prism family:
  $h(L_m)=m+2=n/2+2$ and $d(L_m)=m+1$, so prisms are simultaneously
  count-tight and affine-full; any $h\ge d+1$ argument is sharp on them.
- Walk samples show $h$ growing superlinearly off the prism line; the
  minimum margin at order 64 in the sample is 1080.
- The 5 census non-braces are also affine-full, so the (AS) gluing never
  loses fullness in the sample.

## 7. Precise unresolved target

Prove or refute, on cubic planar braces $B$:

$$
\tag{T} d(B)=|V(B)|/2+1 .
$$

Equivalent forms, all established in the text above:

1. (constant weights) every edge weighting of $B$ constant on all
   Hamiltonian cycles is a vertex potential $w_{uv}=\alpha_u+\alpha_v$;
2. (switch spanning) signed alternating vectors of Hamiltonian switch
   cycles span the cycle space of $B$;
3. (exchange step) for every C4-expansion $H$ of a class member $G$,
   $d(H)\ge d(G)+2$ — equivalently $\dim\mathrm{CW}(H)\le
   \dim\mathrm{CW}(G)+4$ for the constant-weight spaces — with the
   induction glued by (AS) (proved) over tight cuts and HMM generation;
   the surviving obstruction is exactly the constraint system of
   Section 5 (the $\delta$-identity and the $N_{00}$ directions must be
   killed by the spanning-path constancies);
4. by I165's proved reduction, (T) implies Q164 in full; conversely a
   brace with $d<n/2+1$ kills the affine route and a brace with
   $h<n/2+2$ refutes Q164 — neither exists at orders $\le 64$ in the
   438 distinct generated braces.

## 8. Contribution assessment

- **Audit verdicts:** every audited I165 interface passes independent
  re-derivation, with two strengthenings beyond I165's own checks
  (commutation at all five tested orders; a published-census anchor for
  the canonical-form machinery). The I165 sealed replay reproduces with
  the recorded hashes.
- **New certified mathematics:** the B18 obstruction (smallest,
  three-way certified) making GSW's Figure-4 caution concrete; the
  proved face-toggle lemma; the quantified survival obstruction
  (136/142, deficit ≤ 5, $N_{00}$ share ≤ 50%) that redirects the
  exchange-lemma proof search; the switch-spanning reformulation.
- **New exact data:** 452 fully diagnosed class members (orders 8–64),
  all affine-full, no Q164 violation, tight exactly on prisms; 240
  splice instances confirming both the count formula and (AS);
  generation census matching OEIS A007083; direct verification of HMM's
  two-application reduction claim on all small braces.
- **Not achieved:** no proof of (T), no brace counterexample, no
  refutation of Q164. The computational evidence is sample-scale and
  proves nothing universal; per project rules, numerical evidence is not
  a proof, and no new-to-literature novelty is claimed for the data.
  The face-toggle lemma and the B18 certificate are narrow technical
  facts, new to this project; I found no literature statement of either,
  but absence from searched sources is not a novelty certification.

**Next action.** Two concrete threads, in order: (1) attempt the
exchange step $d(H)\ge d(G)+2$ via the constant-weight system of
Section 5, now knowing the spanning-path classes must carry the extra
dimensions (survival failure is generic); the prism-tight cases show the
inequality cannot be strict, so the argument must be exact. (2) Evaluate
McCuaig's brace-generation theorem (unread lead) as an alternative
induction backbone compatible with (AS), since brace-only C4 generation
is refuted by B18. Continue the exact-rank census to orders 66–80 only
if thread (1) produces a candidate lemma needing targeted tests.

## 9. Validation and evidence chain

- Environment: Python 3.14.7 (standard library only), Linux
  7.2.8-200.fc44.x86_64, 32 cores. All diagnostics run with `-I -B`.
- Every enumeration in every payload was performed by two independent
  enumerators with set equality asserted; every brace flag by two
  independent characterizations with agreement asserted; every rank by
  exact rational arithmetic. Visit caps were configured (4–8M) and never
  triggered; incomplete enumerations would have been marked
  "not evidence" — there are none.
- Evidence files (all under `frontier/experiments/i166_affine_span_braces/`):
  `lib166.py`, `selftest166.py`, `audit_i165.py` + `audit-01.json`,
  `bracegen.py` + `bracegen-graphs.json` + `bracegen-meta.json`,
  `census_check.py`, `bracediag.py` + `diag-01.json`,
  `walk2.py` + `diag-02.json`, `as_check.py` + `as-check-01.json`,
  `survival.py` + `survival-01.json`, `c4reduce.py` + `c4reduce-01.json`,
  `verify.py`, `seal.py`, `owned-files.json`, `prevalidation.json`,
  `seal.json`. Source records under
  `frontier/sources/i166_affine_span_braces/`: `external-bindings.json`,
  `reading-ranges.json`, `literature-search.md`, `oeis-a007083.txt`.
- The verifier (`verify.py`, modelled on I165's) checks every owned and
  bound byte before executing anything, forbids writes/subprocess/
  network/ancestor execution via an audit hook, then recomputes every
  payload from the owned sources and asserts full JSON equality. The
  seal is created once, exclusive-create, only over a passing
  prevalidation; the replay then re-verifies against the seal.
- Honest limits: walk samples are seeded and biased toward
  brace-preserving expansion paths (that is their purpose: reach varied
  large braces); the BFS census is exhaustive only through order 20;
  the splice checks cover small factors; the survival analysis covers
  steps with parents of order $\le 16$; nothing universal is proved by
  these samples. The replay reproduces owned computations deterministically
  and binds the I165/pinned inputs by hash; it does not audit upstream
  truth (stipulated) and does not re-execute I165 code.

Seal and replay receipts (filled at seal time): see
`experiments/i166_affine_span_braces/seal.json` and the replay output
recorded in the final task response.
