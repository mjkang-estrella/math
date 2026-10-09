# I07 structures: final prior-art and significance audit, round 3

**Recommendation: TECHNICAL ONLY under the requested substantial, nonroutine-finding standard. Retain the independent proof PASS; do not count this candidate as a fourth substantial finding. This is not a finding of a literal literature duplicate or a mathematical counterexample to Theorem T.**

The decisive reasons are mathematical reductions, not unsuccessful searches. First, Lemma A is an immediate application of B's existing cyclic-cover criterion to a finite cover, with no new extension-cocycle theorem needed. Second, the stated rank conclusion can be obtained by finite replication of the source's unmodified cyclic detector, one for **each nonzero binary direction**, followed by the same local chamber verification and reflection. The failure of only **r coordinate detectors** does not exclude this construction. The endpoint-bit construction improves that replication to a stronger, compactly specified cover classification; its remaining parity mechanism is classical signed-graph balance implemented by the source's local four-tip machinery. This is useful work, but I do not judge the remaining advance sufficiently nonroutine for the user's gate.

Current accepted count is **3: R006, R008, R009**, as instructed by the parent. The older count of two in the proposal and proof review is historical. Only the parent assigns R numbers or changes counts. This review changes no shared index.

## 1. Exact statement, scope, and reading record

The statement assessed is: for **every** integer r ≥ 1 there is a closed connected oriented aspherical topological **four**-manifold M_r and an injection E_r = (Z/2)^r → Out(π₁M_r) such that

    E_r ∩ im(Homeo(M_r) → Out(π₁M_r)) = {1}.

Every nonidentity element is excluded from representation by **any** homeomorphism, including one of infinite order. Failure to lift a finite group action alone does not suffice. Dimension is fixed, the manifold may depend on r, and neither the entire outer automorphism group nor the number of unmarked manifold structures is specified.

I read the complete proposal and independent round-2 proof review, AGENTS.md, the pin, the complete preprint inventory, and the theorem contracts. The source-proof comparison concentrated on the complete B chamber, formal, cyclic, and reflection sections; B's introduction and the statements of its models/extension/normalizer/hyperbolicity sections; the actual MT marked-body and exterior-dual proofs; and PD's marked-exterior and connected-cut arguments. The broader companion statement screen includes all four topology manuscripts listed below, including the boundary-only disk paper. This accepts every applicable pinned theorem as true and does not reopen their proofs.

The immutable revision is **fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb**, repository https://github.com/openai/math. Inputs at review time:

- Proposal, 44,910 bytes: SHA-256 `09631282a1d757480eecb53456017ec429ee8a790d4d8c1e1b71b04ba79136f9`.
- Round-2 review, 32,805 bytes: SHA-256 `f70a6329061df65caced407ac32d97583127f01cdb3163a3508711ea750fe875`.
- Complete preprint tree, 4,858,136 bytes: SHA-256 `eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b`.
- AGENTS.md: SHA-256 `e9ab951853e1607e8d125adb5609a89214a46bb655fda39874257b8210093e7e`.

The complete tree has **13,223 entries, 10,373 blobs, 749 manuscript directories, and `truncated: false`**. All entries were parsed, with duplicate paths rejected. The full directory inventory and the complete paths for the topology-related title screen are retained in `inventory-screen.json`; this was not a screen of catalogue abstracts alone. All **253** cached TeX/BibTeX files were checked against SHA-256, byte counts, pinned URLs, and Git blob hashes in that inventory. All **37** existing contracts were checked against their exact source-line slices and statement hashes. A further inventory records **149** theorem/proposition/lemma/corollary/remark environments in the four closest topology manuscripts. Inventory coverage is not a claim to have substantively read every theorem in all 749 manuscripts.

The independent proof PASS and its geometric checks are accepted as completed work. I did not rerun its 280-artifact proof audit or upstream certificates. The new diagnostics here test the novelty reductions, not those already-audited geometric assertions.

## 2. What the strongest pinned sources already provide

The following abbreviations refer to `build/` beneath the indicated manuscript directories at the pin:

- **B**, [Nonhomeomorphic closed aspherical four-manifolds with the same homotopy type](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Nonhomeomorphic-closed-aspherical-four-manifolds-with-the-same-homotopy-type-October-4-2026/build).
- **MT**, [A marked tensor obstruction to four-dimensional disk embedding](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-marked-tensor-obstruction-to-four-dimensional-disk-embedding-September-24-2026/build).
- **PD**, [A PD4 group without an aspherical manifold model](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-PD4-group-without-an-aspherical-manifold-model-September-24-2026/build).
- **BO**, [A boundary-only obstruction to four-dimensional disk embedding](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-boundary-only-obstruction-to-four-dimensional-disk-embedding-September-24-2026/build).

B already gives both a nonhomeomorphic homotopy-equivalent closed aspherical four-manifold pair (`thm:pair`) and an individually unrealizable self-homotopy equivalence (`thm:self-map`, `cyc:homotopy-involution`). The latter has order two in the homotopy/outer group, and its proof already excludes infinite-order realizing homeomorphisms. Thus r = 1 and the “any representative” distinction are imported achievements, not new features of this iteration.

B `ten:assignment`, `sections/tensors.tex:29–77`, is already an arbitrary **finite loopless multigraph** theorem, with arbitrary local forbidden edge sets, arbitrary endpoint signs, zero-dimensional edge blocks allowed, and actual gradient ideals over the full multivariable nilpotent parameter ring. The present work does not generalize that algebraic theorem. Its five-parallel-edge deficiency argument is already the proof of B `ten:odd-cycle`, immediately following it.

B's geometric statements are narrower than that tensor theorem: its installed bodies and cyclic graph are specified in `ch:four-tip-model`, `for:cuts`, and `for:formal-data`. One must check a new body list against their proofs, rather than simply cite them with broader quantifiers. But the proofs reveal exactly where the specialization occurs:

- `chambers.tex:149–243` places any finite prescribed list with distinct marked tip ports by separated tracks, based connector trees, and independently adjusted framings. Color does not enter a plumbing chart.
- The middle-form and full-basis calculation is per body plus the sum of those contributions; it does not depend on a cyclic deck quotient.
- `formal.tex:73–117` already cuts over the universal covering **tree of a multigraph**, not a line. Its extra-loop generators and prescribed torus collars are the relevant inputs.
- `formal.tex:151–224` uses graph cohomology, the number of extra loops, and per-cut peripheral lines.
- `formal.tex:663–751` uses the law list one four-set at a time. Deleting mixed-channel laws does not remove a test required for a retained law. The actual-ideal/Nakayama argument and nilpotent corrections are unchanged.
- `refl:cover-comparison` separates full lifted-panel labels from reused downstairs labels by a finite cover. Its proof is local on incident panel subgroups and is not intrinsically cyclic.

MT supplies the marked geometry, based edge slices, marked algebraicity, and full-parameter corrections. PD supplies the graph-type PD chamber and the manifold-model-to-marked-filling implication. BO supplies a disk obstruction, not a simultaneous outer-action theorem. Their actual statements do not already state Theorem T for all ranks. They also do not add a hidden stronger simultaneous-realization theorem that could justify counting the same content again.

There is an additional potentially misleading feature of B: it already constructs a large elementary abelian group A of **realized** symmetries and an unrealizable involution δ, inside A × ⟨δ⟩ (`ext:outer-actions`, `ext:delta`). All of Aδ is unrealizable on that model, because a realizing representative for aδ could be composed with one for a. But this is a **coset**, not the desired subgroup. Any subgroup E disjoint from A injects into (A × C₂)/A ≅ C₂, so has rank at most one. The twisted graph subgroups B_ℓ in B have the same codimension-one limitation on their respective models. I therefore do not call Theorem T a literal restatement of B's large label group.

## 3. Exact reduction of the claimed higher-rank height lemma

This reduction uses B's theorem as stated; it needs no new geometric input.

Use the notation of candidate Lemma A. For the chosen integral basis u,u₂,…,u_r set

    L₀ = ⟨u, 2u₂, …, 2u_r⟩ ≤ Z^r,
    G⁰ = w⁻¹(L₀),
    χ: G⁰ → L₀ → Z,

where the last map takes the coefficient of u. Let Q⁰ be the finite connected cover of Q with group G⁰. It is a finite aspherical complex, χ is onto, and its d-fold cyclic cover has group

    χ⁻¹(dZ) = w⁻¹⟨du, 2u₂, …, 2u_r⟩.

In particular its double cyclic cover is exactly Q_(2Z^r), because the displayed basis is unimodular. Its odd cyclic covers of degrees d = 2R+1 are exactly Q_ΛR. The hypothesis in Lemma A is precisely eventual nonrealization of these odd covers. Choose γ with w(γ)=u. Then γ ∈ G⁰ and χ(γ)=1. **B `cyc:criterion` applies verbatim**, excluding any homeomorphism of M inducing Ad_γ.

There is no illicit replacement of an extension by a split extension. The cyclic kernel here is

    ker χ = w⁻¹⟨2u₂,…,2u_r⟩,

which already contains all transverse deck transformations and their commutator information. It is larger than ker w. B's original cyclic proof retains that entire kernel; only the final quotient is infinite cyclic. Thus the Heisenberg issue is genuine for the candidate's chosen proof but unnecessary for the deduction. The candidate's normal-form proof can be correct while the lemma remains a direct source corollary. **No separate novelty credit is due to Lemma A.**

## 4. A finite replication that defeats the principal nonroutine-rank argument

The proposal correctly refutes the construction with only the r coordinate-direction gadgets. It does not refute finite replication in all relevant directions. Here is the stronger comparator, with its geometric obligations made explicit.

### 4.1 Detector list and positive cover

Put U = {0,1}^r \ {0}. For each u ∈ U take ten plumbing types: five red and five blue, both ports of each type having the **same** color. Give each such plumbing generator height u. Use separate ports for different u, retain nine common extra loops, and put height zero on the extra loops and replacement normal circles. The e_j occur in U, so the height map is onto Z^r.

Install the source's full independently conjugated/signed four-tip law list **within each u-channel**, with pattern (R,B,R,B), and no laws mixing channels. This is a finite list of ordinary source four-tip bodies. There are m = 10(2^r−1) plumbing types; if k₀ is the number of bodies in one source block, there are (2^r−1)k₀ bodies. An exponential size is allowed by the exact theorem, which imposes no complexity bound.

In the cover with quotient Z^r/2Z^r, choose for each u an index a(u) with u_a(u)=1, and select at vertex v the color v_a(u) in channel u. Along an edge v → v+u the selected color changes. Since both ports have the same color, exactly one endpoint cap is selected. Every upper torus has one cap of each color; the source's disjoint-cap compression supplies the marked filling. Channels use disjoint plumbing charts, so their selections do not interfere. The resulting reflected manifold still has **dimension four**.

### 4.2 Negative covers sufficient for every outer involution

For the particular nonzero binary vector u, choose a with u_a=1 and use the basis u and e_j for j ≠ a. For d=2R+1 ≥ 3 put

    Λ(u,d) = ⟨du, 2e_j (j ≠ a)⟩.

In A = Z^r/Λ(u,d), the image of u has order **exactly d**. Consequently the u-channel consists of odd cycles, with five red and five blue parallel edges per successive pair. Any endpoint assignment for the full graph restricts to an assignment of the edges of this channel. Its within-channel four-set prohibitions force deficient colors to alternate around each odd cycle, exactly as in B. This is impossible.

All plumbing directions in U remain nonzero in A, so the full graph is loopless. Indeed a binary vector v has coordinates

    (v_a, v_j − v_a u_j for j ≠ a)

in this basis. Membership in Λ requires d | v_a and even transverse coordinates. Since v_a is 0 or 1 and d ≥ 3, it forces v_a=0 and then every other v_j=0. Thus only the zero binary vector could be a loop. This check is essential: invoking B's tensor theorem on a graph with unnoticed loops would invalidate the shortcut.

### 4.3 Why the geometric interface transfers here

This is not the invalid assertion that a filling of a large graph restricts to a filling of a cyclic subgraph. No such geometric restriction is used. Apply the formal-data construction to the **whole** graph, then restrict only the resulting combinatorial endpoint assignment.

The necessary whole-graph verification is the same local extension already checked in Lemma G, in a simpler situation with no opposite-bit ends. The source proof supplies each piece:

1. The finite list has distinct ports, separated bodies, product framings, and the same source Brunnian law. It merely omits mixed-channel quadruples. Opposite ports retain their source same-color convention.
2. The cofiber and full-middle-basis calculations give the free graph group plus two spheres per body. They are unchanged under arbitrary height assignments to the plumbing free generators. Replacement pieces have height zero, so the basis and boundary markings lift in the required covers.
3. Undoing laws leaves the marked graph and nine extra loops per vertex. Its tree-cut construction is B's same tree construction. For an index-n cover, the degree-one count is b₁(W) = [10(2^r−1)+8]n+1; after removing graph classes, the kernel is exactly the 9n extra-loop evaluations.
4. Single-cut edge inputs, signed restrictions, and the common background are independent of color. For each retained four-set, the full conjugator/sign list gives the same actual product-ideal membership. No law linking two channels is required, and mixed nilpotent products are retained.
5. Thus B `ten:assignment` applies to the full graph. The negative implication follows from its assignment on the odd u-channel, while the positive implication uses the cap selection above. Reused-panel reflection gives the positive manifold model, and the full-panel finite cover gives the negative marked-filling implication, exactly as in candidate Theorem F.

This records the source-local verification, rather than assuming a general graph geometry theorem that B did not state. It requires no new cap type, new formal estimate, new tensor theorem, or preservation of a nonrealizable class under an arbitrary retraction.

Now apply §3 separately to each u. The common positive model is the 2Z^r cover. Every necessary odd skew cover has no model. The same quotient conjugation map (Z/2)^r → Out(π₁M) is injective because each nonzero class is unrealizable. This supplies the **exact main rank conclusion** by finite replication of cyclic detectors and the source's local proof machinery.

This is a prior-art/significance reduction, not an additional proposed finding or an independently promoted construction. It explains concretely why “r independent copies fail” does not establish the advertised nonroutine gate. Arbitrary r is obtained by increasing the number of source blocks inside one four-dimensional chamber, not by taking products of closed manifolds.

## 5. The genuinely additional content that survives those reductions

The candidate does more than the all-directions replication: it enforces

    marked filling exists ⇔ Λ ⊂ 2Z^r

for every finite-index Λ with e_j ∉ Λ, and passes this criterion to reflected closed manifold models. The replication above need not detect all such lattices.

An explicit distinction is r=2 and

    Λ = ⟨(4,0), (−1,1)⟩,
    Z²/Λ ≅ Z/4,  e₁ ↦ 1, e₂ ↦ 1.

The three nonzero binary directions have orders 4, 4, 2, all even. Thus all three independent cyclic channels admit alternating selections. Nevertheless (−1,1) ∈ Λ has odd coordinates and e₁,e₂ ∉ Λ. The candidate's coupled criterion correctly excludes this lattice. I do not collapse the exact classification into the weaker replication result.

Its combinatorial mechanism, however, is standard. Once B's five-edge deficiency test forces a unique bit at each vertex, the i-th channel has equations

    σ_i(v+e_j) − σ_i(v) = δ_ij in F₂.

Write the sign on a j-edge as (−1)^δ_ij and the vertex switching function as (−1)^σ_i(v). These equations say that the signature is a vertex coboundary. A closed walk has sign (−1)^λ_i, where λ is its integral displacement in Λ. Hence a solution exists precisely when every λ_i is even. This is the usual balance/potential criterion for signed graphs, coordinate by coordinate. Theorems 1.1–1.2 and the spanning-tree proof in Zaslavsky's author-hosted [Negative (and positive) circles in signed graphs](https://people.math.binghamton.edu/zaslav/Tpapers/npc.pdf) state this criterion; I read the complete statements and accompanying proof, not just an abstract. The routing choice 1−δ_ij translates that standard constraint into the source's endpoint deficiency convention.

The **new-to-corpus bridge** is therefore the explicit signed-port, channel-separated realization of these simultaneous balance constraints by marked four-dimensional chambers, with the exact cover criterion. The independent audit checked that the source local constructions tolerate this relabeling, including opposite ports on one upper torus. That verification is valuable and cannot be replaced by a citation to the tensor theorem alone. But it changes only the finite incidence/law list and its bit labels; the geometric, formal, and reflection arguments are the same source arguments with their local hypotheses checked.

My separate significance criterion requires more than a correct construction and a stronger quantifier: a new obstruction, a substantially new geometric or algebraic bridge, or a consequence not accounted for by finite assembly of the strongest source machinery. On that criterion the main rank theorem is a finite amplification, the height lemma is a direct corollary, and the exact cover theorem is a signed-balance application with a checked local extension. The 10r² specification is much smaller asymptotically than 10(2^r−1), but the task did not ask for an optimized size bound, and the manifold complexity is not itself analyzed. I recommend retaining this as a technical strengthening rather than spending one of the ten substantial-finding slots.

## 6. External primary-literature comparison

Searches were performed during 2026-10-08 Pacific / 2026-10-09 UTC, including current indexed papers and recent developments. Primary texts, not search snippets, support the comparisons below. Six earlier PDF/text pairs were recovered from the retained literature cache and their recorded hashes verified. Seven additional primary PDF/text pairs were downloaded and hashed in this review's directory. Version dates and theorem locations are recorded in `reading-index.json`; exact downloaded bytes govern the citations.

**Block–Weinberger, 2008.** I read Problem 1.1, Proposition 1.2, Theorems 1.5–1.6, and the construction discussion. Theorem 1.6 is a Z/2 finite-action nonrealization example with centerless π. Theorem 1.5 treats a relatively torsion-free extension of a virtually torsion-free group, with a prescribed aspherical action that does not extend. Proposition 1.2 uses dimension at least five and Borel hypotheses for torsion-free extensions. These statements neither exclude arbitrary-order representatives of a single outer involution nor give the present rank family in dimension four. They establish important prior art, not an exact duplicate. [Primary published manuscript](https://math.uchicago.edu/~shmuel/Nielsen.pdf).

**Bartels–Lück, 2012; retained arXiv v2, 2010.** Theorem A gives prescribed-class topological rigidity for closed aspherical manifolds of dimension ≥5 with group in their class B (containing hyperbolic and finite-dimensional CAT(0) groups). Proposition 0.3(ii) extends the conclusion to dimension four only under Freedman goodness, in addition to the stated assembly hypotheses. Its part (iii) gives an ANR-homology-manifold conclusion for finitely dominated PD complexes in dimension ≥6, not arbitrary four-manifold realization. These hypotheses do not trivialize or contradict the stipulated construction. [Primary manuscript](https://arxiv.org/pdf/0901.0442).

**Davis–Hayden–Huang–Ruberman–Sunukjian.** The retained December 2024 v2 has Theorem 1.1: closed aspherical smooth four-manifold pairs that are homeomorphic but not diffeomorphic. Its introduction and Proposition 2.1 explain the reflection of compact exotic pieces and the smooth genus obstruction. This is a serious comparator for local-to-closed promotion and cover arguments, but the topological homeomorphisms exist. It does not supply the requested Homeo-image obstruction. [Author manuscript](https://people.math.osu.edu/davis.12/papers/dhhrs.pdf).

**Daura Serrano, published 2025.** Theorem 1.6 assumes a finitely generated center and a Minkowski outer group and gives Jordan, discrete-symmetry, and almost-asymmetry conclusions for actual finite actions; its fourth conclusion assumes Aut is Minkowski. Proposition 1.11 makes Out finite and Aut Minkowski for products of closed aspherical manifolds with hyperbolic groups and factor dimensions at least three. The constants concern each fixed manifold/group, not a uniform bound over all M_r. They do not bound ranks of individually unrealizable outer classes across different manifolds. [Primary manuscript](https://arxiv.org/pdf/2407.13602), [publication record](https://academic.oup.com/imrn/article/2025/10/rnaf126/8139877).

**Davis, reflection group trick.** I read Theorem 11.1.1 with its thickening construction and proof, and §11.7, especially Proposition 11.7.1 and Theorem 11.7.3. The first turns a finite aspherical complex, thickened to a compact manifold, into a closed aspherical manifold retracting onto it; the dimension is that of the thickening, not automatically four. The equivariant version assumes an actual finite action on the input pair with an admissible simplicial boundary action. It extends that actual action and computes fixed spaces and normalizers. Theorem 11.7.3 gives virtual PD examples in dimensions ≥6 whose finite-subgroup normalizer quotients need not be virtual PD. None says that a nongeometric outer class survives a retraction, or supplies the present fixed-four-dimensional rank obstruction. [Author-hosted book, §§11.1, 11.7](https://people.math.osu.edu/davis.12/davisbook.pdf).

**Davis–Leary.** Theorems 1–2 and the equivariant construction in §2 distinguish proper cocompact contractible-manifold actions, finite models for proper classifying spaces, and actions with manifold fixed sets. The construction starts from an actual action on a pair with flag boundary and preserves dimension when the input is already a manifold. The examples obstruct stronger proper/fixed-set models; they are not a theorem forbidding every homeomorphism in prescribed outer classes. This explains why equivariant-reflection terminology alone cannot be used as a duplicate certificate. [Primary manuscript](https://people.math.osu.edu/davis.12/examples.pdf).

**Avramidi–Okun–Schreve, 2024.** Theorem D takes a compact n-manifold with flag-triangulated boundary to a closed n-manifold retracting onto it, preserving asphericity, hyperbolicity, virtual specialness under the stated hypotheses, and residual finiteness. I also read the §7 proof of parts (1)–(4). It is an effective dimension-preserving promotion tool once a suitable compact input exists. A retraction by itself does not force a homeomorphism of the output to preserve or restrict to the input. It supplies no general preservation theorem for the Homeo-image obstruction or the lattice classification. [Primary manuscript](https://arxiv.org/pdf/2301.06112), [published theorem](https://link.springer.com/article/10.1007/s00039-024-00667-w).

**James F. Davis–Lück, 2024.** Theorem 1.4 assumes a finite extension 1→π→Γ→G→1, an oriented closed d-manifold model for Bπ with d≥5, π hyperbolic, every nontrivial finite subgroup of Γ cyclic of odd order, and conditions (M), (NM), (OH). These specify unique maximal finite overgroups, their self-normalization, and a homological surjectivity condition. It concludes existence, pseudofreeness, and equivariant uniqueness of a cocompact proper Γ-manifold model. This is a positive high-dimensional proper-action theorem, not a four-dimensional individual obstruction. I read the full theorem and its definitions. [Published author offprint](https://jfdavis.pages.iu.edu/papers/dl5.pdf).

**Hilman–Kirstein–Kremer.** Theorem A and Corollary 1.2 remove the extra homological condition in the case of an extension by C_p for an **odd** prime p, π the hyperbolic group of a closed orientable aspherical manifold of dimension ≥5, and Γ pseudofree (every nontrivial finite subgroup equals its normalizer). They give positive proper-manifold/Nielsen realization. Both the dimension and group-order restrictions matter here. This recent refinement does not already solve the candidate's four-dimensional problem. [Primary manuscript](https://arxiv.org/pdf/2409.02220).

**James F. Davis–Hillman, 2025 preprint, June 2026 v2.** Theorems A–D classify compact aspherical four-manifolds with elementary amenable group via permitted groups and enhanced peripheral systems. The closed case has a polycyclic PD4 group; the accompanying rigidity statement makes prescribed relative homotopy equivalences homeomorphic. I read the complete introductory theorems, including the boundary hypotheses. This is genuine dimension-four prior art, but on a restricted group class. The candidate's group contains a nonabelian free subgroup through its chamber retraction, so is not elementary amenable. [Primary manuscript](https://arxiv.org/pdf/2501.12512).

**Signed graphs.** Zaslavsky's Theorems 1.1–1.2 identify precisely the combinatorial balance calculation in §5. This comparison reduces the novelty claim for the finite parity mechanism; it does not purport to contain the four-dimensional topology. [Primary author text](https://people.math.binghamton.edu/zaslav/Tpapers/npc.pdf).

No exact published duplicate was established. In particular, the ordinary generalized Nielsen literature cannot justify a “duplicate” verdict by conflating finite action nonrealization, a proper-action fixed-set obstruction, a smooth obstruction, and exclusion from the image of all homeomorphisms. My technical-only recommendation instead rests on §§3–5 and the strongest **stipulated corpus**.

## 7. Other proposed routine transfers and their actual limitations

A direct product of r four-manifolds has dimension 4r and so fails the statement. Moreover a nonrealizable map on one factor need not remain nonrealizable after stabilization without an additional argument. Disjoint unions lose connectedness. Connected sums of nontrivial closed aspherical four-manifolds are not aspherical: their free-product fundamental group has more than one end, incompatible with an aspherical closed PD4 group. These are not valid shortcuts.

Permuting identical reflected pieces normally produces actual homeomorphisms. Promoting a finite abstract action by the usual equivariant reflection trick assumes an actual compatible action on its input; it does not turn a forbidden class into many independently forbidden classes automatically. Likewise, “virtually a manifold group” alone does not decide which finite-index subgroups admit manifold models. A finite cover of a manifold is a manifold, but downward realization needs an action or additional rigidity hypotheses, exactly what is at issue.

The useful shortcut here is more specific: a finite list of the source's parity channels, geometrically installed before reflection, indexed by every class that needs exclusion. This avoids all of those defects and only asks the source-local general graph verification already available. It is the appropriate challenge to the substantive gate.

## 8. Proof status, next target, and priority limit

**No mathematical gap in the submitted theorem was exposed by this comparison.** The full-middle-basis, opposite-port, arbitrary-graph cut, actual-ideal, nilpotent, and reflection issues remain covered by the independent PASS. The principal correction is to the claimed amount of novelty: Lemma A is a direct corollary, and the mixed-relation counterexample excludes too narrow a class of finite-copy alternatives to establish that Theorem T itself needs the coupled mechanism.

A concrete harder target is an individually unrealizable outer class of **order three** on a closed connected oriented aspherical topological four-manifold. One possible route would be a new three-state marked chamber with a 3-fold-cover filling and eventual nonfilling in cyclic degrees 3R+1, followed by the analogous one-dimensional height argument. A realizing homeomorphism for the square of an order-three class would, on squaring, realize the class itself, so excluding one generator would exclude both nonidentity elements. The unresolved step is an actual ternary cap/law construction with verified positive fillings and full formal-ideal obstruction; binary relabeling does not supply it. This is a plausible research target using the existing interfaces, **not a solved theorem or a promised achievable result**. It should be tested first at rank one before any further rank packaging. It would address an obstruction type not obtained by repeating B's binary detector.

The literature conclusion is bounded: I examined the pinned inventory and strongest relevant manuscripts, recovered retained literature, and searched current primary sources along the specific Nielsen, virtual-PD, fixed-dimension, reflection, and signed-graph routes. This is not an exhaustive worldwide priority certification. Older terminology, nonindexed papers, forthcoming work, and unlocated general realization theorems may remain. No MathDB numerical rank, score, featured status, or independent resolution of Borel/Wall is asserted. Search absence plays no role in the demotion.

## 9. Reproducible artifacts and write boundary

Supporting files are only in `frontier/{sources,experiments}/i07_structures_novelty_r3/`. The source directory contains:

- `input-hashes.json`, `inventory-screen.json`, `pinned-verification.json`, and `topology-statement-inventory.json`;
- `retained-literature-verification.json` for all six previous PDF/text pairs;
- seven newly retained primary PDF/text pairs and `literature/manifest.json`, recording exact URLs, bytes, SHA-256, and UTC retrieval times;
- `reading-index.json`, the search log and retained search responses;
- `artifact-manifest.json`, sealing this review and its artifacts, with input and dependency references.

The exact finite novelty diagnostics passed: 6,024 skew-lattice cases, 1,036,416 all-binary no-loop checks, positive cap selections through rank eight, the Z/4 mixed-relation witness distinguishing exact classification from all-direction replication, and the codimension-one coset obstruction in B. These finite tests support the algebra in the review; they are not proofs of geometric realizability, infinite-family statements, or worldwide novelty.

From the project root:

```sh
python frontier/experiments/i07_structures_novelty_r3/reductions.py
python frontier/experiments/i07_structures_novelty_r3/seal.py --verify
```

`provenance.py` independently checks pinned-file and contract bytes and can rebuild the inventory/input records; `provenance.py --download` performs fresh primary downloads and updates retrieval timestamps, so should not be used as the retained-snapshot verification command. `seal.py --verify` checks existing artifacts and dependencies without rewriting them. A changed current external PDF does not invalidate the retained byte snapshot; compare versions and hashes before replacing it.

Only this review and the two assigned support directories were written. No agents were started; no files were staged or committed; no shared index or other project was changed. **Final recommendation: technical-only; proof PASS retained; no new accepted finding assigned.**
