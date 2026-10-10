# I94 — relative free involutions in the parity chamber

**Disposition: technical partial theorem and an unresolved equivariant surgery target; no substantial nomination. Eight accepted findings remain eight.** This is an author proof, not an independent proof or contribution review. All pinned OpenAI statements and their lower constructions are accepted as premises at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. No upstream truth audit, inconsistency argument, or ex-falso deduction is used.

The paid result is a relative extension obstruction and a stabilization-spectrum constraint on the *actual* double-cover filling used in the aspherical four-manifold source. The unresolved step is an equivariant cancellation construction, not a new qualitative manifold-existence assertion. The finite upper bound, evenness obstruction, and monotonicity below are explicitly **technical** under the user's full-operation premise.

## 1. History, scope, and sources

The four informational ledgers were frozen under `frontier/sources/i94_topology_transformation_discovery/snapshots/`: root `README.md`, `frontier/README.md`, `frontier/TEN-FINDINGS.md`, and `frontier/iterations/README.md`. Historical entries and current status were read selectively; exact ranges are in the read manifest. No claim is made to have read every unrelated historical paragraph. The frozen current entries record I15 as technical by iterated marked-annulus replacement, I89's separate geometric-group lane, and I93's technical reduction of the independently passed Q90. Earlier “pending” paragraphs are historical, not the final status. No in-progress I91 artifact is bound or used. Neither Banach rank, symplectic packing, fluid computation nor CAT(0) finite-obstruction research is reopened.

Source abbreviations below denote **pinned originals**, not catalogue paraphrases:

- **N**: [Nonhomeomorphic closed aspherical four-manifolds with the same homotopy type, October 4, 2026](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Nonhomeomorphic-closed-aspherical-four-manifolds-with-the-same-homotopy-type-October-4-2026). Theorem `thm:pair` concerns topological, unmarked nonhomeomorphism with a common word-hyperbolic group. `thm:self-map` separately obstructs one homotopy class. Neither is a smooth-only statement.
- **PD**: [A PD4 group without an aspherical manifold model](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-PD4-group-without-an-aspherical-manifold-model-September-24-2026). It distinguishes a finite integral PD complex from a topological manifold model. Its marked stable-product operation has an existential stabilization count and hypotheses on a hypothetical closed model.
- **MT**: [A marked tensor obstruction to four-dimensional disk embedding](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-marked-tensor-obstruction-to-four-dimensional-disk-embedding-September-24-2026). The local plumbing, marked body and framing operations are relevant, as are the retained boundary and gradient-ideal markings.
- **BO**: [A boundary-only obstruction to four-dimensional disk embedding](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-boundary-only-obstruction-to-four-dimensional-disk-embedding-September-24-2026). Its stronger nonfilling conclusion does not prescribe the replacement disk classes or output framings. It supplies no positive equivariant cancellation operation.
- **CS**: [Purely Cosmetic Surgery on Knots in the Three-Sphere](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Purely-Cosmetic-Surgery-on-Knots-in-the-Three-Sphere-September-23-2026).
- **HS**: [The Hilbert–Smith conjecture in every finite dimension](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Hilbert-Smith-conjecture-in-every-finite-dimension-September-23-2026).

The complete tree was inventoried, not the truncated `sources/tree.json`: 13,223 entries, 749 manuscript directories and 10,373 blob positions. I14's ignored corpus was located by `rg --files --no-ignore` (9,340 files); the augmented I88 domain maps the additional 1,033 original positions, including 776 PDF text representatives from I79. Nothing recursively copied or redownloaded that corpus. Four full-domain lexical searches were replayed. Their broad patterns intentionally produce many irrelevant hits; zero hits for one surgery pattern are **not** a semantic novelty certificate.

The companion selection contains 129 representations in ten manuscript families: the six assigned starting families, MT, BO, the Singer paper and the October 6 Wall D(2) paper. Their inventory includes every blob in these families. The complete-tree title/version inventory finds no later same-family title for N/PD/MT/BO/CS/HS. The selected PDF representatives were re-extracted for byte comparison. This compares evidence representations, not mathematical equivalence of PDF and TeX. The read manifest distinguishes full operations, statements, excerpts and search-only files; the 129-file inventory is **not** a claim that 129 proofs were read in full.

## 2. Three precise targets after accepting the corpus

### R94: economical free realization of the actual boundary involution — selected

Use N's actual oriented chamber with `m_R=m_B=5`, choose `p=9`, install its entire marked four-tip list, and use its specified red-at-0/blue-at-1 cap choice to form the filling `V=D'_2`. Let `S=∂D`, `S_2=∂V`, and let `θ:S_2→S_2` be the nontrivial deck transformation of the connected oriented double cover `S_2→S`. The marking is `j:(V,S_2)→(P_2,S_2)`, identity on the boundary.

**Target:** construct an orientation-preserving free topological involution on

`V # 2(S²×S²)`

whose boundary restriction is exactly `θ`, where both sums are in the interior and the boundary identification remains fixed. Equality of actions up to conjugation is allowed only by a homeomorphism that is identity on `S_2`; no assertion of uniqueness of conjugacy classes is sought. A free action of the finite group `C₂` is effective and proper; the manifold and its quotient are compact with collared boundary. No smooth structure on the extension is required. This is not the weaker task of extending `θ` by a homeomorphism of unrestricted order.

This is a relative finite-group realization problem connected to Nielsen realization and four-dimensional disk embedding, and to the relative version of Wall's manifold-realization problem. It is not asserted to be an already catalogued conjecture with a score. N already constructs free deck symmetry before all middle pairs are removed. The genuine remaining demand is to retain that symmetry after removing *all but one orbit* of hyperbolic pairs, while identifying the resulting double cover **relative to the same boundary** with the specified `V#2(S²×S²)`. No read source proves this. It remains unproved and unrefuted here.

### S94: two labeled fillings determine a genus-two hyperbolic knot — screened only

For smooth nontrivial hyperbolic genus-two knots `K,J` in oriented `S³`, ask whether the two independent orientation-preserving homeomorphisms

`S³_2(K) ≅ S³_2(J)` and `S³_{−2}(K) ≅ S³_{−2}(J)`

force equivalence of the unoriented knots by an orientation-preserving ambient homeomorphism of `S³`. On each exterior fix meridian `μ` and preferred longitude `λ`; slope `p/q` means the primitive unoriented class `pμ+qλ`. Thus the displayed slopes are `(2,1)` and `(−2,1)`, of distance four. The closed fillings carry the exterior orientation. Neither given homeomorphism is required to preserve the surgery core, and no compatibility between their restrictions is assumed. This is a proposed restricted two-slope characterizing question, not a proved assertion or a named ranking.

CS solves the same-*knot*, different-*slope* problem for arbitrary oriented homeomorphisms. It does not identify two different exteriors. Its terminal genus-two reduction and the complete repetition proof in `05-stack.tex`, lines 873–1027, use the same-knot surgery chain and its cap pairing. Two separate cross-knot homeomorphisms do not supply that chain or a common peripheral identification. A new relative Floer comparison or a common core-recognition theorem is unpaid. A single filling cannot serve instead: Luecke–Osoinach's actual annulus family has infinitely many knots with a specified integer surgery, including `n=2` ([arXiv:1407.1529v1](https://arxiv.org/abs/1407.1529v1), Theorem 0.2). This does not refute the simultaneous `+2,−2` target. No complete new surgery theorem is nominated.

### H94: explicit displacement under a fixed geometric normalization — screened only

For a closed connected oriented smooth Riemannian three-manifold with `|sec|≤1`, `inj≥i₀>0`, `diam≤D`, and a nontrivial compact group acting effectively and jointly continuously by uniformly `L`-bi-Lipschitz maps, seek a specified positive formula `c(i₀,D,L)` such that some `g,x` satisfy `d(gx,x)≥c`. The assertion concerns the whole subgroup, not a lower bound for each nonidentity element. The regularity and metric constants remain in the target. No numerical formula or sharp exponent is proved here, and no claim is made that this target is new to the quantitative Newman literature.

HS's Lie conclusion and its fixed sphere denominator do not supply a numerical displacement estimate. The inspected lower lattice theorem fixes `L_d=2^{e_d}` independently of the action, but its degree tests are not a metric size estimate. Even smooth isometric actions refute a bound depending only on dimension and diameter: use flat `S¹_ε×T²` with the circle translating its own factor and normalize diameter to one. Every displacement tends to zero as `ε→0`, while the action remains effective and compact. The injectivity-radius lower bound deliberately excludes that counterexample. Classical Newman mechanisms make this lane particularly vulnerable to a technical reduction, so it is not the selected research target.

The exact [MathDB Hilbert–Smith item](https://mathdb.com/p/366196/hilbert-smith-conjecture) was found; no verified item score is assigned. The cosmetic question is linked to Gordon's conjecture/Kirby 1.81(A) in CS, and characterizing surgery to Kirby 3.6(D) in the primary annulus paper. These are problem identifications, not significance ratings.

Other assigned sources were screened at their actual statements. Cannon already gives a proper cocompact `H³` action with finite kernel, including orientation-reversing elements; standard virtual-special corollaries are already discussed there. The no-conjugate-points graph manifold uses the actual gluing `h₂=h₁+f₁, f₂=h₁` and already excludes geometric actions on nonempty proper CAT(0) spaces, not just nonpositive Riemannian metrics. Neither supplies an R94 relative cancellation, and neither is used to duplicate I89/I91. Singer concerns closed aspherical PD4 spaces, whereas R94 has boundary and, after stabilization, nonzero `π₂`. Wall D(2) concerns finite CW dimension reduction, not embedded sphere cancellation.

## 3. Exact chamber data used

For clarity rename N's number of installed bodies `b` (called `k` in its `chambers.tex`). The source's accepted construction supplies:

1. A compact connected oriented **smooth** four-manifold `D` with connected boundary `S`, a nonabelian free group `H=π₁D`, and `D ≃ BH ∨ ⋁^{2b}S²`. Its equivariant middle pairing is the sum of `b` framed hyperbolic planes. The quotient `(D,S)→(P,S)` attaches the specified three-cells and is identity on the boundary; `(P,S)` is an oriented PD4 pair and `P≃BH`.
2. A specified epimorphism `w:H→Z`, sending each plumbing generator `τ_r` to one and every `l_s,z_j` to zero. Put `H_d=w⁻¹(dZ)` and let `S_d,D_d,P_d` be the connected covers. Boundary maps `π₁S_d→H_d` are onto.
3. A particular compact oriented **topological** filling `V` of `S_2`, with `j` as above, formed by replacing all disjoint embedded punctured `S²×S²` neighborhoods in `D_2` by balls. There are **2b neighborhoods**: each of the `b` base pairs has two lifts. Hence, in the oriented topological category, relative to the identified boundary and its `π₁` marking,

   `D_2 ≅ V # 2b(S²×S²)`.                                      (1)

4. No compact oriented topological graph-type marked filling exists for `S_d` for any odd `d≥3` (N, `for:odd-nonfilling`). This is a boundary-marked nonexistence statement, not merely an obstruction to smoothing.

The complete local operation read is N `chambers.tex`, lines 1–792, including the four-tip placement, actual plumbing chart, group/sphere model, full framings, and the entire filling proof through line 785. N `cyclic.tex` 1–223 and `models.tex` 1–636 were read completely. The imported MT marked-body operation and PD marked-exterior operation were also read through their proof ends. The odd-nonfilling statement and final proof were read; its complete deformation/tensor derivation was **not** re-audited or claimed newly proved.

For (1), the embedded pairs in N are geometric, not merely an abstract hyperbolic basis. Their regular neighborhoods are explicitly punctured products. Replacing them by balls gives the actual `V`. Reversing that replacement is an interior connected sum; any boundary `S³` identification is harmless in TOP by its extension over a ball. Nothing here asserts a smooth identification for an arbitrary alternative filling.

The exact installed list has ten red and ten blue ports. Its ordered distinct `(R,B,R,B)` choices number `(10·9)²=8100`; the four independent conjugating choices give `(p+1)^4`, and the four signs give `16`. Therefore

`b=129600(p+1)^4`,  `rank H=10+p+b`.                            (2)

For the fixed `p=9` instance, `b=1,296,000,000` and (1) uses `2,592,000,000` summands. These are literal counts of this redundant source list, not a lower bound on its necessary complexity or a claim that an enormous diagram has been produced.

## 4. Paid relative obstruction: no unstabilized extension

**Proposition A (technical relative height criterion).** For the actual `(P,S,H,w)` above, let `W` be *any* compact connected oriented topological marked graph-type filling of `S_2`. There is no homeomorphism `h:W→W` whose restriction to the identified boundary is `θ`. In particular there is no such finite-order homeomorphism. No claim about a different, unmarked boundary map is intended.

**Proof.** Choose `γ∈H` with `w(γ)=1`, for example `τ₁`, and put `K=ker w`. The marking identifies `π₁W=H_2`; `W` is aspherical because it is homotopy equivalent to the graph `BH_2`. The boundary map is onto on fundamental groups. Thus `h|∂W=θ` forces the outer automorphism `Ad_γ` on `H_2`. It also preserves orientation, since `θ` does and the boundary orientation detects the orientation of a connected manifold.

Let `X=K\widetilde W`, with generator `T` of its infinite cyclic deck group corresponding to `γ²`. Its boundary is the marked infinite cyclic cover `S_∞` of `S`, and is connected. Lift `h` to `u` on `\widetilde W` so that the boundary lift agrees with the canonical action of `γ` on the regular boundary cover with deck group `H`. This is possible by choosing the image of one boundary basepoint; connectedness of that cover and surjectivity of the boundary group then give

`u g u⁻¹=γgγ⁻¹` for every `g∈H_2`.

The descended map `h':X→X` commutes with `T`. On `∂X=S_∞` it is exactly the one-step deck translation `γ`, not merely a freely chosen homeomorphism homotopic to it. This boundary normalization is the extra point needed for the relative argument.

A map `W→S¹` representing `w/2` lifts to a continuous height `t:X→R` with `t(Tx)=t(x)+1`. This height is proper: choose a compact set whose deck translates cover `X`; a bounded height interval intersects only finitely many of those translates. Compactness of `W` and `Th'=h'T` bound `|t(h'x)−t(x)|` by some `c` on all of `X`. For an integer `a>c+1` set `F=T^a h'`. Then

`0<a−c≤t(Fx)−t(x)≤a+c`.

Iteration proves that `<F>` is free and properly discontinuous. Every orbit meets the compact band `t⁻¹([0,a+c])`, so the quotient `Y=X/<F>` is compact. The boundary action is exactly `γ^{2a+1}`, hence the quotient boundary, with its orientation and identification, is `S_{2a+1}`.

The universal cover of `Y` is `\widetilde W`, and its deck group is

`K ⋊_{Ad_{γ^{2a+1}}} Z ≅ H_{2a+1}`,

by sending the new stable letter to `γ^{2a+1}` and fixing `K`. This isomorphism agrees with the original boundary marking: the lifts on the boundary have been fixed as above. Contractibility of `\widetilde W` gives `Y≃BH_{2a+1}`; the classifying map restricts to the prescribed map on `S_{2a+1}`, since maps into that graph's classifying space are determined by the fundamental-group map. Thus `Y` is the forbidden marked odd-degree filling. Taking `a` positive makes `2a+1≥3`. This proves the proposition. ∎

This proof is N's complete height operation with its boundary identification retained. It is a paid relative bridge but **not substantial** under the premise that lower operations are available. It does not use a bound on the height displacement or claim an effective estimate for it.

## 5. Paid stabilization-spectrum theorem

For the particular `V` in §3 define

`Σ(V,θ)={k≥0 : V#k(S²×S²) admits a free orientation-preserving topological involution restricting exactly to θ}`.

All connected sums are interior. No triangulability, smoothness or linearity of the involution is assumed. A free finite action gives a genuine manifold quotient and a two-sheeted covering, rather than an orbifold with fixed-point strata.

**Theorem B (author proof; technical).** There is an integer `κ` with `1≤κ≤b` such that

`Σ(V,θ)={2κ,2κ+2,2κ+4,…}`.                                   (3)

In particular the `p=9` example has an unspecified positive even threshold at most `2,592,000,000`. Proposition A prohibits *every* unstabilized extension, whereas (3) concerns **free involutions only**. It says nothing about an involution with fixed points on `V#(S²×S²)` or an unrestricted-order stable extension. R94 is the precise assertion `κ=1` for the fixed source example, not a consequence of (3).

**Proof, finite upper bound.** The deck involution on `D_2→D` is free, orientation preserving and restricts to `θ`. Transport it through (1). This gives `2b∈Σ` with its boundary map unchanged.

**Proof, upward closure by two.** If `a` is a free involution on `W_k=V#k(S²×S²)`, choose a small interior ball `B` disjoint from `aB`. Remove both and attach two copies of punctured `S²×S²` using matched gluing maps. Exchange these copies by an orientation-preserving identification agreeing with `a` on their boundary spheres, and use its inverse on the other copy. This defines an involution, is free because it exchanges disjoint pieces, agrees with the old action elsewhere, and leaves `S_2` untouched. The result is `W_{k+2}`. This is the ordinary free-orbit connected-sum operation; no novelty is claimed.

**Proof, parity.** Suppose `k∈Σ`, let `Z=W_k/C₂`, and write `r=rank H`. The boundary of `Z` is the identified `S`. There is a commutative diagram of fundamental-group covering sequences for `S_2→S` and `W_k→Z`. The left map `π₁S_2→π₁W_k=H_2` is the original surjection and the quotient maps to `C₂` agree. Consequently `π₁S→π₁Z` is onto. Its kernel is exactly the kernel of `π₁S→H`: any kernel element has trivial parity, lies in `π₁S_2`, and there the two kernels agree by the unchanged interior stabilization marking. Conversely every element of the latter kernel is trivial upstairs. Thus

`π₁Z=H`, with exactly the marked boundary homomorphism.          (4)

This avoids assuming that an arbitrary extension group with the same quotient is automatically the desired one.

The graph-type PD pair gives `H₁(S;Z)→H₁(P;Z)=Z^r` an isomorphism: by duality `H₂(P,S)=H₁(P,S)=0`, and the pair sequence applies. Therefore (4) gives `H₁(S;Q)≅H₁(Z;Q)`. The stabilized filling has `H₃(W_k;Q)=0`; transfer for the double cover implies `H₃(Z;Q)=0`. Also `H₄(Z;Q)=0` since its connected boundary is nonempty. Euler characteristic of a finite cover is multiplicative (compact topological manifolds have finite CW homotopy type), and `rank H_2=2r−1`, so

`χ(W_k)=2−2r+2k`, `χ(Z)=1−r+k`, `b₂(Z)=k`.                    (5)

Poincaré–Lefschetz duality gives `dim H₂(Z,S;Q)=b₂(Z)`. The exact pair sequence and the `H₁` isomorphism make `H₂(Z;Q)→H₂(Z,S;Q)` onto, hence an isomorphism. The intersection form on `H₂(Z;Q)` is therefore nonsingular of rank `k`.

It remains to determine its signature; it is not legitimate to multiply signatures directly for this cover with boundary. Glue along the **same entire marked boundary** to form a closed oriented topological manifold

`C=Z ∪_S (−D)`.

The boundary covers agree, so it has an oriented double cover

`C̃=W_k ∪_{S_2} (−D_2)`.

The source hyperbolic forms give `σ(D)=σ(D_2)=0`: the graph fundamental groups have cohomological dimension one, so the ordinary middle homology is the coinvariant sphere module, and augmentation gives the ordinary hyperbolic form; `V` has zero middle homology, so `σ(W_k)=0`. Additivity along a whole closed boundary gives `σ(C̃)=0` and `σ(C)=σ(Z)`. The closed topological finite-cover signature theorem yields `0=σ(C̃)=2σ(C)`, hence `σ(Z)=0`. The external input is Ranicki, *Algebraic L-theory and topological manifolds*, Proposition 22.26(ii), with the topological application in 22.27; his boundary-defect comparison on printed pp.269–270 explicitly uses the same closed-gluing distinction ([author-hosted primary text](https://webhomes.maths.ed.ac.uk/~v1ranick/books/topman.pdf)).

A nonsingular real symmetric form of rank `k` and signature zero has equally many positive and negative eigenvalues. Thus `k` is even. Proposition A excludes zero. Nonemptiness, well-ordering and the `+2` operation now prove (3), with `2κ≤2b`. ∎

The infinite topological argument is not replaced by the finite diagnostic. No extra claim about the quotient's smoothability or its integral form being geometrically standard is made.

## 6. Two serious attempts at R94

### Approach I: equivariant cancellation in the actual plumbing

Start from the known deck action on `D_2`. To obtain R94 it would suffice to find `2b−2` embedded hyperbolic pairs with disjoint punctured-product neighborhoods, permuted freely in pairs by the deck transformation, such that replacing them by balls leaves a manifold *marked-homeomorphic* to `V#2(S²×S²)`. The final relative identification is part of the required lemma. Merely computing its rank and intersection form would not establish it.

N's nonequivariant cancellation does not meet this condition. Its selection function is red at vertex 0 and blue at vertex 1. The deck transformation exchanges vertices and preserves the color of a port. Therefore it carries the selected system to the opposite selection. Each is separately disjoint; their union is not. In the source chart `(D²_R×D²_r)∪(D²_r×D²_R)`, opposite core branches meet at exactly `(0,0)` with the prescribed product framing. At each red plumbing, the union selects both endpoints of the appropriate lifted edge. The same occurs at blue plumbings. Taking both systems produces actual intersections; it is not an equivariant surgery system.

The complete four-tip list matters: at each vertex it includes every ordered pair of distinct red ports and every ordered pair of distinct blue ports, with independent paths and signs. Restricting to a small conveniently commuting subfamily changes the manifold, its normal-circle generators and boundary marking. It is not a repair on this example. In the restricted uniform-per-vertex selection ansatz, the only disjoint choices are `(R,B)` and `(B,R)`, and neither is deck-invariant. The diagnostic checks all 20 lifted plumbing edges (ten types, two lifts each), and all 8,100 ordered port quadruples. It establishes the failure of that ansatz, not the impossibility of a more sophisticated equivariant system.

An attempted repair is to add one free orbit of hyperbolic pairs and use its two geometric duals repeatedly to eliminate intersections between the two selected systems. For a single local crossing, tubing changes representatives and their group labels; repeated use must keep the auxiliary sheets disjoint, preserve every old sphere's based class, and leave the last pair available. The source's row-by-row algebraic cancellation is not a geometric Whitney-disk construction. BO/MT specifically prevent treating algebraic duals and vanishing pairings as a universal embedded-disk theorem.

**Unpaid lemma I:** on these fixed port sheets, perform the required finite family of paired Whitney moves with preserved boundary, framings and `ZH_2` labels, using only one free orbit of auxiliary product summands, and prove the marked relative complement is `V#2(S²×S²)`. No such family of Whitney disks or complement identification is supplied here. Its absence is the failure of this approach, not an upstream contradiction.

### Approach II: construct the quotient first

Every solution of R94 has a quotient `Z` with boundary exactly `S`, boundary group map exactly `π₁S→H`, `b₂(Z)=2` and `σ(Z)=0`; its double cover must be the specified `V#2(S²×S²)`. Conversely, a compact oriented topological `Z` with these markings **and that relative double-cover homeomorphism** produces the desired free involution by conjugating its deck action. The homeomorphism condition cannot be weakened to homotopy equivalence or equality of ordinary forms.

The actual base `D` already has `b` hyperbolic planes over `ZH`. Algebraically one can isolate one plane and identify the complementary free hyperbolic module of rank `2b−2`. This suggests surgering away the other planes downstairs. If one had disjoint embedded representatives with geometric duals and the right relative complement, their lifts would cancel all but one orbit upstairs. This is a quotient surgery problem with boundary fixed and nonabelian free fundamental group, not the simply connected smooth stable-isotopy problem.

The relevant primary theorem of Powell–Ray–Teichner explicitly assumes a **good** fundamental group, and geometric duals are essential for controlling the fundamental group during sphere surgery ([published 2025 primary text](https://www.maths.gla.ac.uk/~mpowell/s00029-025-01069-y.pdf), Theorem A and introduction). It cannot be invoked as an unrestricted positive theorem for this relative problem. The source PD stable-product operation was read in full: it first assumes a closed aspherical manifold model, builds a marked homotopy equivalence to it, then obtains an `s`-cobordism and finitely many stabilizations. It does not give a prescribed count, a relative filling of this boundary, or a finite-order extension. Its eventual periodicity over a deck subgroup is not descent of a product through the missing involution.

Auckly–Kim–Melvin–Ruberman's [arXiv:1406.4937v2](https://arxiv.org/abs/1406.4937v2) is also insufficient: its Extension Lemma 2.3 requires actual disjoint framed disks with a specified handlebody complement. Its “1-stably symmetric” definition even distinguishes an extension automorphism from an involutive extension. Their particular blown-up cork constructions do not give such disks or that complement on N's graph-type chamber. Their ordinary smooth cork category is not interchangeable with topological nonextension here.

**Unpaid lemma II:** construct the relative quotient with the necessary residual hyperbolic plane, and identify its double cover relative to `S_2` with the chosen stabilized filling. A stable isometry, a normal bordism, an existential stable homeomorphism or an enumeration with no output bound does not pay this lemma. Neither a construction nor an obstruction at `k=2` was found.

These approaches expose different obstacles: the first has explicit competing geometric representatives but no equivariant simultaneous cancellation; the second isolates the desired quotient algebraically but lacks its relative geometric realization. They are not two independently proved theorems.

## 7. Validation, contribution limits, and evidence contract

`frontier/experiments/i94_topology_transformation_discovery/diagnostics.py` is a read-only standard-library finite diagnostic. It enumerates the actual two-vertex color selections and port quadruples, tests the formula for `b`, checks rational homology/signature parity bookkeeping over finite ranges, and checks free-group conjugation identities on a Schreier basis for the index-two subgroup. These tests can catch an orientation, multiplicity or arithmetic mistake; they cannot certify topological surgery, existence of an equivariant Whitney system, or novelty.

The author proofs of A and B are complete at their stated scope under the stipulated source operations and the cited classical finite-cover signature theorem. Their contribution status is **technical**: A retains a boundary condition in N's height quotient; B combines N's full local cancellation, a classical signature-defect comparison, homology bookkeeping and the ordinary free-orbit sum. No source-derived finite upper bound is counted as substantial. R94, S94 and the explicit H94 estimate remain unpaid; the latter two were screened, not exhaustively researched.

The evidence package has its own snapshots, exact read ranges and original-reference hashes. Every range is one-based inclusive in UTF-8 text decoded with replacement and Python `str.splitlines()`; LF-based `rg -n` offsets are not substituted. The Ranicki PDF has a duplicated extraction layer, and `splitlines()` also splits form feeds/control characters. Initial mistaken LF-offset readings were corrected before any manifest was sealed. The actual Proposition 22.26 range is 15408–15430 in the recorded extraction, and page 254 was rendered and inspected. The read manifest binds the corrected complete statement/proof endpoint. No incorrect offset is represented as a successful read.

The verifier is offline and READ-ONLY: no network, downloads, repair, reseal, source writes or bytecode. It verifies the exact owned inventory, every immutable input, every original Git blob identity and search-representative hash, the I14 ignored inventory, all four search outputs, selected-family completeness, exact passage hashes, selected PDFs and all four new primary PDF extractions, the retained rendering, and the finite diagnostics. It permits drift **only** in the four informational originals listed above; their owned snapshots must remain fixed. It preserves all earlier sealed artifacts. It binds but does not re-extract every one of the 776 inherited PDF representatives; only the ten selected-family PDFs are re-extracted here. Full-domain lexical replay is not a full semantic audit, and PDF replay is not proof verification.

Run from the research root:

```bash
PYTHONDONTWRITEBYTECODE=1 python -B frontier/experiments/i94_topology_transformation_discovery/verify.py
```

Preseal validation is run before the one final `seal.json` is created. The sole excluded owned file is that declared seal itself; report, scripts, snapshots, source records and diagnostic output are all sealed. No postseal edits are allowed. A final read-only run validates the seal. The final handoff supplies its SHA-256; the report does not embed its own circular hash.

**Evidence verdict:** mechanically reproducible at the verifier's exact bounded scope. **Mathematical verdict:** author-level technical A/B, independent review pending. **Research verdict:** the useful unresolved bridge is marked equivariant cancellation on the actual two-color chamber; no substantial ninth finding is claimed, and no worldwide priority, human peer review or formal certification is asserted.
