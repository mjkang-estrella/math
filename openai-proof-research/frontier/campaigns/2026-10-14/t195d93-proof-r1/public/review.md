# T195D93 independent correctness review

Verdict: **PASS**, for the full original frozen statement, conditional on the expressly stipulated pinned OpenAI statements and operative proofs. There is no blocking correctness issue or required mathematical repair. This verdict concerns correctness only; it assigns no contribution, substantiality, acceptance, or campaign count. Parent authentication was used to identify the reviewed bytes, not to endorse their mathematics. No contribution-review brief or contribution review was inspected.

## Statement actually reviewed

For every smooth integral projective surface X over C, every ample globally generated Cartier divisor H, and the full section ring T=⊕_{n≥0}H⁰(X,O_X(nH)), put n=T_{>0} and R=completion of T_n at its maximal ideal m. For every nonzero finite reflexive R-module M, of arbitrary positive rank r,

    length_R H²_m(M) is finite, and
    length_R H²_m(M) ≥ r max{0,(K_X²−2c₂(X)−3H²)/24}.

The coefficient is exactly 1/24. The review imposes no proportionality of K_X and H, grading, algebraizability, rank or denominator bound, HN-length bound, semistability of M or its extension, asymptotic qualification, or replacement of the given lattice by a favorable surrogate. It proves no effectiveness, equality classification, nonconical extension, lim-CM assertion, or positive-characteristic analogue.

The reviewed author proof is `fresh-arithmetic-discovery-r93/packet/public/proof.md`, SHA256 `b05e2ea21ed2d31c1521e9ef32c38358c335c1beb6278459834adab9c864ebf2`. The frozen statement hash is `ac626f4ab8d04589a8709854b9407f4577b72cdada161e6fe5f7943b7fa87572`. All paths named below are resolved from the author metadata, not guessed from a manuscript title.

## Stipulated source contract and its precise use

The operative source is [source195, build/paper.tex at the pinned commit](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Complete-Local-Domain-Without-a-Small-Cohen-Macaulay-Module-September-23-2026/build/paper.tex). Its Git blob is `df6c3550b6fa6866034f792a2f53941b6a3e6703` and retained SHA256 is `76d8de92a9ef5850d2f6f185812051aeedfa100885f96fe93ef9cd7b5d94dea0`.

Its printed `thm:obstruction` assumes an MCM module and concludes Δ≤6h, where Δ=K_X²−2c₂(X) and h=H². It does not itself state the finite-defect theorem. The following stronger operative contracts in its proof are stipulated and have the needed scope:

* §2 `sec:cone`, `eq:completion`, and `eq:conormal`: finite projection f:X→D=P², h=deg(f), the full-ring completion R=T⊗_S A for A=C[[x₀,x₁,x₂]], and ordinary regular integral Noetherian models W and V, with W finite over V and proper over Spec A. Their exceptional divisors are X and D, their complements are the actual punctured spectra, and J=g*I with I|D=O_D(1), J|X=O_X(H). The proof explicitly treats section rings not generated in degree one. R is a normal three-dimensional complete local domain, regular off m.
* The §2 double-dual restriction argument, after punctured local freeness is established, gives a coherent extension ℰ with torsion-free positive-rank restriction to X. The argument uses local depth and a Cartier equation; it does not require the module itself to be MCM once punctured freeness has been supplied.
* §3 `lem:balance` and `eq:transform`: for a torsion-free ℰ with torsion-free restriction, the last-HN-quotient transform preserves the punctured bundle and gives 0→G(H)→ℰ'|X→ker(P→G)→0. The arbitrary-offset version is explicitly supplied by actual r83, and is also checked below.
* §4 `eq:layers` and `eq:Tor`: actual Cartier quotient layers, their finite rank capacities, and the derived-restriction identity. The printed `lem:lattice` is a trivial-punctured-bundle statement. The review does not misquote it as a bound for a nontrivial atom: the changed-reference calculation is proved separately below.
* §5 `lem:factor` and `eq:RR-variance`: for every torsion-free H-semistable G of rank u, the pushforward has rank uh, mean μ(G)−K_X.H/(2h)−3/2, and variance at most 1/4−Δ/(12h). These statements have arbitrary-surface scope. Their square completion uses the rational class c₁(G)/u−K_X/2 and Hodge index; it does not require K_X proportional to H.

The source's special surface construction and existential no-MCM example are unnecessary to this theorem. Source truth was not audited. In particular, neither source195's MCM-to-A-free step nor its zero-defect lower bound is applied directly to an arbitrary reflexive M.

## Reduction of the actual module to a finite defect

The additional finite-flatness assertion is valid. A finite morphism from the smooth surface X to the regular surface D is flat by the local Cohen–Macaulay parameter criterion (miracle flatness). Equivalently, at each base stalk, the finite semilocal pushforward of O_X has a regular parameter sequence, hence is free by Auslander–Buchsbaum. Its rank is the generic degree h. Base change gives finite flat g and, on the complements, finite flat U_R→U_A. This does not assert that R is free over A at the closed point.

Reflexivity of M over the normal R implies torsion-freeness and S₂. For a nonmaximal prime of R, its regular local ring has dimension at most two; reflexivity and Auslander–Buchsbaum therefore give freeness, including the dimension-zero and dimension-one cases. Thus M determines a vector bundle on U_R. Its finite flat pushforward is a vector bundle on U_A of rank N=rh. The underlying finite A-module E is A-torsion-free. At the origin its depth is at least two because the extension of the maximal ideal of A has radical m, so the corresponding local cohomology vanishing is the same. It is S₂ at all other primes by punctured freeness, hence reflexive over A. Since A is regular of dimension three, pd_A(E)≤1.

The module T_E=Ext¹_A(E,A) is finite and supported at the closed point, so its length L is finite. Local duality for A with normalized dualizing complex A[3] gives D_A(H²_n(E))=T_E: the usual completion on Ext is redundant here. Local cohomology of a finite module at the maximal ideal is Artinian, so Matlis biduality recovers H²_n(E) from this finite-length dual and preserves length. Radical independence identifies this module with H²_m(M). Both A and R have residue field C; a finite-length module's length over either ring is its C-dimension. Consequently

    L = length_A Ext¹_A(E,A) = length_R H²_m(M).

There is no factor h in this length conversion. The h occurs only in N=rh. The classical contracts were checked against [Stacks 0AAK, local duality](https://stacks.math.columbia.edu/tag/0AAK) and [Stacks 090V, Auslander–Buchsbaum](https://stacks.math.columbia.edu/tag/090V); they are not part of the stipulated OpenAI axiom merely because they are standard.

On W, ℰ=(p*M̃)** agrees with M̃ on U_R. At a nongeneric point of X, the coherent dual has depth at least two over the regular local ring of W. Quotient by the nonzerodivisor defining X leaves depth at least one; at the generic point it is free over a DVR. Thus ℰ|X is torsion-free of rank r. This verifies the exact extension interface used by the source. Its finite pushforward g_*ℰ is torsion-free since g is dominant between integral schemes. None of this descends M to a graded or algebraic module before completion.

## Exact syzygy orientation, multiplicity, and dual atom

A free resolution 0→A^b→A^a→E→0 dualizes to

    0→E*→A^a→A^b→T_E→0.

Thus E*, rather than E, is a second syzygy of the actual defect T_E. Take a composition series of T_E of length L, with all factors C. Resolve each factor by the Koszul resolution of the regular parameters. At each horseshoe step the free modules in degrees zero and one are direct sums of the outer terms. First taking the kernels of the degree-zero augmentations, then the kernels of the resulting degree-one surjections, gives exact sequences of first and second syzygies. The resulting second syzygy Z therefore has a filtration with exactly L factors Ω²_A C. No minimal-resolution or number-of-generators substitution is being made.

Twice applying Schanuel to the two presentations through degree one gives finite u,v≥0 with E*⊕A^u≅Z⊕A^v. To make the comparison explicit, if the other presentation is 0→Z→Q₁→Q₀→T_E→0 and the first uses P₁=A^a,P₀=A^b, the second Schanuel identity is

    E* ⊕ Q₁ ⊕ P₀ ≅ Z ⊕ P₁ ⊕ Q₀.

All projectives here are finite free because A is local. Restriction to U_A makes all factors locally free. Dualization there is exact, reverses the filtration, and gives L factors (Ω²_A C)* together with v free line factors in the bundle E|U_A⊕O^u. Reflexivity identifies E** with E. Necessarily N+u=2L+v. If L=0, the same statement reduces to stable freeness and contains no atom; no exceptional case is lost.

The second Koszul syzygy is ker(A³→A), with row (x₀,x₁,x₂). On V, division by the local exceptional equation turns this row into the tautological quotient ρ*O_D³→ρ*O_D(1). Its kernel is ρ*Ω¹_D(1); the apparent change of local equation only changes the target trivialization and not the kernel. Its dual is precisely

    ρ*B,  B=T_D(−1)=Ω¹_D(2),

on U_A. This fixes both the dual orientation and the twist. The conormal I is canonically trivial on U_A. There is no assertion that the original E is pulled back from D.

## Every-lattice atom inequalities

Put Φ(F)=2ch₂(F)−c₁(F) for coherent sheaves on D; c₁ and ch₂ are their numerical coefficients. This is additive for arbitrary coherent exact sequences, including torsion terms.

For B, the Euler sequence gives rank 2, c₁=1, ch₂=−1/2, hence Φ(B)=−2. Its slope stability is proved without importing a classification. A saturated rank-one subsheaf has torsion-free quotient; the depth lemma on the smooth surface makes its kernel reflexive, hence a line bundle O(d). If d≥1 it would give a nonzero section of Ω¹(2−d). For d=1 the map on sections C³→H⁰(O(1)) in the Euler sequence is an isomorphism; for d≥2 the preceding line-bundle sections vanish. Thus d≤0<1/2. The other atom O is semistable of slope zero and Φ(O)=0.

Fix either atom B₀ and a torsion-free coherent lattice K on V for its given punctured pullback. Under that identification, clearing denominators on finitely many affine charts gives a≤−1 and q≥0 with

    I^(q+a)ρ*B₀ ⊂ K ⊂ I^aρ*B₀.

Both inclusions are genuine lattice inclusions, since the sheaves are torsion-free. A sufficiently negative a only enlarges the reference lattice; it does not twist K. The quotient Q=I^aρ*B₀/K is killed by a power of I. Its finitely many layers Q_j are quotients of B₀(a+j), so 0≤n_j=rank Q_j≤rank B₀. Semistability applied to the torsion-free quotient of Q_j gives

    c₁(Q_j) ≥ (μ₀+a+j)n_j.

For full-rank quotients the same inequality holds (the kernel of a generic isomorphism from a bundle to a torsion-free quotient must vanish). For rank-zero layers the assertion is c₁(Q_j)≥0. In all cases, the discarded torsion has effective divisorial first Chern class and zero-dimensional torsion has c₁=0. Thus no hidden local freeness of the layers is needed.

The positive conormal sign is essential. Multiplication by the Cartier equation is injective on both K and I^aρ*B₀. For Q_j supported on D, Tor₁^V(Q_j,O_D)=Q_j⊗I|D=Q_j(1). Additivity of derived restriction therefore gives

    [K|D]=[B₀(a)]+Σ_j([Q_j(1)]−[Q_j]) in G₀(D).

Since Φ(Q(1))−Φ(Q)=2c₁(Q), this implies

    Φ(K|D) ≥ Φ(B₀(a))+Σ_j 2(μ₀+a+j)n_j.

The restriction K|D may contain torsion; G₀ additivity and the torsion estimate already account for it. At the generic point of D it has the atom's rank because K is free over the regular DVR there.

For B₀=O, Φ(O(a))=a²−a, μ₀=0, and capacity n_j≤1. The negative coefficients occur at 0≤j<−a, and their full sum is −(a²−a). The lower bound is 0.

For B₀=B, Φ(B(a))=2a²−2, μ₀=1/2, and capacity n_j≤2. For the same indices the coefficients are 2a+1+2j, whose capacity-weighted sum is −2a². The lower bound is −2.

Discarding nonnegative terms and filling every negative slot minimizes the relaxed affine expression; no existence or independent gluing of optimizing quotient layers is assumed. These are bounds for EVERY K with the specified punctured bundle.

## Saturation, restriction, and stable cancellation on the same lattice

Let ℒ be any torsion-free coherent lattice for E|U_A on the actual V. Apply the stable punctured isomorphism to ℒ⊕O_V^u. For each subbundle in its punctured filtration, take its generic vector subspace and intersect with ℒ⊕O_V^u. On a Noetherian affine chart this intersection is a submodule of a finite module and is finite. Localization commutes with the intersection with a fixed fraction-field subspace, so the local constructions glue coherently.

Each intersection is saturated: if a nonzero function times a local section lies in the generic subspace, the section itself lies there. Its quotient in the ambient lattice is torsion-free. Successive quotients are torsion-free too, as they embed in the corresponding ambient quotient. On U_A the intersection recovers the original subbundle because its original quotient is locally free. Consequently the successive quotients are actual lattices for exactly L copies of ρ*B and v copies of O.

For every successive quotient K_i, the Cartier equation is a nonzerodivisor. Thus Tor₁^V(K_i,O_D)=0, and restricting every filtration sequence to D is exact. This is the justification needed to sum the atom inequalities; merely taking unrelated extensions of the punctured factors would not suffice.

Additivity now gives Φ((ℒ⊕O_V^u)|D)≥−2L. Both stabilizations have zero cost: the v free factors in the filtration contribute lower bound zero, and the u summands on the left contribute exactly Φ(O_D^u)=0. Therefore

    Φ(ℒ|D) ≥ −2L                                      (A)

for EVERY ℒ extending E|U_A. No bound on u,v, r, L, or filtration length is needed. This proves the full stable-defect/same-lattice interface. It does not rely on any additional hypothesis about algebraization, a split filtration, or a favorable choice after balancing.

## Actual HN transforms and the final coefficient

Let b=K_X.H/(2h)+3/2 and c=1/4−Δ/(12h). Begin with the extension ℰ already constructed. An integer twist by J makes μ_max(ℰ|X)<b+1 without changing the punctured bundle. If μ_min<b, take the last HN quotient G and perform the source transform. Its new restriction is an extension of the preceding HN subobject by G(H), hence torsion-free. Both pieces have maximal slope strictly below b+1, so this strict upper bound persists. The average increases by rank(G)/r≥1/r at each step. Because it stays below b+1, only finitely many steps are possible. If P is semistable and is itself the last quotient, the kernel piece is zero and the same argument simply twists its restriction by H. Termination puts all actual HN slopes in [b,b+1).

This is the full arbitrary-offset fixed-interval argument already in actual r83 `slope-budget.md`, not a return to the weaker 6h threshold. Every twist and transform preserves the actual bundle on U_R. At the end, still call the sheaf ℰ and let P=ℰ|X. Exact finite pushforward and J=g*I give the sheaf identity

    F=f_*P=(g_*ℰ)|D.

Indeed, push forward 0→Jℰ→ℰ→i_*P→0 and use the projection formula for the invertible I. The lattice ℒ=g_*ℰ extends the same E|U_A as at the start; it is exactly a lattice covered by (A).

For the actual HN factors G_i of P, with rank u_i and w_i=u_i/r, source `lem:factor` gives

    m_i=c₁(f_*G_i)/(u_i h)=μ(G_i)−b ∈[0,1),
    v_i=2ch₂(f_*G_i)/(u_i h)−m_i² ≤ c.

The arbitrary-canonical-class term is already controlled by the stipulated factor proof: if C=c₁(G_i)/u_i−K_X/2, its remaining quadratic contribution is C²/h−(C.H)²/h²−K_X²/(4h), at most −K_X²/(4h). No numerical proportionality is silently inserted.

Exact pushforward and additivity, with N=rh, now imply

    Φ(F)/N = Σ_i w_i(v_i+m_i²−m_i) ≤ c,

since m_i²−m_i≤0. Combining this upper bound with (A) for THIS F gives

    −2L ≤ Φ(F) ≤ rh/4−rΔ/12,
    24L ≥ r(Δ−3h).

The earlier finite-length identity and L≥0 yield exactly the full frozen formula. If Δ≤3h, the asserted lower bound is zero and remains valid; no hypothesis of a positive numerical obstruction is needed. All ranks and all finite HN lengths are retained.

## Primary comparisons and dependency boundaries

[Chen 2609.24142v1](https://arxiv.org/pdf/2609.24142v1), Main claim 1.1, assumes K_X≡4H and 15h/8−χ(O_X)>0 and proposes the same deficiency lower bound in that specialization. Its §6 is expressly a proposed proof. The identity with the present formula is exact: Noether's formula gives Δ=3K_X²−24χ=48h−24χ, so (Δ−3h)/24=15h/8−χ. Its Lemmas 2.3–2.5 address reflexive restriction, punctured freeness and finite deficiency. Proposition 3.3 proves fixed-interval normalization. Proposition 4.3 uses the stated slope interval and canonical slope 4 to bound both tails; it cannot be extrapolated to arbitrary K.H/h. Proposition 5.1 controls the entire kernel from the fixed source H¹(X,F), using the filtered quotient F(sY)/F and eventual injection to the puncture, not just kernels of individual transition maps. These are real retained operations, but no truth stipulation for Chen or general two-tail extension is used in the proof reviewed here.

[Anghel 2609.15589v1](https://arxiv.org/pdf/2609.15589v1), Theorem 1.1, states the aCM-bundle obstruction h≥K_X²−8χ=Δ/3. Its §2 uses finite projection, Horrocks splitting, the exact slope conversion, RR/Bogomolov/Hodge index and majorization; Theorem 1.3 concerns graded modules. These statements do not grade an arbitrary completed-local module. The author proof uses neither that shortcut nor an unsupported preservation of semistability under finite pushforward.

[Horrocks, Construction of bundles on Pⁿ, Astérisque 71–72 (1980)](https://smf.emath.fr/system/files/filepdf/AST_1980__71-72__1_0.pdf), printed pp.197–198, supplies the projective stable-filtration/exterior-tangent antecedent. It does not literally state the local arbitrary-lattice bound (A). The local horseshoe/Schanuel argument and its exact L multiplicity were checked directly above. OCR of the old displayed projective theorem is imperfect; its precise multiplicity formula is not a premise of this review. The unacquired Evans–Griffith Ch.5 Thm.5.2 is navigation only. BHM2410.18372v2 supplies no imported lim-CM assertion.

Actual r83 is credited for the full nongraded zero-defect Δ≤3h threshold and the arbitrary-offset interval operation. Selected actual I28/I31 model and gluing/construction passages were inspected only to identify the older operations and boundaries; their nonconical theorem is not a premise of T195D93 and has not been re-reviewed here. No contribution comparison is assigned a score or verdict.

## Reading, provenance, chronology, and failure limits

I read repository AGENTS.md and sources/upstream.json; full author HANDOFF.md and REPORT.md; and full public FROZEN.md, proof.md, comparison.md, freeze.json, reading-limits.md, report.md, reproduction.md, other-screens.md and rights.md. I inspected the actual parent terminal-status, intake and replay records solely as provenance/integrity records. They contained no prior correctness verdict. I did not read its contribution brief or the contribution-review output.

I read the source195 main paper in bounded passes, including the exact theorem statements and the full operative model, extension, balancing, lattice and factor sections and its conclusion. The separate `surface.tex` and other-family source bodies were not semantically read; their hashes were checked. The metadata lists were parsed in full to resolve retained paths. The complete 13,223-entry canonical tree was parsed and hash-checked; `sources/tree.json` was not used.

I read the retained Chen text through §§1–6, including Props.3.3/4.3/5.1 and the proposed assembly; only the beginning of §7 was incidentally displayed. I read Anghel's exact Theorem 1.1, relevant scope distinctions and §2 through its numerical conclusion/defect identity. I read Horrocks's printed pp.197–198 via the retained text. Primary PDF/text hashes were verified, but I did not render the PDFs or independently redownload them. Formula use here rests on legible text and the direct algebraic checks above, not on an unparsed OCR equality. BHM and the rest of the Horrocks volume were not semantically read. The complete r83 slope-budget body was read. I28 §3 model passages and selected I31 §§1–2,5–7 passages were inspected; one oversized history display clipped a short portion of I31, and no complete historical theorem audit is claimed.

The initial combined catalogue/public-metadata display was oversized and truncated. Required author documents and the missing primary statement/conclusion portions were recovered in smaller displays; full semantic reading of the large catalogue or every other-family document is not claimed. An initial Horrocks extraction using Python splitlines landed on earlier pages because form feeds affect that numbering; a literal search located the actual article and printed pp.197–198 were then read. A directory-existence check returned absent before this review directory was created. These display/navigation failures were not treated as mathematical evidence. There were no failed control cases and no numerical mathematical tests. Online primary checks of the two Stacks tags succeeded; browser UI was not used.

The author discloses substantial prefreeze calculation of the full formula, syzygy route, atom budgets, saturation and cancellation. Actual r83 was discovered after initial feasibility but before the freeze at 2026-10-19T12:19:06.549004Z. The full proof followed at unchanged scope. This review preserves that disclosed chronology and does not manufacture an earlier freeze or erase late reads. It does not independently certify session timing from filesystem timestamps. Search inventory hashes and bounded snippets do not establish complete semantic reading or worldwide priority. No priority claim is made.

## Independent artifact controls and disposition

The separately written `public/code/verify.py` does not import or execute author code. It is read-only, requires a detached FINAL hash, checks the exact author packet manifest and metadata/body contracts against the complete external tree, and prints its result. It was inspected before execution. `public/code/controls.py` runs this verifier against the original and disposable full copies located only inside this review directory. All six supplied author detached anchors matched.

The original passed: 94 payloads, 60 directories, 22 canonical bodies, four primary PDF/text pairs, 28 history copies and five context copies. All 14 control cases had the expected results: baseline acceptance and rejection for wrong anchor, changed/missing proof, extra file/directory, symlink, changed mode, hardlink, changed manifest/report, plus separately reanchored copied canonical-metadata, Git-blob and freeze-receipt corruption. Those last three are deliberately new test anchors, not alternatives to the authenticated author anchor. Every copied input was unchanged by verification. Full original paths/types/bytes/modes/link counts and the external complete tree were unchanged across the run; the disposable copies were removed. Detailed receipts remain private.

These observations are artifact checks only. Neither the author's seal nor the verifier seals the manifest's own mode or the exact root-level extra-file inventory; the independent before/after snapshots separately establish preservation. The audit hook denies specified write/mutation/process events, but no denial probes or hostile-runtime/race guarantee is claimed. Artifact success is not a mathematical gate.

The review's original prose/code and public metadata are separated from private snapshots/receipts and all third-party material. All writes, scratch and disposable copies stayed under `t195d93-proof-r1/`. No nested agents, author/shared-index edits, staging, commits, resets, PRs, contacts, uploads, publication, browser UI, or downstream formal/manuscript/release work occurred. Parent integrates. Campaign18/20 and publicationSTOPPED remain unchanged by this correctness review.

**Final correctness disposition: PASS for full original T195D93. No blocking issues or required repairs.**
