# Arithmetic/algebraic discovery r81 — prefreeze archive

No target was frozen, no candidate is nominated, and no mathematical gate, contribution rating or campaign count is assigned. All pinned OpenAI statements and operative proof operations are stipulated true at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. This round did not truth-audit them. The calculations below are selection/feasibility work, not replacements for any earlier frozen target.

The sustained screens concern source053 tautological relations, source209 integral/coefficient Gersten detection, and source050 metric exclusion. Additional actual historical screens concern sources195,199,200,052 and256, at the unequal extents recorded separately. The complete tree was parsed and all 13,223 entries traversed; the truncated root tree was not used. Arithmetic r80's report, research and reading limits were read, and its three supplied detached anchors matched. Its196/019/059/031 operations were exclusions, not reopened targets. The active152 mechanism and the explicitly excluded source families were not worked on.

## 053: direct removal of markings has a formal alternation obstruction

The actual `thm:main`, `def:candidate`, `def:pixton-span`, `prop:known-relations` and `prop:detector` matter here. Put

    g = 10^60, D = binom(g,3), n = 3D, r = binom(g-1,2).

The source class Y has codimension 2D and is alternating under the group K=(S_r)^g permuting occurrences of each color. Its nonzero detector value is ±(r!)^g times the ordered product of all exterior cubic generators. The bridge correction is killed because the test is supported on rational-tails graphs. The original Pixton span already includes outer insertions and is stable under multiplication and gluing/forgetting pushforwards and pullbacks. Treating it as merely the unclosed list of seed formulas would give the wrong novelty comparison.

Arithmetic r11's entire screen053 was read before these calculations. It already identifies fewer markings and new-relation ideal generation as distinct ambitions, and records the detector's degree/arity cutoff. It does not give the calculation below. No new full conjecture was frozen on the strength of that absence.

Consider the formal map π_* from the n-pointed strata algebra to the unpointed one, and a polynomial α in the n leg ψ-classes and the permutation-invariant global κ-classes. All operations here are formal graph operations, not merely Chow operations: saying that the Chow image vanishes would be vacuous since q(Y)=0 already.

For homogeneous α of weighted degree a, equivariance and the alternating character of Y give

    π_*(αY) = π_*((Alt_K α)Y),
    Alt_K α = |K|^(-1) sum_(σ in K) sign(σ) σ(α).

An alternating polynomial in the r ψ variables of one color is divisible by their Vandermonde polynomial. This follows by setting any two variables equal, observing that the value changes sign, and using unique factorization over Q; the distinct linear differences are pairwise nonassociate primes. Applying this in each color shows that a nonzero Alt_K α has degree at least

    A = g*r*(r-1)/2.

The available degree before global dimension truncation is only

    B = (3g-3+n) - 2D = 3g-3+D.

Since D=gr/3, A-B = gr(3r-5)/6 -3g+3. Already for g≥5, r≥6 and this is at least 10g+3>0. Thus if a<A the alternation is zero; if a≥A then αY exceeds the dimension and is zero in the strata algebra. Every such formal decorated-forgetting output is zero, including sums of homogeneous α.

This rules out only this direct ψ/κ decoration method. It does not rule out boundary decorations, adding markings, gluing positive-genus components, other formal detectors, or an unpointed counterexample. In particular it is not a refutation of the proposed broader phenomenon and is not nominated as a result.

### Stronger compatible reduction checked: genus-tagged tails

Before declaring removal of labels genuinely unpaid, I tested the standard gluing/self-intersection method against actual primary operations. The relevant primary texts are [Pixton1207.1918v1](https://arxiv.org/pdf/1207.1918v1), Proposition1; [Graber–Pandharipande, math/0104057v2](https://arxiv.org/pdf/math/0104057v2), AppendixA, Proposition9 and formula(11); and [Faber–Pandharipande, math/0002112v1](https://arxiv.org/pdf/math/0002112v1), §0.4 and Theorem1 with the first proof in §1.2. Janda–Pixton1304.0026v2 §2 gives a further explicit pairing comparison. These bodies were read at the extents in reading-limits.md; abstracts were not substituted for them.

The feasibility calculation uses a star gluing with root of type (g,n), one one-pointed tail for each label, and tail genera h_i≥2 chosen with

    h_1>g, h_j>g+sum_(i<j)h_i.

The resulting genus is G=g+sum h_i and there are no external markings. On tail i the classical test is

    α_i = λ_(h_i) λ_(h_i-1) ψ^(h_i-2),
    c_i = integral_(Mbar_(h_i,1)) ψ α_i ≠ 0.

The nonzero c_i is exactly the one-point version of the Faber–Pandharipande κ_(h_i-2) integral, by the definition of κ and the projection formula. The Hodge product restricts to zero on the entire boundary of this one-pointed tail. On a nonseparating boundary the top Hodge class vanishes from the trivial residue quotient. On a separating boundary both genera are positive (there is only one marking), Hodge splitting and λ_a²=0 give zero. These are credited Hodge identities, not new positivity inputs.

If one pulls the gluing output back to the star and pairs the tail factors with α_i, the diagonal excess factor is

    product_i (-ψ_i - ψ'_i).

Only the term using -ψ'_i at every tail survives integration: α_i has degree one below that factor's dimension. Its coefficient is the nonzero scalar (-1)^n product c_i, multiplying the original root class. The test does not require a nonzero Chow value of Y on the root; one retains the root formally and uses its formal detector (or a functional on the root quotient).

The crucial compatibility question is other generic refinements, rather than this diagonal scalar alone. In the primary's actual (A,B)-graph formula, a refinement in a tail factor is supported on that tail's boundary and is killed by α_i. If all those factors remain unsplit, a second cut representing a genus-h_j leaf must select exactly the h_j vertex: the genus inequalities exclude every collection of smaller leaves plus any part of the root, and exclude larger leaves. Adding a nonempty genus-zero piece from the root would create an unmarked genus-zero tree with only two external half-edges, impossible for stable vertices (sum(valence−2) would be zero instead of positive). The corresponding cut is therefore the original leaf edge. The specified cuts identify the root markings, removing a spurious symmetrization that would kill Y. Automorphisms of the distinct-genus star introduce no permutations of these cuts.

Finally, pulling back a Pixton relation lands in the sum with a relation in one factor. A root relation is killed by the root detector; a tail relation is killed by the actual Chow integral, since it is Chow-valid. This uses precisely the full product-valued stability contract, not a mere stability statement for scalar classes.

This prefreeze calculation checks the obvious stronger alternative to naive forgetting. It is an application of the existing full excess-intersection and Hodge pairing operations with genus separation; Graber–Pandharipande §4 also explicitly uses self-intersection and a surviving Künneth component to retain nonmembership under gluing. Their published theorem concerns nontautological cohomology, not this exact formal-Pixton statement, and I do not claim a verbatim duplicate. Equally, absence of the exact unpointed headline is not evidence of an unpaid operation. I did not identify an additional compatibility task beyond these already available contracts. Accordingly no unpointed target was frozen or proposed for contribution review. This is a selection disposition, not an independent theorem/contribution verdict. No claim of finite generation failure of the whole relation system is made.

## 209: nondivisibility is already source-paid; the broader detector remains limited

The complete degree-three source was read. Its `thm:main` already says more than nonzero integral generic kernel: there is c∈K3(A), with c|Frac(A)=0, whose restriction to A[1/π] has nonzero mod-five reduction. Its introduction expressly concludes c∉5K3(A). Thus a proposed nonsaturated-image or finite-coefficient strengthening is already stated, not an unpaid refinement.

The exact operations are also important. Here L=Q5(ζ5), π=1−ζ5, A is the regular local ring of the quintic at m=[0:0:1], S=A/(y), and D=Frac(S). The source constructs β with coefficient boundary [ζ5], uses (1−t)^5=ζ5 and the integral Steinberg identity to kill the boundary of β_D[t], lifts to K3(D), then lifts across the DVR S because K2(F5)=0. Support kills the integral generic restriction before any detector is used.

`lem:field` gives the full isomorphism θ_E:E*/E*5→K3(E;Z/5) for every finite E/L, and `lem:norm-detector` identifies transfers with norms. `lem:opens` retains every point specializing to m in the filtered localization. All omitted points have residue degree divisible by five, whereas the distinguished point has N(t)=π. This is an all-coefficient transfer statement, not just a calculation on specially selected symbols.

The degree-five companion's introduction and complete main proof were also read. It already uses a Picard-valued test after character-square-weighted splitting: the scalar valuation sum 1+4+4+1 is zero modulo five but the elliptic orbit yields 4Q≠0. Thus retaining positions rather than only norms is itself already a stronger source operation. The intervening arithmetic/specialization proofs were not newly read in full; no new theorem is based on extending them.

The closest external primary inspected is [Feld2608.05005v2](https://arxiv.org/pdf/2608.05005v2). Proposition4.3 and Corollary5.1 distinguish coefficient kernel, vanishing Bockstein, and integral generic vanishing. Its integral lift becomes divisible by three in the fraction field, and integral K2 injectivity prevents interpreting it as an integral kernel. The proposed general odd-prime statement in Remark5.2 is explicitly unproved there. It is not adopted as a theorem.

I tested whether the scalar norm method could supply many independent mod-five detections at the fixed degree-three model. The common norm quotient over all finite E/L of residue degree divisible by five is only the valuation line. Indeed norms have valuations divisible by five. Conversely the unramified degree-five extension has norm-surjective units: the residue-field norm is surjective, and on successive principal-unit quotients the induced map is the residue trace, which is surjective; successive lifts converge in the complete DVR. Its uniformizer norm has valuation five. Consequently the quotient of L*/L*5 by these norm images is F5, detected by valuation. This is classical local norm algebra, not a new kernel-rank theorem. It constrains detectors required to annihilate all such transfers; it does not say every such extension occurs at an omitted point of every particular localization.

For rational nonvanishing, a compatible higher-power tower, many independent local kernels, or even-degree local survival, the source's one coefficient value is insufficient. No one of these was frozen as a headline. The actual Gersten recovery bodies were read: the moving point y=z defeats the iterated coefficient norm detector, but does not prove integral class vanishing; the cohomological reduction leaves res(α) cup(z) after further localization unproved. Its original G4 is not replaced here by the nonlocal Bass suspension or by a restricted coefficient statement. No new localization-survival mechanism was found.

## 050: the strongest history already gives the uniform barrier

The complete source `prop:limit` proof was read. It works for arbitrary positive-rank G and preserves a finite Hermitian quadratic on every fiber. It includes trace through the branch locus, a frame exponent2/m, coefficient compactness, fixed-test noncollapse, radial convolution, polarization at every point, and overlap identification. The graph obstruction was read through its ruling-reduction proof and the beginning of the logarithmic curvature proof; the remaining obstruction is a stipulated source input, not a newly audited argument.

An initial feasibility calculation considered twists P^a with a/m→0. Before any freeze, the complete arithmetic r15 checkpoint was read and found to contain the stronger answer: one δ>0 excludes every semipositive metric on f_m*G⊗P^a whenever a/m<δ, for every positive integer m and every integer a≥0. Its actual argument uses frame factor |u|^(2a/m), handles a=0 directly and forces unbounded m in a putative sequence with positive a. It also proves failure of approximate Griffiths semipositivity on G itself. The initial sublinear-twist thought adds nothing to this full antecedent. The time of this discovery is disclosed: after first feasibility, before any frozen bytes or candidate proof.

Structural r29's complete source050 screen was also read. Its rank-four P2 transfer retains ramification, finite duality/direct-image ampleness, a fixed twist and the quotient curvature metric. The new base alone does not leave an unpaid operation. These are controlling authored bodies, not author ratings used as mathematical evidence.

[Raufi1211.2948v2](https://arxiv.org/pdf/1211.2948v2) was read at Definitions1–2 and the introduction through Theorem1.1. It distinguishes negative singular metrics defined by psh squared norms from curvature-current existence, the latter requiring a determinant lower bound in that theorem. I did not infer a smooth curvature tensor or uniform eigenvalue lower bound for the source's rank-deficient limiting quadratic. R15's actual DPS and later-primary comparison is inherited exclusion context; those further original papers were not newly acquired/read in this round.

## Other actual-history screens and decision

The complete r37 source199 screen was read: its induced symmetric module has stable endomorphism ring k[ε]/ε², not a stable brick; the full degree-zero rectangular cone calculation leaves sums of the same module. Thus scalar/matrix or ordinary spherical-twist variants were not selected. R28's complete source200 screen provides a concrete failure of Betti-tail rigidity and credits I226's integral consecutive cancellation. I31's first235 lines include the full-section-ring persistence proof, primitive canonical-weight deformation and Euler obstruction through the main nonconicality argument; that is much stronger history than a title suggesting only an isolated example. No new no-MCM deformation was proposed. The source052 multiple-summand and source256 torsion-free-equation histories were located by content matches only, not reread completely; those remain navigation exclusions, not operative primary clearances.

There is no frozen full target to weaken or repair. The most concrete new diagnostic is the formal alternation degree obstruction. The stronger tail test was checked against an existing compatible gluing mechanism rather than ignored. The arithmetic and metric screens were closed at selection by actual stronger source/history operations. None is a nominee. The primary search is bounded; no priority exhaustion is asserted. Parent review/integration decisions are untouched.

Public files contain original prose/code; upstream, external-primary and retained historical bodies are private under their original rights. No nested agents, browser UI, git/staging/PR operations, contacts, publication, shared-index edits, formalization or manuscript work occurred. The detached verifier authenticates bytes and membership only.
