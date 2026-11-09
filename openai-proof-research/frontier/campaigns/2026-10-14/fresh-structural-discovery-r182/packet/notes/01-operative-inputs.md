# Operative inputs and preserved boundaries

Provenance: Codex / GPT-6 Astra / high / default service tier. Supplied campaign context: 19/20, latestR041. Only Source322 is developed. The source and ALL operative upstream proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. This note does not audit them or assign mathematical grades.

## The complete pinned operation

The two authenticated TeX files are main.tex (35,253 bytes, Git blob ab9bd82b388ec4e55a333d05c61c853b7941798b) and references.tex (5,302 bytes, blob 796debae8df956385c1aee3398c3d578fda1cdf5). The only mathematical include is main.tex → references.tex. All 544 main lines and all 151 bibliography lines were read. Complete-tree same-family metadata shows no other TeX/Bib companion. README and the redundant compiled source PDF were not treated as required mathematical bodies.

Theorem thm:main applies to EVERY surjective sphere isometry between NONZERO REAL BANACH spaces. The positive radial extension is a surjective real-linear isometry and the unique linear extension. Arbitrary dimension, nonseparability, nonsmoothness and flat faces are explicitly included. The complex-as-real interpretation supplies only real linearity.

For an ordinary sphere isometry g, the proof uses D_q(x,y)=||g(x)-qg(y)||-||x-qy||, q∈[0,1], and M=sup |D_q|. It has D_0=D_1=0, inverse defects with opposite sign, and |D_q|≤2min(q,1-q). If M>0, an inverse if needed, maximizing sequences, a fixed limiting radius t, and a free-ultrafilter quotient followed by completion attain M while retaining the bound for EVERY pair and EVERY q. Here M/2≤t≤1-M/2. Choice is explicit; no compactness of an infinite-dimensional sphere is asserted.

For centers ty and tg(y), the unique sphere contact along each unit direction has radius in [1-t,1+t], continuous in the direction. The opposite-endpoint return g_ret is continuous because the original sphere map and its inverse are isometries and the positive radial contacts are continuous. On the attained-defect set E, s=p+M and r=u+M. Equality in the ordinary triangle inequality gives a common support for v and g_ret(v). Every direction sharing a support with g_ret(v) remains extremal. Strictly positive finite convex combinations propagate this equality. A dense rational scheduling constructs a closed bounded convex invariant C⊂E⊂S_X; C is separable, but the ambient spaces need not be.

The return estimate is

    ||g_ret(v)-g_ret(v')|| ≤ up/(rs)||v-v'||
                         +2|u-u'|/r+2u|p-p'|/(rs),
    up/(rs) ≤ (1-M/(1+t))² < 1.

Finite partitions of the scalar ranges p,u make the last terms vanish in the Kuratowski measure of noncompactness. Darbo gives an actual fixed direction. The Appendix proves convex-hull invariance of that measure, compactness of nested sets whose measure tends to zero, the simplex fixed-point result by Sperner parity, and the compact-convex fixed-point step. The required hypotheses are completeness, norm continuity and CLOSED convex bounded nonempty C, not ambient finite dimension or weak compactness.

For aligned chords, d=p+r=s+u≤2, A=p/d, B=u/d, ε=1-t and A+B=1-M/d<1. Lemma lem:secant yields ε/p≤φ(v)≤K and the two upper branches 1-B or B. In the large branch, common support signs on span{v,y}, the inverse configuration (p',s',r',u')=(u,r,s,p), and finite-dimensional dual compactness give a strict radial perturbation contradiction. In the small branch ε≤dA(1-B), ε≤dB(1-A) imply ε<1/2; convexity of ||y+λv|| and ||g(y)+λw|| contradicts an exactly preserved sphere distance. Thus M=0. Scaling then pays all cross-radius distances; midpoint-reflection doubling pays real linearity. Radial extension, uniqueness and ordinary coherent compositions of exact isometries are already paid.

For a phase-isometry, the source's equality at the opposite endpoint is NOT initially available: the target distance may be the source sum norm. Running the source return map with arbitrary sign choices would assume exactly the orientation that is missing. The developed bridge below first constructs a global ordinary sphere isometry. Only then do ALL the source operations above apply, unchanged.

## Strong actual primary constructions read

Ilišević–Omladič–Turnšek, arXiv:2005.02949v2, 13 November 2020, full paper: antipodality and injectivity; signed metric midpoint sets H; iterative half-diameter intersection recovering the midpoint up to sign; radial homogeneity up to sign; Birkhoff–James orthogonality; two-plane preservation by local midpoint propagation; and projective geometry/orthogonality rigidity. The published work is LAA612(2021)99–111. The author v2 was read, not certified byte-identical to publication. Its whole-space input includes sums, halves and unequal radii that sphere data do not provide. It is not applied to the radial extension without checking these hypotheses. Its cited planar and orthogonality results are not needed as black boxes here.

Tan–Gao, arXiv:2008.09282v2, 31 October 2020, full paper: maximal-star convexity, separable back-and-forth, paired-face correspondence, compact finite-intersection step, norming-functional values up to signs, and Urysohn-based sign consistency for C(K). These are actual operations, not just its abstract. The final radial extension already supplies linearity for that class. The global phase function is not presumed continuous.

Enami–Matsuzaki, arXiv:2603.00583v1, 28 February 2026, full 15-page PDF text: paired faces of C0, individual even sign changes, continuity on each signed face, Lemmas3.4–3.7 proving agreement on ALL signed overlaps, gluing in3.8–3.9, and the exact boundary interpolation in Proposition4.1 followed by the four-step weighted-composition proof. Its continuity argument on a face uses exact sum norm2; its triple-face witnesses use Urysohn interpolation. Those hypotheses are unavailable for arbitrary normed spaces. Its remarks about the CL-paper are attributed to that author paper; no independent verdict on the CL-paper is assigned.

Tan–Zhang–Huang's CL-space publisher theorem/intro were navigated, but full PDF access returned403 (publisher) and406 (API PDF endpoint). Thus its entire proof was NOT read or used as a premise. The complete newer C0 proof was read, including its precise signed-overlap comparison. This remains a primary-access limitation; no comprehensive literature clearance is claimed.

Martini–Swanepoel–Weiss, arXiv:0708.2900v1: actual complete Proposition31 proof in §3.5 and supporting Lemma5 proof read; pages21–22 also rendered and visually read. This is their supplied proof of the classical planar monotonicity operation. The unit-sphere case needed below has a direct two-triangle proof and is not presented as new.

Hatcher, author-hosted Algebraic Topology PDF: actual path/homotopy-lifting proof in Theorem1.7 and actual lifting-criterion/uniqueness proofs in Propositions1.30–1.34 read. Lifting depends on path and local path connectedness; these will be explicitly verified for arbitrary normed spheres. No assumption that an arbitrary quotient map automatically lifts is made.

## Original history, exceptions and immutable scopes

The seven exact completed r181 exceptions were read; a truncated combined output was recovered by separate full reads of notes02–04. Preserve its one-cell plus model, exact normal/module generator gap, all-coefficient six-cover calculation, and actual31-summand stable comparison. None supplies the unstabilized integral chain map or a finite two-model. No attempt connects those algebraic complexes to the present Banach geometry; I07/I97/r180 remain unchanged.

The eligible ORIGINAL r94 comparison-and-limits note was read in full. It records the earlier general radial ε-isometry target and its unpaid quantitative face/chord alignment. Its references to I12 are navigation only; I12's operative original was not admitted by the mandatory lexical guards. No I12 semantic read or full-history clearance is claimed. The present phase operation has exact unordered distances, no ε, and does not assert any new stability modulus or approximation by a linear map. The old quantitative target is unchanged.

Original I88's complete target section and source-contract section were read at [6225,8541) and [8541,12495), through their next equal heading. Q88 rank complexity, S88 coupled absorption/AP/no-BAP, D88 binary diamond scope remain unchanged. The statements are not silently replaced by phase rigidity. Two guarded primitive navigations found no relevant original phase-lifting body; this is a limited lexical search, not a novelty certificate.

All supplied S176A, T054L136, analytic161/T337A161 and T366A166 dispositions remain unchanged. Forbidden bodies and active peers were not inspected or used. No mathematical self-grade, acceptance or count is assigned.
