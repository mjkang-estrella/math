# I272 independent CONTRIBUTION review of I271

**Verdict: TECHNICAL.** I271 genuinely removes every initial orientation-closeness hypothesis and supplies an implication missing from I266. It is a useful global fixed-profile corollary. Under the stipulated sharp exponent family, however, its entire additional scope reduces to an explicit one-variable optimization, followed by the already validated local estimate. No exact published duplicate is established, and no full proof-gate verdict is issued.

Target: `frontier/iterations/i271-global-fixed-profile-channel-stability.md`, read completely, SHA256 `a3ecaddeec1745579ca729e7d2d1e9067c9d97006169a1df0eedfa1361fb54fa`, matching the assigned identity. Its complete analysis, read log, authentication and literature were read. The completed I264 statement, I265 proof review and analysis, and I266 contribution review, analysis, read log and literature were read in full. All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. This review is independent of author response and of live sibling output.

## Statement assessed and prior decisions

Fix a>0 and 1/2<gamma<3/2, r=(gamma-1/2)^(-1)>1. Keep w=(r+1)a²sech²(ra x) and normalized phi=c sech^(1/r)(ra x) fixed. For every finite m>=2 and every measurable REAL unit orientation v, set

    H=-d² I_m-w vv^T,
    J=inf_(real |e|=1) integral w phi²[1-(v.e)²],
    D=a^(2gamma)-Tr H_-^gamma.

The claimed comparison cJ<=D<=CJ has constants depending only on a,gamma and no initial bound on J, pointwise angle, support, variation or derivatives. It is global in orientation, with fixed scalar profile, center and scale. Complex orientation fields, infinite channels, arbitrary profiles, interacting occupied solitons and endpoints are outside it.

I265 PASS remains a correctness decision on I264's LOCAL weighted-J theorem, including its tau. It is not a PASS on I271. I266 TECHNICAL remains the contribution decision on that local theorem. I266 already derived globally

    J/(r+2+J/a²)<=delta:=inf spec(H)+a²<=J,

but its full-tail absorption required J small. It did not infer small J from small D. I271 is a new, unreviewed all-orientation scope in the same chain; this review does not dismiss it as a duplicate local count or overturn prior decisions.

## The new implication works at the mechanism level

Write d=delta/a² in [0,1]. If d<1 every binding energy E_j is at most a²(1-d). The actual pinned matrix theorem applies at EACH s in (1/2,gamma), so

    sum E_j^gamma <= [a²(1-d)]^(gamma-s) C_s integral w^(s+1/2).

The beta integral cancels the Gamma factors in C_s. With q=s-1/2, the dimensionless cost is

    (r+1)^(q+1) q^q/[r(q+1)^(q+1)].

Independent differentiation confirms F(gamma)=F'(gamma)=0 and F''=1/[q(q+1)]. The integral Taylor remainder on q>=1/(2r), with gamma-s=d/(2r), gives I271's exact k0=(r+1)/[2r(2r+1)]. The resulting D>=a^(2gamma)(1-exp(-k0 d²)) is uniform in m and all orientations. The zero-moment and endpoint cases can be handled directly. No optimizer assumption at the comparison exponent is needed.

There is an even shorter comparison. Optimize the same bound exactly: its unique minimizing exponent is

    s*=1/2+(1-d)/(r+d),   0<d<1.

Substitution gives

    Tr H_-^gamma/a^(2gamma)
        <=(1+d/r)(1-d)^(1/r).                       (E)

This is the minimum of the available upper bounds, not a claim of attainable sharp stability. Since log(1+d/r)<=d/r and log(1-d)<=-d-d²/2,

    D>=a^(2gamma)[1-exp(-d²/(2r))]
      >=a^(2gamma)(1-exp(-1/(2r)))d².

The analytic derivation of (E), the candidate's constants, and the global projection comparison are in `frontier/experiments/i272_global_fixed_profile_contribution/analysis.md`. No code or numerical checks were used for these deductions.

In particular J<=Z=2(r+1)a²/(r+2) and the I266 comparison imply D>=A J² with explicit A>0 independent of m. Thus for every epsilon>0 there is a positive full-deficit gap on J>=epsilon, simultaneously over all finite dimensions. This is the missing implication: extra bindings cannot compensate enough for a lowest-energy loss to make the full moment nearly optimal. Neither strict equality by itself nor I266's small-J tail estimate proves it.

The remainder is a direct promotion. On J<=tau use the exact I265-validated local lower bound. On J>tau use D>=A tau J. For the upper bound, delta<=J and the mean-value theorem work on J<=a²/8; elsewhere D<=a^(2gamma)<=8a^(2gamma-2)J. This covers the actual all-orientation quantifier rather than merely smooth perturbations.

## Primary comparisons and overlap limits

Fresh pinned raw bytes of the matrix introduction and four equality sections were matched to the retained I266 identities and fully read. The matrix `thm:main` supplies the entire sharp exponent family, ordinary trace and finite-dimensional measurable class. The equality `thm:main` and `rig:factorization`/`rig:partner` supply scalar saturation and the gap. Its `act:quantitative-action` and `comp:relations` retain auxiliary defects and obtain exact-equality rigidity; `comp:tail-bounds` has an m factor. They do not themselves state this physical J estimate or a dimension-uniform near-equality theorem. Exact pinned URLs and extents are in the literature record.

[Carlen–Frank–Lieb, Theorems 2.2 and 5.1/Lemma 5.3](https://arxiv.org/html/1301.5032v2) supply scalar ground-state stability and the familiar local-to-global compactness strategy. They do not control rotating matrix orientations or the full negative moment. Their global promotion is methodological precedent, not a theorem subsuming I271.

[Leng, Theorem 1.2](https://arxiv.org/html/2606.03749v1) gives scalar ground-state stability using normalized potential densities. Those densities are unchanged when only v rotates in w vv^T, so that scalar distance cannot detect J.

[Read–Schulz v2, Proposition 4 and (2.1)](https://arxiv.org/html/2609.10478v2) gives sharp operator-valued control at gamma=1. It does not supply a sharp family below every target gamma or a J remainder, so that theorem alone cannot replace I271's essential tangency input.

[Hundertmark–Laptev–Weidl, Theorem 3.1 and Corollary 3.5](https://arxiv.org/pdf/math-ph/9906013) provide operator-valued endpoint control and beta-integral lifting of moments. That lifting shifts the spectral threshold and integrates; I271 instead uses a bound on E_max and minimizes the exponent. The two arguments should not be identified.

[Frank–Gontier–Lewin, Theorems 1 and 5](https://arxiv.org/pdf/2109.05984v2) address scalar finite-rank maximizing sequences, bubble decomposition and endpoint multisolitons. Their N is spectral rank, not I271's channel dimension. They are relevant to the broader optimizer geometry, not a direct fixed-profile matrix stability contract.

Current bounded searches located these primary comparisons but established no exact duplicate. Search absence is not evidence of novelty. Only the extents actually read are used; no full-paper or worldwide-priority claim is made.

## Why TECHNICAL rather than the alternatives

There is a real new inference, and dimension uniformity matters. An unsupported assertion that equality plus compactness automatically promotes the theorem for every m would be inadequate. A short classical-method proof can also be substantial when it resolves a new structural difficulty. The assessment here does not turn on proof length, the word “global,” or an obligation to prove a larger theorem than the one stated.

The concrete reason for TECHNICAL is that the fixed profile has already paid the nonlinear geometry: I266 controls J globally by the scalar lowest-energy displacement. The only remaining issue is whether the full moment can approach equality with that displacement bounded away from zero. The stipulated sharp exponent family answers this by the exact scalar envelope (E), with no new compactness theorem, channel analysis, tail decomposition or equality extraction. The familiar local-plus-positive-gap case split then gives the whole announced comparison. This positive reduction covers every new quantifier, not just individual classical ingredients.

KNOWN would require an authenticated duplicate or a read theorem directly supplying the conclusion; neither was found. UNRESOLVED is unnecessary for the contribution judgment because the mechanism is explicit and checks analytically. SUBSTANTIAL is not supported as an increment beyond the stipulated results and the already reviewed local chain: this is an explicit global corollary of that infrastructure. This does not call the theorem false or erase its useful removal of a hypothesis.

No substantive obstruction remains in the claimed fixed-profile promotion at this level of review. A presentation repair is to make the corollary status and sharp-family dependence explicit, credit I266 for the global projection comparison, and use (E) to expose the reduction. Improving a nonoptimal quadratic coefficient alone would not change the contribution judgment. A possible substantive extension would survive variable profiles or several occupied channels, where the nearby-exponent costs and ground-state geometry are no longer fixed. That is a future direction, not an authorized candidate change or an extra correctness demand here.

This is one spectral chain and no second finding. The target remains twenty substantial findings, ten accepted; no count, candidate, acceptance, ledger or shared index was changed. The review does not issue I271 proof PASS, certify its optimal constants, or appeal I265/I266. Authentication, exact read extents, access failures and detached output identities accompany this report.
