# I225 reading and failed routes

## Scope

Work stayed in `/home/mj-kang/Documents/Dev/math/openai-proof-research`. Only the assigned I225 files and explicitly page-limited primary excerpts were written. No subordinate agents, live other-agent outputs, shared-ledger edits, research code, numerical experiments, tests, commits, staging or publication. Inline Python was used only for retrieval, PDF text extraction and provenance hashes. Existing pinned-source copies were reused. `input-authentication.json` records exact files, scopes and pinned blob identities.

Read `AGENTS.md`, `sources/upstream.json`, and catalogue entries 356–360. Read the focused opening and MTW discussion (lines 1–100) of the historical report `frontier/iterations/i07-analysis.md`; its relevant outcome is that deriving smooth transport by asserting cut separation was not paid. Focused searches in historical iteration reports found no prior substantial result for 356 or 357. That scoped search is not a worldwide novelty claim.

## Three-family screen, no substitution

1. **356, distributional sectional curvature and Alexandrov comparison.** Read the actual introduction of the characterization and the whole introduction of the Hessian-along-every-geodesic companion. The latter already turns a bounded Lipschitz function's distributional Hessian bound, with bounded continuous upper coefficient, into the corresponding inequality on every minimizing geodesic. Merely transporting convexity or triangle-comparison consequences through this theorem would be a standard transfer. No quantitative defect-to-chart theorem was extracted.

2. **357, open bi-Lipschitz charts.** Read the actual introduction and the precise lower interfaces `co:cumulative-comparison`, `pi:directional-pinching`, `re:metric-iteration`, and the beginning of `re:limit-chart` through its scale choices. The main theorem has dimension-only `L_n` but a point-dependent neighborhood. The catalogue summary's wording about a point-dependent finite constant was not used in place of the theorem. The source already constructs charts from cumulative positive matrix forms and summable directional defects; ordinary dyadic GH summability is also prior art (Gigli–Violo v1, Theorem 2.6). No radius depending only on dimension, Ricci bound and regularity of one point was assumed. No analytic regularity of the final chart components was assumed.

   In `co:cumulative-comparison`, `C_*` depends on `n,A_0,C_0,L,J`; these enlargement and overlap parameters are fixed before taking a late rescaling. In `pi:directional-pinching`, `L,C_sep` are fixed first. In `re:limit-chart`, the fixed `D` is chosen from previously obtained jet/metric constants, then the normalized harmonic approximation error and tail are made small at that fixed ratio. There is no explicit rate converting the initial regularity of one point into that late rescaling. Replacing these steps by a guessed uniform radius would not be justified.

3. **360, weak MTW.** Selected as the main lane after the early screen. Read both actual introductions, the entire Hölder paper's density-free interface section, its scalar gap definition/power reduction, and its whole conclusion; read the foundation's full proof of intermediate regularity. The strongest attempted result is Q in `analytic-attempt.md`. Two different routes were pursued: global dual-gap coercivity and intermediate-time regularization/density comparison.

## Failures that mattered

- Treating the already-proved power section bound as a new stability mechanism fails the contribution gate: Gallouet–Merigot–Thibert has the abstract modulus transfer, and Kitagawa–Letrouit–Merigot already has general-manifold quantitative stability without MTW.
- Confusing squared map distance with map norm changes exponents by a factor of two. KLM v2 (1.5) has exponent `1/6` for the squared integral, hence `1/12` for its square root. The I225 target asks for exponent one on that squared integral. No ambiguous “one-half stability” is used without specifying the norm.
- In the pinned power bound, `beta,C_0,r_0` are uniform only for fixed geometry and density bounds and are nonexplicit. No superiority to KLM's exponent has been inferred.
- Inferring quadratic cost-gap growth from spatial bi-Holder regularity fails in the explicit power-map model. That model fails the positive target lower bound, so it does not settle Q.
- Inferring uniformly positive intermediate density or uniformly elliptic transport derivative from endpoint density bounds fails the displayed determinant-one anisotropic matrix test. The matrix test has not been promoted into a global fixed-manifold counterexample.
- Taking `t` to one in `Q_tu` with fixed constants is not licensed: the displayed upper/lower Hessian estimates have denominators `t` and `1-t`, and the local quadratic-growth construction gives `b_t` proportional to `1-t` after shrinking a radius with no stated rate.
- A near-conjugacy tail estimate obtained merely from integrating a semiconvex Hessian would be a standard trace/Markov transfer. It was considered but not developed into a nomination.
- New results in family 357 cannot be invoked for transport potentials merely because both use matrix normalization. The required harmonicity and directional Bochner estimates have not been verified for those potentials.

## Primary reading retained

All five new `.txt` copies are precise PDF-page excerpts and were read completely. No full PDF or unread full-paper copy is retained. The primary-source index states URLs, page limits and use. Failed attempts to request nonexistent GMT HTML versions v2/v3 were corrected by inspecting its abstract page: arXiv has v1. The actual v1 PDF was then used. No mathematical claim relies on the failed HTML requests.

## Disposition

No substantial finding is nominated. The report preserves a fully proved standard consequence and a precise unpaid coercivity estimate so that a parent can assess a future genuinely new approach without treating the present work as either a proof or a disproof of Q. The parent retains both independent gates.
