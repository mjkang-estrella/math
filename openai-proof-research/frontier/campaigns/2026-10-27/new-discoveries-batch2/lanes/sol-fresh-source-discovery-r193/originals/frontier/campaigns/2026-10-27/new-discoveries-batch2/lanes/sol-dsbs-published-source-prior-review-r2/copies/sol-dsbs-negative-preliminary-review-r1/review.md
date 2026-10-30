# Independent preliminary review: negative-order DSBS separation

Review date: 30 October 2026 UTC. Candidate: `sol-fresh-source-discovery-r170`, PROOF.md SHA256 `2e44d1b6a01fad0f61ca5fa601569178e95abb3e3a11b33715e78cdca861acde`. This is an ordinary-mathematics review, with no acceptance or count recommendation implied by a mathematical PASS. Nine additional /39 total, next40 remain root's state.

## Separate verdicts

* **SOURCE: PASS for the identified arXiv target and exact quantifiers; published-version coverage incomplete.** Conjecture1/eq19 is the sufficiently small epsilon, sufficiently large beta strict-separation assertion. The proposed every `0<epsilon<=2^-10`, every `beta>=1` including infinity proves that assertion if the proof is correct. It does not prove a sharp threshold at 0.0551. The nontrivial relaxed-Wyner input is explicitly attributed, not a new result here.
* **MATH: PASS at ordinary proof level**, using the published mutual-information-region theorem / source Proposition1 as an input. I find no missing mathematical bridge to the stated endpoint. Detailed independent checks and an explicit deduction of the needed Proposition1 branch appear below. No diagnostic is treated as a proof.
* **SUBSTANTIVE: qualified positive preliminary assessment, with a serious adaptation objection retained.** This is more than a numerical parameter instance or merely formalizing a public endpoint. The code-dependent posterior/tensorization converse is not supplied by source IV-A or by a direct substitution in the closest fixed-channel theorem. Its proof is classical and short; that fact alone does not exclude it. The actual complete classical route is laid out below so root can adjudicate routine status. This verdict is not permission for large formal investment while the source/prior gap persists.
* **NOVELTY: HOLD, bounded evidence only.** No exact prior proof was identified in the read primary bodies and inherited qualified registry evidence. I positively identified the fixed-channel companion's 2025 journal publication, but could not compare its VoR body. Nor was the 2023 mutual-information paper's VoR compared. These are specific coverage limits, not a demand for impossible global priority certainty. Historical capped merge/OpenAI-tree gaps remain PARKED, not cleared.
* **FORMAL-FEASIBILITY: feasible in principle, substantial missing infrastructure; no endpoint certificate.** In particular, the nontrivial DSBS mutual-information-region / relaxed-Wyner theorem must itself be proved in the allowed kernel environment. Assuming it as an axiom or as a hypothesis of the final source endpoint would not satisfy this campaign. No Lean build was run.

## Actual sources, versions, and priority limits

The cached actual bodies consulted are Yu arXiv:2407.06132v1 (8 July2024), definitions eq6–11, Theorem1 eq14–15, Conjecture1 eq19, Proposition1 eq20–21 and its branch/derivation, IV-A–C and AppendixC; Yu arXiv:2402.07660v5 (7 June2025), fixed-channel formulation, Theorem3 eq42–44 and AppendixD; and Yu arXiv:2212.14696v2 (6 July2023), the mutual-information-region definitions, Theorem2 and its lower-envelope formula eq8. Original HTML, extracted bodies, failures and existing source provenance are in the private input copy. This is a relevant theorem/proof-body review, not a claim of an exhaustive line-by-line audit of every unrelated theorem in the long companions or the reconnaissance sources.

Fresh primary metadata retrievals at 03:16:30 UTC confirm unchanged main v1 and companion v5 abstract pages, byte-identical to the candidate's retained pages. Main arXiv has no journal reference; a fresh Crossref title query returned no exact main-paper journal match. That is an identification limit, not a proof of no publication. The companion is **IEEE Transactions on Information Theory, August2025, DOI10.1109/TIT.2025.3578324** (Crossref exact title match). The mutual-information paper is **IEEE TIT69(10)(2023)6251–6268, DOI10.1109/TIT.2023.3293616**. Version5's arXiv comment says proofs of Lemma11 and Theorem5 are omitted from the published version; this is an author statement, not my independent VoR comparison. IEEE stamp requests for article11029606 and10177210 returned HTTP418 at03:16:44 UTC; both were stopped, with no alternate-route retry or bypass. URL/time/hash records are in `live-sources/`.

The inherited exact original-history audit records no earlier qualified target in that audited history. It does not establish literature novelty. I did not reconstruct capped histories, repeat denied GitHub/ScienceDirect/Google routes, chase heads, send messages, or use a browser. Current metadata and qualified inherited screens do not constitute a fresh complete global proof-registry clearance. No worldwide priority claim is justified.

## Adversarial check of the full converse

Let `beta>0`, `c=(1+beta)/beta`, fully supported finite target pi, and `E=D_(1+beta)(pi^n || P_n)`. Finite E forces P_n positive everywhere. Thus any Q, including one with zeros, satisfies Q^n absolutely continuous with respect to P_n and pi^n. All expectations in the finite-block argument are finite. Terms on zero Q mass are omitted. Infinite E blocks cannot occur arbitrarily late in an achievable sequence tending to zero after normalization.

For `R(z)=T(z)^(1+beta)V(z)^(-beta)/Z`, direct expansion gives

`D(S||V)-cD(S||T) = log(Z)/beta-D(S||R)/beta`.

The coefficient is c, not beta/(1+beta), and the coefficient of the last KL is 1/beta. Consequently `D(Q^n||P_n)<=cnD(Q||pi)+E`. The negative-order skew symmetry multiplies reverse divergence by `-beta/(1+beta)`; convergence to zero is still equivalent. Keeping its sign is essential.

Transporting exactly the original seed posterior preserves the Q^n marginal. Cancellation proves equality of joint and marginal KL, not just an inequality. Conditioning instead on the seed yields

`D(Q^n||P_n)=D(Qhat_M||Unif)+I_Qhat(X^n;Y^n|M)+E_M[D(Qhat_X|M||A_M)+D(Qhat_Y|M||B_M)]`.

Every positive transported joint mass has positive original joint mass. A component processor may have zeros even though the mixture is fully supported; the displayed decomposition remains valid. Arbitrary internal coordinate dependence of A_M and B_M is allowed. The candidate never assumes it away.

For `U_i=(X_i,Y_i)`, `W_i=(M,U_<i)`, productness of Q^n gives

`sum I(U_i;W_i)=sum[H(U_i)-H(U_i|M,U_<i)]=I(U^n;M)<=log M`.

For the other direction, `H(X_i|M,U_<i)<=H(X_i|M,X_<i)` and the analogous Y inequality. Summing and subtracting the unchanged joint entropy chain proves `sum I(X_i;Y_i|W_i)<=I(X^n;Y^n|M)`. The conditional mutual information inequality direction is correct. Uniform independent J makes `W=(J,W_J)` feasible for `C(Q,cD+E/n)`, while `I(U_J;J)=0`. Neither equality needs the transported M to remain uniform.

Cardinality/right continuity also survive scrutiny: represent each conditional XY law by `(d-1)` marginal coordinates, its CMI and its joint entropy, a continuous map into R^(d+1). Its compact convex hull has representations with at most d+2 atoms. Both the objective and constraint are preserved. On the fixed finite auxiliary simplex optimizers exist, and subsequential limits prove right continuity at every `t>=0`, including t=0. Thus each achievable rate R is at least `C(Q,cD(Q||pi))` for every Q. Infimizing achievable rates preserves this lower bound. For a strict separation one first fixes a witness Q with value strictly above Wyner; it is not necessary to have a uniform-in-code or uniform-in-beta gap.

**Broader implication checked:** for finite beta this is exactly the supremum in source eq14, since `1-1/alpha=1+1/beta` at alpha=-beta. Combining the source's achievability with this converse would yield `Ttilde_alpha=T_alpha=Gamma_alpha^UB` for fully supported finite targets and finite negative alpha. For order negative infinity the direct variational inequality `D(S||V)-D(S||T)<=D_infinity(T||V)` gives the analogous argument with c=1. Alternatively continuity in c plus compact optimization recovers it. These observations warrant scrutiny and attribution checks; they are not a second independently credited nomination. No extension to targets with zeros has been verified here.

## Independent check of the exact relaxed-Wyner branch

The source's alternative optimal-distribution prose is inconsistent as printed: at t=0 its q=q0 is generally smaller than its b=(1-sqrt(1-2r))/2, so `(q-b)/(1-2b)` is negative. That purported Bernoulli parameter cannot be used. The candidate correctly uses eq20–21, not that prose.

Here is an independent bridge from the underlying region theorem. Time-share a law W|XY with its X/Y-swapped version and include the independent selector in W. This preserves gamma=I(XY;W) and the residual CMI, and makes alpha=I(X;W)=I(Y;W). Write v=h^(-1)(1-alpha), and a=(1-sqrt(1-2r))/2. On the diagonal, the lower envelope in Theorem2/eq8 becomes

* for `v>=a`, `g(v)=(1-r)[1-h((v-r/2)/(1-r))]` (region D1);
* for `v<a`, `g(v)=1+h(r)-2h(v)>w(r)` (region D2).

For D1 put `q=(v-r/2)/(1-r)`. Then `gamma>=g(v)` and `CMI=gamma-2alpha+1-h(r)>=F(r,q)`. As v goes from a to1/2, q goes from q0 to1/2, F increases from0 to1-h(r), and g decreases. Indeed

`F_q=2(1-r)h'(v)-(1-r)h'(q)`.

To check its sign put z=1-2q, so 1-2v=(1-r)z. Positivity of F_q is equivalent to `2 atanh((1-r)z)>atanh(z)`, equivalently `2(1-r)/(1+(1-r)^2 z^2)>1`. This holds exactly when `z^2<(1-2r)/(1-r)^2`, that is q0<q<1/2. At q0 the derivative is zero. F is not globally convex on this interval; only its local quadratic minimum is needed later. Hence `F<=t` forces `q<=q_t`, and gamma>=g(q_t). D2 cannot improve that value because g>w(r)>=g(q_t). This proves the needed lower bound from the nontrivial region theorem, with no reliance on the erroneous Bernoulli prose.

For attainment take W uniform binary, W|X=Y equal to X flipped with probability q, and W|X!=Y uniform. Direct calculation gives `I(XY;W)=(1-r)(1-h(q))`, `I(X;W)=I(Y;W)=1-h((1-r)q+r/2)`, and CMI=F. Thus the exact formula and the branch used by the candidate are independently reconciled with the underlying theorem.

## Taylor step, signs, and explicit range

With `a(1-a)=r/2`, `q0=a^2/(1-r)`, one obtains `F=F_q=0` at q0 and precisely `F_qq=4(1-r)^2(1-2r)/(r^2 ln2)>0`. The factor of2 in the quadratic expansion is correctly canceled against the factor of2 in the binary-KL quadratic expansion. At each fixed e>0, derivatives are uniformly controlled for r in a compact neighborhood of e and q near q0(r). Dividing F by `(q-q0)^2` and taking its positive continuous square root proves the stated one-sided inverse expansion. There is no need for a remainder uniform as e approaches0.

The entropy objective then has slope `A(e)-sqrt(c)B(e)` with exactly the displayed A and B. On `0<e<=2^-10`, `s>31/32`, `A>log2(7/4)>3/4`; `sqrt(e)log2(2/e)` is increasing there, so `B<(4/3)(11/32)=11/24`. With c<=2 and sqrt2<3/2 the slope is strictly greater than1/16. These are analytic interval bounds, not consequences of sampled numerics. One may choose a sufficiently small delta separately for each e and beta. For negative infinity, `D_infinity(pi^n||P_n)>=D_2(pi^n||P_n)` implies inclusion of achievable-code classes in the required direction, hence `Ttilde_-infinity>=Ttilde_-1>w(e)`.

## Strongest substantive objection and its limit

The complete classical route is: finite Renyi variational identity; seed-posterior KL decomposition; ordinary entropy chain rules and conditioning monotonicity; finite-dimensional support reduction/right continuity; the public exact DSBS region theorem; a quadratic local perturbation; elementary interval bounds. Every step to the literal endpoint is now specified. No new credit is due for the region theorem, individual entropy identities, the numerical interval, or the stronger general equality separately.

The closest concrete public theorem is fixed-channel companion Theorem3 eq42–44: for fixed memoryless K it optimizes `max_Q min_{Q_input|output : D(Q_output|input||K|Q_input)<=cD(Q_output||target)} I(input;output)`. Replacing that channel KL by CMI is suggestive but not a valid substitution for all synthesis codes: their A_m,B_m can correlate coordinates and vary with n and m. Optimizing one fixed single-letter product-output channel only bounds a restricted family of codes. Treating each complete block processor as a channel letter would change the channel and alphabet with n, so the fixed-channel asymptotic theorem cannot be invoked unchanged.

The precise missing bridge in that direct public-theorem argument is a uniform code-independent converse for these changing channels. The candidate supplies it through the posterior and W_i construction checked above. Source IV-A gives only the Wyner lower bound and contains no such construction. Thus I do not find a complete *published theorem substitution* exclusion. A reviewer may still reasonably judge that this new bridge is a standard strong-converse adaptation; root should decide on the demonstrated mathematical content, not on shortness or the author's conjecture label alone. Pending the VoR/prior gap, I do not recommend claiming established new-to-literature status.

## Formal feasibility and verification boundaries

Read-only local library inspection used the mathlib checkout under `frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib`, configured revision `d13f23b723b8a846827a245b89c10fc7d3f11612` (configuration read; no git verification). Actual bodies provide `InformationTheory.klDiv` in ENNReal, `klDiv_compProd_left`, `klDiv_compProd_eq_add`, `klDiv_map_le`, finite PMF constructions, binary entropy facts, and convex Caratheodory infrastructure. This is useful support, not a ready finite Shannon/CMI/Renyi/source-code API. Natural-log conventions require conversion to bits. Totalized real log at zero must not silently replace infinite KL.

Required new work includes finite distributions/kernels with support-aware KL; entropy, MI and CMI chain rules; the arbitrary finite block posterior construction; independent-coordinate tensorization; Renyi variational identity and negative/infinite orders; the source's literal infimum over all code sequences; d+2 auxiliary reduction and right continuity; then the full nontrivial DSBS mutual-information-region result or an independent proof of the exact relaxed-Wyner lower bound. The last requirement is likely the largest task: an explicit feasible binary W proves only an upper bound and would be useless for this converse without the matching lower bound. A theorem conditional on that input is not a full source certificate. Local Taylor/inverse estimates can avoid an abstract inverse-function theorem by factoring F at its quadratic minimum. This remains a substantial formal project.

All94 frozen original files were independently checked and copied. The original91-record scientific freeze and92-record final manifest are checked separately at closure. Candidate diagnostics were replayed in the private copy and output is byte-identical. My separate checks use12 exact-rational posterior constructions, including zero processor entries, with exact marginal identities; KL decomposition and tensorization are evaluated at75-digit precision, and four local derivative/slope controls plus rational bound arithmetic are checked. The entropy/KL calculations remain high-precision diagnostics. Two local setup/check failures and truncated read-output deviations are preserved in provenance; no resource cap was raised. Original and private-copy after-hashes and the independently checked final manifest accompany this report.
