# Terminal dimension reduction in real Lp — full author theorem, technical assessment

Status: full author proof assembled; author-side TECHNICAL / no nominee. Independent proof and contribution gates were not run. The unchanged scope in original-scope.txt is retained. Supporting lemmas, history indexing, and the complementary assembly packet are not separate findings. No acceptance or contribution count is asserted.

For every fixed p in(1,infinity), p!=2, and D>1, there is C_{p,D}<infinity such that every n-element set T in any real Lp(mu), n>=2, admits a map F of the entire ambient Lp(mu) into l_p^d, where

 d <= exp(C_{p,D}(log n)^gamma(p)),
 gamma(p)=2-p for1<p<2 and gamma(p)=1-2/p forp>2,

and one common scale s>0 such that

 s||t-x||p <= ||F(t)-F(x)||p <= D s||t-x||p

for every t in T and every ambient x, simultaneously. In particular d=n^{o(1)}. No ambient-dimension, aspect-ratio, finite-query-set, or measure-space restriction is imposed. No linearity, measurability, continuity, efficient evaluation, or query-query distortion statement is added. p=2 has established primary terminal-JL theorems and is not proposed as a new contribution.

The proof consists of the complete arguments in profile-cover.md and assembly-proof.md, both integral parts of this packet, followed by the single stipulated source invocation below. The first is an all-p bounded distance-profile covering theorem: actual representatives from arbitrary constrained query subsets, polynomially many in the number of tested terminals. The second is a complementary author proof by /root/analytic_r29_recovery_astra, copied byte-for-byte with hash/provenance in author-collaboration.json. Root supplied author suggestions and primary comparisons. None of these authors is an independent reviewer.

In detail, profile-cover.md §1 proves polynomial covers for bounded linear observations in reflexive Lr and Hilbert spaces using a uniformly convex regularized-dual potential. §§2–3 factor scalar distance powers into finitely many Holder-dual monomials and, for non-even p, a signed-Fourier Hilbert remainder. Two-sided Taylor subtraction makes the log-ratio kernels W^{2,1}; the same-sign singularity is integrable for every p>1. §4 takes products of the observation covers and chooses actual query representatives. Constants depend only onp, the bounded radius and tolerance.

assembly-proof.md uses that theorem with R=1+2/kappa and eta=kappa/(1+kappa), where kappa=min(1/4,(D-1)/8). Only multiplicative bins surrounding actual interterminal distances need representatives. The union contains at most n+n(n-1)M(2n+2)^A actual points, M=ceil(log(kappa^-2)/log(1+kappa)); this is polynomial in n at fixedp,D. All other radii are handled by a nearest-terminal image plus one common height coordinate. Active queries map to their representative images; representatives themselves retain the finite map. Complete estimates give one global lower factor1-kappa and upper factor(1+2kappa)/(1-kappa), whose quotient is at mostD.

Apply the stipulated pinned094 main theorem ONCE to that finite enriched set with distortion1+kappa. Normalize its one scale before the assembly. Its bound exp(C(log|E|)^gamma(p)), and |E| polynomial in n, give the displayed dimension, absorbing the one extra coordinate into the constant. This establishes the claimed scope under the stipulated source theorem and the supporting author proofs. The source's lower operations are not audited for truth.

The ordinary finite-set source map alone cannot be outer-extended by a Hilbert-style arbitrary-map theorem: outer-extension-obstruction.md gives an exact four-terminal L4 counterexample to that interface. It is not an impossibility statement for this candidate, which chooses its finite map after enrichment.

Contribution assessment: TECHNICAL / no nominee, author-side only. Standard uniform-convexity/mistake covering is prior work; generic enrichment, shared height coordinates and near/far gap handling are prior Elkin–Neiman operations. More decisively, paid-profile-bridge.md derives the entire qualitative all-Lp local profile theorem from the classical Ben Yaacov–Berenstein–Henson omega-stability theorem via bounded splitting rank and finite mistake transcripts. This author read that full bridge and the exact primary theorem/setup. It includes arbitrary measure spaces and actual representatives from arbitrary constrained U. Thus the explicit Fourier/Holder factorization is an alternative proof, not an indispensable new qualitative construction for this target.

The last enrichment adaptation was separately checked: nearby terminals use profile accuracy directly, and distant terminals use only ||x-y||<=2rho from a common radius shell. No unproved ambient closeness of representatives is assumed. The polynomial interterminal-bin enrichment and one common height/scale then give the full statement by the prior finite-set theorem. reading-and-comparison.md details this operation comparison. This can be a new-to-project full corollary without meeting the campaign's substantial-construction criterion. We do not claim that the exact terminal statement was already published, a worldwide novelty result, or an independent contribution PASS/FAIL. No narrowed target or stronger-rate side result replaces the original scope.

Formal support: the full combinatorial/functional-analytic construction is not Lean-checked. No executable index, receipt, hash, or finite diagnostic is presented as mathematical proof. A scoped future formal certificate for the finite tetrahedron's integer distances would validate only that obstruction, not this theorem. No nomination or count is requested; any future use as an accepted theorem would require the appropriate independent gates.
