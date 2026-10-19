# T271D110: unbounded random exchange remains unresolved

Original research prose, CC BY 4.0. Author research archive, not a theorem nomination, independent review, contribution rating, or acceptance decision.

The full target in `frozen-target.md` is preserved byte for byte (SHA256 `00c8048cdad5c368cbefcba1cda27219cea1e56b7eff997b738f7f45747c429a`). It concerns every fixed positive quantum spin and every iid nearest-neighbor coupling law on [1,infinity) having all positive moments, without an upper support bound. The thermodynamic limit precedes the positive field derivative at zero, which precedes the low-temperature limit. The coefficient is the homogenized variable-speed random-walk coefficient. No complete proof or counterexample to this target was obtained. No smaller theorem is nominated in its place.

## Paid operations and strongest compatible reduction

Let B denote the pinned *Bloch's Law for Finite-Range Heisenberg Ferromagnets in Three Dimensions*, October 5, 2026. Its `thm:main` is translation invariant. The operative inputs are appreciably stronger than that headline:

- `02-pins.tex`, `prop:pin-identities`, `prop:exposure`, `prop:next-pin-kernel`, `prop:fresh-walk`: arbitrary nonnegative rates in the finite-set stable-symbol input; the actual conditional exposure density including its normalization; and the fresh-walk first-moment identity. All these identities hold at fixed finite volume with specified rates. Spatial invariance is not used in those algebraic operations.
- `03-geometry.tex`, `eq:energy-comparison`, `prop:nash`, `prop:sparse-energy`, `prop:spread-energy`: deterministic graph geometry and a lower comparison of the full weighted energy with a nearest-neighbor available-slot energy. With all bonds at least one the comparison remains available. No random-walk homogenization is required at this stage.
- `04-bootstrap.tex`, `thm:sparse-pins`: a simultaneous-pin estimate, obtained by downward induction on a finite time grid. Its constants include an upper rate bound. The moment/power issue in extending this operation is the actual gap below.
- `05-returns.tex`, `lem:return-expansion`, `prop:long-tail`: the same exposed environment is retained through repeated forward/reverse traversals. The leading long-return constant is independent of the truncation index K.
- `06-ideal.tex`, `prop:finite-word`: midpoint smoothing turns an encounter probability o(1) into an absolute diagonal error o(beta^(-3/2)); the two halves need not have independent environments. `thm:return-bounds` then combines this with the long-return estimate.
- `07-pressure.tex`, `lem:pin-mixture` and its final proof: positive field is an exact mixture of deterministic extra-pin laws. Pressure increments are integrated before taking volume and field limits. It is unnecessary, and insufficient, to try to differentiate a bulk free-energy asymptotic instead.

Raw source URLs have the prefix
`https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Blochs-Law-for-Finite-Range-Heisenberg-Ferromagnets-in-Three-Dimensions-October-5-2026/build/sections/`.
The exact individual URLs, tree Git blobs, and SHA256 values are in `private/source-receipt.json`. Every pinned statement and operation is stipulated true. This work does not audit their truth.

The strongest external compatible reduction is Andres–Taylor's published *Local Limit Theorems for the Random Conductance Model and Applications to the Ginzburg–Landau Interface Model*, Journal of Statistical Physics 182, article 35 (2021), DOI 10.1007/s10955-021-02705-5: Theorems 1.2, 1.5 and 1.7, with speed measure theta=1. Their proof of the annealed result uses an integrable maximal bound and dominated convergence, not an illicit averaging of an uncontrolled quenched local limit. The all-moment assumption and lower bound in the frozen target satisfy its hypotheses after multiplying rates by S. [Published primary PDF](https://api.repository.cam.ac.uk/server/api/core/bitstreams/cfcac6d9-ec11-4298-ad5a-337a9dfddc9d/content).

For fixed conductance bounds 1 <= a_e <= A, B's lower-energy comparisons and upper clock estimates are compatible with this heat-kernel theorem. Keeping p_t^a(x,x) rather than prematurely replacing it by one scalar coefficient avoids demanding a local-limit rate uniform over every environment. The spatial average is taken at fixed beta first. This checks the main integrated compatibility objection; random coefficients alone do not supply an unpaid mechanism. We do not nominate this bounded-rate reduction or assert a fully checked separate bounded-rate theorem.

The correction companion's `08-pressure.tex`, `prop:comparison` proof, supplies a still sharper pinned capacity/ideal-return comparison for its stated constant nearest-neighbor model. It assumes its good-event and residual estimates; its treatment of bad events by q_i<=1 does not furnish those estimates for unbounded external disorder. The spherical-law companion has a different fixed-temperature, zero-field total-spin observable. The ordering companion supplies the finite-set and deterministic geometry already credited in B. No companion is silently promoted to a random unbounded-rate theorem.

## Completed subordinate calculation: quenched pressure exists

This is standard thermodynamic tiling, included to isolate the real missing step. It proves only the pressure-existence part of the frozen statement.

Write c_S=S(S+1); the two-spin operator norm satisfies ||S_x dot S_y||<=c_S. For Hermitian A,B, ordered-eigenvalue comparison gives

|log Tr exp(A)-log Tr exp(B)| <= ||A-B||.

Fix an integer tile side l. Partition a large cube into disjoint translated l-cubes and a boundary remainder. Delete intertile bonds and bonds incident to the remainder, leaving remainder sites independent. The change in pressure per site is at most c_S times the total deleted coupling divided by the volume. For fixed l, the ordinary strong law on the finitely many residue classes of iid edges makes the intertile cost converge to at most C c_S E[a]/l. The remainder cost divided by volume tends to zero: it lies in a fixed-width boundary shell, and the difference of the total coupling sums on the outer and inner cubes, divided by the outer volume, tends to zero by the cube strong law. The remainder's single-site partition contribution also tends to zero.

The tile log partition functions are iid integrable random variables. Integrability follows from the same operator-norm estimate relative to the zero-interaction tile: their absolute values are bounded by a deterministic spin/field term plus beta c_S times the finite sum of internal couplings. Their volume average converges to a deterministic expectation. Thus, for each l, the limsup and liminf of the full pressure lie in one deterministic interval of length at most C c_S E[a]/l. Let l tend to infinity. The limit exists and is deterministic and finite.

Initially take rational beta>0 and h, and intersect the resulting probability-one events. To extend to every pair, use t=beta h and

q_N(beta,t)=|Lambda_N|^(-1) log Tr exp(-beta H_(N,a)+t M_N).

The same norm estimate bounds its Lipschitz constants in beta and t by c_S |Lambda_N|^(-1) sum_internal a_e and S. The former converges almost surely to 3 c_S E[a], hence is bounded along large cubes. A rational dense-set approximation extends convergence locally uniformly to all beta>0,t in R on the same probability-one event. Division by beta gives the claimed simultaneous pressure limit. Convexity in h and the S-Lipschitz bound pass to the limit. Rotation by pi makes it even. Therefore the right derivative defining m exists in [0,S]. This does not determine its low-temperature asymptotic.

## Completed subordinate calculation: the ideal coefficient

Let p_t^a be the heat kernel with generator L_(S,a) in the frozen target. The source's lattice Nash argument, applied to the full site graph, and a_e>=1 give a uniform energy inequality with constants depending on S alone. Dissipation and the semigroup identity then yield

0 <= p_t^a(x,y) <= C_S (1+t)^(-3/2).

For clarity, for a unit mass u_t, q(t)=||u_t||_2^2 obeys q'<=-c_S q^(5/3) while its L1 norm is at most one. Integration gives q(t)<=C_S t^(-3/2); splitting a heat-kernel entry at t/2 gives the claimed entry bound. The construction and nonexplosion of the walk are covered by the primary random-conductance hypotheses. The finite-support energy argument passes through killed boxes and the conservative limit. No upper bound on a is needed for this estimate.

The primary local limit at the origin implies

t^(3/2) p_t^a(0,0) -> kappa,
 kappa=(4 pi)^(-3/2) (det D_(S,nu))^(-1/2),

almost surely. The normalization is exact: the primary Brownian covariance is Sigma^2=2D, so (2 pi)^(-3/2)(det Sigma^2)^(-1/2)=kappa. Uniformity for t in compact diffusive intervals in Theorem 1.5 passes from square integer scales to all real t. The Nash bound permits expectation and then summation over n by dominated convergence:

lim_(beta->infinity) beta^(3/2) sum_(n>=1) E[p_(n beta)^a(0,0)]
 = kappa sum_(n>=1) n^(-3/2).

The tail is bounded by C_S K^(-1/2), uniformly in beta>=1. At fixed beta the spatial ergodic theorem identifies the volume average of each bounded stationary diagonal with its expectation. These are the classical ideal-walk operations. They are not the interacting spin result.

## Attempt 1: remove upper-rate dependence by loop erasure

A naive bound for all chronological mark lists uses high moments E[a^j] if a bond is revisited. That is unnecessarily weak for localization. A complete first-moment escape estimate survives without any conductance cap.

Use the source's finite cube and its allowed pin law at each fixed disorder environment. Pins may be a measurable function of the conductances, but must be deterministic conditional on them. Sample the full picture with its correctly normalized pinned law, then the exposure and fresh transitions as in B. Require the starting slot to be a hole almost surely (for example, pin that slot at the cut). Consider a deterministic schedule of at most s full/partial traversals, each of elapsed length at most beta, with either direction and matching layers. There exist A,c,C_s>0, depending on S,E[a],s but not the cube, anchor or chosen pins, such that its annealed probability of leaving the sup-norm ball of radius R=ceil(A(s+1)beta) about the starting site before being killed is at most C_s exp(-c beta), for beta>=1. The same assertion holds for the ideal walk, stopped in a finite box.

Proof. Before the first exit, some traversal piece has displacement at least R/s, since displacements of at most s pieces sum to the total displacement. Its visited sites give a finite nearest-neighbor walk. Chronologically erase loops from the portion ending at that displacement: the resulting simple site path has length at least R/s and its jumps occur in their original chronological order. Take the first j=floor(R/s) edges. They are DISTINCT unoriented site bonds. This is the essential bookkeeping improvement over counting all jumps.

There are at most C R^3 possible starting sites for the selected piece before the first exit, at most 6^j site paths from each, and at most C_S^j choices of slot endpoints and actual/fresh clock designations. Forced transports use actual marks. Fresh jumps use the independent fresh clock family for this piece. Seam operations have zero site displacement and require no mark in the simple site path. On one piece, physical time is injective modulo beta, so the j mark times have simplex volume at most beta^j/j!, also after reversing or unwrapping the piece.

At fixed disorder, B's `lem:factorial` bounds the mixed factorial measure by a constant per step times the product of the j conductances. The bound is uniform over the pins. Since the retained site bonds are distinct and the external conductances are iid, integration over the ORIGINAL disorder law makes this product exactly (E[a])^j. Thus the probability is at most

C_s R^3 [C_S beta E[a]]^j / j!.

Choose A so that j is at least twice e C_S beta E[a] for all sufficiently large beta. The inequality j!>=(j/e)^j gives exponential decay; the polynomial R^3 is absorbed by decreasing the exponent. Increasing C_s covers the remaining beta>=1. The source factorial estimate applies before any conditioning on exposure, exactly as in its localization proof. No averaged Gibbs partition function or resampling of disorder on later traversals is introduced. This proves the assertion.

This repairs the naive escape estimate. It does not establish the sparse-pin bootstrap or Bloch's law. Chronological loop erasure, iid factorization and factorial insertion are credited standard operations, not a proposed contribution by themselves.

## Attempt 2: anneal the sparse-pin induction

Keep the law correct. Write Z_E(a)=E_b^a[2^(n_E)] for the source's PIN normalizer, and define

Q_E(da,domega)=P(da) [2^(n_E(omega))/Z_E(a)] P_b^a(domega).

Its disorder marginal is exactly P, for every deterministic or disorder-measurable choice of E. Consequently the raw union/Markov bound for exceptional conductances disclosed before freezing DOES remain valid under this quenched mixture. The prefreeze warning about reweighting is not an assertion to the contrary. Replacing Z_E(a) by one globally integrated normalizer would change the disorder distribution and would be a different argument.

Suppose an averaged version of the source's sparse-avoidance induction were available for the augmented pin set P=E union T. Its blocking, regularity, energy and new escape calculations are linear in probability or expectation up to the last step. They would at best give

E_a r_a(E,T) <= C beta^(-99/100),

with a suitable control of the sparse geometry. But the exact source pin inequality is QUENCHED:

P_E^a(T subset B_E) <= [2 r_a(E,T)]^m,  m=|T|.

Averaging gives an upper bound 2^m E_a[r_a(E,T)^m], not [2 E_a r_a(E,T)]^m. The latter replacement has the wrong Jensen direction. A Bernoulli variable X of mean delta has E[X^m]=delta, which can exceed (C delta)^m for any fixed C and m>=2 when delta is small. This scalar example refutes that inference only; it is not a spin-system example and does not refute the frozen target.

Retaining the stronger product BEFORE the arithmetic–geometric-mean step in B's `prop:pin-identities` does not instantly fix the problem. It gives

P_E^a(T subset B_E) <= 2^m product_(j in T) P_(E union T)^a(j in sigma(T)).

Those factors share the entire environment and the augmented-pin normalization. They are not independent just because the bare bond variables are iid. The source first-moment next-pin kernel does not assert a joint independent law for them. No volume/test-cardinality-uniform product or high-moment estimate was obtained.

A concrete unclosed induction obligation is an upper bound on E_a[r_a(E(a),T)^m] at the scale (beta^(-9/10)/2)^m, uniform in all finite grid pin choices, sparse tests of arbitrary cardinality and cubes, under an induction hypothesis strong enough to control the augmented laws. This is a sufficient proposed closure criterion, NOT an assertion that it is necessary for the target or that every possible proof must use it. Alternatively one could establish an appropriate product estimate using the unaveraged pin-output factors. Neither follows from the calculations here.

In particular, independence of the exposure halves, iid resampling on every period, removal of the pin-normalizer factor, a cap depending on the box, or a finite bound on |T| would change a required operation. None has been adopted.

## Attempt 3: truncate conductances and pass through pressure

There is a robust pressure approximation but it does not control the required derivative. Put a^A=min(a,A). The norm comparison gives, uniformly in h, for the thermodynamic pressures just constructed,

|p_beta(h)-p_beta^A(h)| <= 3 c_S E[(a-A)_+].

The right side tends to zero, faster than every fixed inverse power of A under the frozen moments. It is independent of h. Nevertheless uniform approximation of even convex Lipschitz functions does not preserve the right derivative at zero: f_delta(h)=sqrt(h^2+delta^2) and g(h)=|h| satisfy sup_h|f_delta-g|<=delta and are even convex 1-Lipschitz, while f_delta'(0+)=0 and g'(0+)=1. Thus an error divided by h cannot be sent through h down to zero at fixed cap. This diagnoses the proposed pressure-only transfer, not the physical limit.

An annealed physical partition function is not a substitute. For example a=exp(|Z|), Z standard normal, lies in the frozen class: E[a^q]<=2 exp(q^2/2) for q>0. Yet E[exp(t a)]=infinity for every t>0, since the integrand on the positive Gaussian tail grows as exp(t exp(z)-z^2/2). In any finite cube with an edge, the fully polarized vector is an eigenvector at energy -S^2 sum_e a_e. Hence at h=0 the original partition function is at least exp(beta S^2 a_e) for that edge, and its disorder expectation is infinite. The quenched log partition function remains integrable by the norm bound above. This is a reason to preserve the frozen quenched model, not a counterexample to its asserted Bloch law.

No monotonicity of magnetization under arbitrary quantum Heisenberg bond changes is assumed. Search hits on XY correlation inequalities and weak-disorder spin-wave calculations are navigation only here; their full bodies were not read and they are not premises or exclusions.

## Exact outcome and limits

The unclosed operation is the compatibility of unbounded iid rates with the source's simultaneous sparse-pin induction, retaining arbitrary test cardinality, the quenched disorder law and the actual augmented-pin normalizers. The ideal coefficient, thermodynamic existence and annealed escape are not the missing central invariant. All three are explicitly separated above so they cannot be mistaken for a proof of the interacting result.

No full proof, full-target refutation, eligible candidate, independent review, formalization or manuscript is claimed. The bounded-rate comparison, elementary diagnostics, and escape adapter are not nominated. No count or mathematical gate is assigned. A continuation would need a new weighted/product sparse-pin invariant, not another heat-kernel theorem, truncation-pressure estimate or numerical check. All frozen hypotheses and the entire limit order remain unchanged.

The public directory contains original prose/code only. Upstream/third-party bodies are private evidence under their original rights. Reading extents and retrieval failures/limits are recorded separately. The exact inventory checks bytes, never mathematics. No upload, publication, browser UI operation, nested agent, shared-index edit, commit, staging or PR was performed.
