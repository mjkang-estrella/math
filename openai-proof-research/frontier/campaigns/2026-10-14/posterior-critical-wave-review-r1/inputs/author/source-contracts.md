# Exact source contracts

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Third-party rights
retained privately. Source truth is stipulated, not independently audited.

The repository is https://github.com/openai/math at commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The internal complete catalogue
has 13,223 entries and `truncated:false`. All 15 retained source blobs were
retrieved by immutable raw URLs and checked using Git's `blob SIZE\0BYTES`
SHA1, catalogue size, and SHA256. Machine-readable per-path identities and
URLs are in `inputs/source-authentication.json`; the verifier recomputes them
against the internal complete catalogue. No truncated tree cache was used.

## P: family236, actual dependency

Catalogue title: *The sharp factor-of-IID threshold for the free Ising model
on regular trees*, September26,2026. Upstream prefix:

`preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/`.

There is exactly one constituent manuscript in this catalogue family. Retained
README, main, figure, references and nine section files make 13 blobs. The
main file fixes section order. Literal TeX labels, which are stable despite
rendered numbering, identify the interfaces:

1. `build/sections/01-introduction.tex`, `thm:main` / `thm:sharp`:
   every integer d>=3 and beta>=0, free zero-field ferromagnetic Ising spins
   on the infinite d-regular tree are IID factors iff tanh(beta)<=1/sqrt(d-1).
   The statement expressly gives no finitary coding or coding-radius estimate.
   **Not invoked to prove PCW**; it selects the source family and its setting.
2. `build/sections/02-posterior-fields.tex`, `lem:posterior`,
   `eq:finite-posterior`, `eq:cavity`, `eq:site-field-bound`: for the planted
   free prior and independent Brownian noises, with 0<theta<=1/sqrt(b),
   finite posterior masses have the stated Gibbs likelihood, component
   fields are the posterior log odds using only the component's observations,
   h_(v->w)=X_v+sum_(u~v,u!=w)psi(h_(u->v)), and
   h_v=X_v+sum_(u~v)psi(h_(u->v)). Here psi(z)=atanh(theta tanh z),
   |psi(z)|<=beta, |psi(z)|<=theta|z|; the field bounds use b beta and d beta.
   The continuous all-time versions are supplied by item4, not asserted
   from the raw fixed-time version alone.
3. `build/sections/03-critical-information.tex`,
   `lem:critical-information` / `eq:critical-information`: at theta=b^(-1/2),
   the component posterior second moment is between c min(sqrt(t),1) and
   C min(sqrt(t),1), and the whole-site second moment has that upper bound.
   `lem:component-spin-tilts` gives densities 1+eta tanh Y and
   1+eta theta tanh Y when conditioning on component-root or deleted-neighbor
   spin. PCW rederives the whole-history version of the tilt and the exact
   leading normalization. No sharp constant is imported from this lemma.
4. `build/sections/04-innovations.tex`, `prop:innovations`, plus
   `sec:continuous-causal-versions` (especially lines469–603): component
   and full-site posteriors have simultaneous continuous, causal versions,
   start at zero, satisfy the field bounds and cavity identities at all
   times, and tanh(h_(v->w)) is the conditional expectation in the usual
   **component** observation filtration. This last filtration is essential
   for the independent-martingale averaging proof. No assumption that a
   cavity posterior is a martingale in the larger whole-tree filtration
   is made. The innovation SDE's coefficients and its inverse are unused.
5. `build/sections/08-critical-comparison.tex`, `lem:critical-tail` /
   `eq:critical-all-moments`: at criticality, for every integer p>=1 there
   are fixed d-dependent K,t0 such that E|h_(v->w)(t)|^p<=exp(K p^2)t^(p/4)
   for all0<t<=t0. The statement also holds under either spin tilt. PCW
   needs only unconditional fixed orders and derives the uniform path
   bounds with Doob. The separate exp(-c log^2(1/t)) tail is unused.

The bounds are for the actual infinite component. They are not uniform
finite-depth estimates silently promoted to an infinite posterior. The
prior is the free state; no plus/minus state, external deterministic field,
finite random-graph limit, or supercritical theta is substituted.

## Q: referenced companion, comparison only

The companion is *The free uniform spanning forest is a factor of IID*,
September25,2026, upstream prefix
`preprints/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026/`.
P's introduction explicitly references it. Its `introduction.tex`
`thm:main` concerns a graphwise Borel FUSF factor on every infinite connected
locally finite simple unweighted graph; `thm:sr-group` treats invariant
strongly Rayleigh laws on countable groups. Its `response.tex`
`lem:forest-response` and `prop:canonical-drift` give a uniform supremum-norm
response bound for the forest posterior. These permit a causal inverse.
Neither the read theorem interfaces nor the read response proof states a
critical Ising posterior process scaling. Q is not a PCW proof premise.

## Standard operations and external primary comparisons

The martingale inequalities and continuous time-change theorem in candidate
Section4 are standard probabilistic tools. The application to a changing-law
array, including time zero and bracket averaging, is proved there explicitly.
External retained primary bodies are comparison evidence, not extra
stipulated theorems that imply PCW. Their retrieval identities, unsuccessful
version attempt, reading extents and limits are recorded separately.
