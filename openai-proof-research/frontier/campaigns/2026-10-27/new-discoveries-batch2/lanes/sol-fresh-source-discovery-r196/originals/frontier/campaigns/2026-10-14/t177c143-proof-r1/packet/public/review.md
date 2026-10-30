# T177C143 — first independent correctness review

**Verdict: PASS for the entire unchanged frozen theorem, relative to the
stipulated Source177 statements and operative proof operations at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.** No mathematical repair is required;
no frozen clause remains unresolved. This is one correctness verdict. No
contribution, novelty, acceptance, count, formalization, manuscript or release
assessment is assigned. Publication remains stopped.

Reviewer: Codex / GPT-6.1-Sol / high / default service tier. This is the first
independent correctness round, with no inherited T177C143 findings or responses.
The immutable scope is the incoming `packet/public/frozen-scope.md`, SHA256
cc916afef1373c1b3c0abdee271a4c2769f887f664e8c9b2b16b1b381c0de221. The incoming
author proof has SHA256
10e6dda7b9824e629922e3cf6f42de1b2bc194803ace97eb774c7dd85858792a.

The verdict retains the universal finite (A), its stronger sum (B), all
nonlinear and nonnormalized stochastic sections and equivalent grand
couplings, every pair, both constants, and the exact Source177 complexes for
every d>=3, every source-admissible odd prime and every m>=2. It also retains
every finite (C) bound and the uniform ordinary-cofilling and fibre-metric L1
embedding separation. No algorithmic, linear-only, dimension, subsequence or
changed-complex replacement is used.

## P1. Incidences, kernel and metric

For a vertex v, count pairs consisting of a top face through v and an edge of
that face through v. There are d such edges. Dividing by the normalizing
binomial coefficient gives sum_{e containing v}nu(e)=2mu(v). Similarly an
edge lies in d-1 triangles of each containing top face, giving
sum_{t containing e}omega(t)=3nu(e). Each weight function sums to one.
Consequently the union bound gives ||delta_1 x||_2<=3||x||_1 and the exact
identity sum_e||delta_1 1_e||_2=3. Purity with d>=2 places each edge in a
triangle, so every syndrome direction delta_1 1_e is nonzero.

H^1=0 means precisely ker(delta_1)=im(delta_0)=B^1. Thus every fibre is one
coset of cuts, and dist_1(x,B^1)=lambda(delta_1 x). The hypothesized
degree-one inequality and the union bound imply, for all b in B,

    ||b||_2/3 <= lambda(b) <= ||b||_2/beta.

Positivity of incidence weights, finiteness and the support triangle
inequality make lambda(b+c) a genuine translation-invariant metric. B has at
least two elements, since an edge direction has nonzero syndrome, so the
maxima in the definitions are nonempty. The triangle-coordinate map
b -> (omega(t)b(t))_t has distance exactly ||b+c||_2; its Lipschitz and inverse
Lipschitz factors relative to lambda have product at most 3/beta. This covers
all of B, including zero, not selected directions only.

## P2. Exact transport and all joint couplings

Every cross-fibre difference is a preimage of b+c, so every coupling has
expected cost at least lambda(b+c). A minimum preimage z gives the bijection
x -> x+z between the two fibres, with constant cost lambda(b+c). This proves
the exact uniform-fibre W1 identity with the stated weights.

For any grand coupling, all marginal membership events hold simultaneously
with probability one because B is finite. Its outcome is therefore a section
and its induced law is a law on the finite set of all sections. Conversely,
given any section law, add one independent uniform U in B^1 to every output.
Conditional on the sampled section, each marginal is uniform on its entire
fibre. Every pairwise difference is unchanged. The same U is used for all
inputs. Both directions preserve all expected costs and therefore the two
infima, with either denominator. There is no normalization at zero, linearity
assumption or illicit simultaneous choice of pairwise optimal couplings.

## P3. The arbitrary-section Fourier step

Fix any deterministic section. The map q(x)=x+s(delta_1 x) is a cut and obeys
q(x+delta_0 a)=q(x)+delta_0 a. These statements use only the right-inverse
property. Connectedness makes a cut potential unique modulo constants;
potential differences are equivalently path parities, independent of paths.
Thus the sign F_uv transforms under cut translation by (-1)^{a(u)+a(v)}.

In the normalized Walsh expansion under uniform edge-cube measure, translate
a nonzero coefficient at A by every delta_0 a. Equality of the resulting
characters forces the odd boundary of A to be {u,v} for u!=v. Handshaking
inside the component containing u forces v into that component. It therefore
contains a u-v path, so |A|>=dist_G(u,v). For u=v, F_uu=1 gives the required
zero lower bound directly.

For Boolean signs, I_e=E(F(x+1_e)-F(x))^2/4 equals
sum_{A containing e}hat F(A)^2. Parseval gives total squared Fourier mass one.
Hence sum_e I_e(F_uv)>=dist_G(u,v). No property of s beyond being a section
is needed; equivariance is proved for q, not assumed for s.

## P4. The fixed sum, averaging and lower constants

The cut q(x+1_e)+q(x) has some vertex potential a of mass t. Independently
sampling ordered vertices with law mu separates their potential values with
probability 2t(1-t). This is at most 2min(t,1-t), hence at most
2||delta_0 a||_1/alpha. Replacing a by its complement changes nothing.
The cut itself equals

    1_e + s(delta_1 x+delta_1 1_e) + s(delta_1 x).

Its norm is bounded by nu(e) plus that section difference. Sum over e, average
over uniform x, and then average the Fourier inequality over the ordered
vertices. The syndrome map pushes uniform edge cube to uniform B because
it is a surjective linear map with equal-sized fibres. With S(s) denoting
the exact sum on the left of (B), this gives

    bar_d <= (2/alpha)(1+S(s)),
    S(s) >= alpha*bar_d/2-1.

This holds separately for every deterministic section and thus for every
section law, with one fixed distribution-independent sum over (b,e).
If L_s and R_s are the maxima of expected ratios for that law, then
S(s)<=3L_s by P1 and S(s)<=R_s sum_e lambda(delta_1 1_e)<=R_s by
lambda(delta_1 1_e)<=nu(e). Taking infima yields exactly

    L(X)>=(alpha*bar_d-2)/6,
    R(X)>=alpha*bar_d/2-1.

All compared syndrome pairs are distinct by P1. A bad pair is extracted from
the expected costs of the law, not chosen after observing its realized seed.
No positive-lower-bound assumption is used: the inequalities remain valid
when their right sides are negative.

## P5. One law for all upper bounds

Restriction to a spanning tree is a bijection from cuts to arbitrary
tree-edge assignments. Correct a preimage x by the unique cut with the same
tree restriction. H^1=0 makes the resulting zero-on-tree output independent
of the chosen preimage. This constructs a linear right inverse s_T.
For f outside T its output is parity on the fundamental cycle C_T(f).
Consequently

    sum_e||s_T(delta_1 1_e)||_1
      =sum_{f outside T}nu(f)|C_T(f)| <=2D_G+1

for a BFS tree. The last step uses tree depth at most D_G and sum_f nu(f)<=1;
it does not assume cycles have short fillings by triangles.

Aut(X) is finite and preserves the intrinsic weights. Uniform conjugation
over any given subgroup H averages a column uniformly over its edge orbit O.
Since nu is constant on O and |O|nu(e)>=gamma, the averaged column is bounded
by (2D_G+1)nu(e)/gamma. For each b+c choose a minimum preimage x. Linearity
and the support triangle inequality give expected pair cost at most
(2D_G+1)lambda(b+c)/gamma. The distribution on sections was fixed before
choosing this pair or its minimizing preimage. P1 supplies the beta factor
for L. These are exactly both upper bounds in (A), attained as inequalities
by the asserted single law on linear tree-gauge sections.

## P6. Exact Source177 interface

The actual construction, geometry, homology and expansion files identify
X_m=skel_d CC(U/Gamma_N(m);(bar H_i)) for N=2d+1 and every m>=2. The source
requires an odd prime satisfying its local-group, spherical-opposition and
KMS largeness requirements. The frozen statement retains all of them.
The source's homology comparison, quotient-homology proposition and final
skeleton-weight assembly give connectedness, H^1(X_m;F_2)=0 and
alpha=beta=epsilon with the intrinsic X_m weights. These operations are
stipulated true; I check their application, not their upstream truth.

The local-pattern lemma gives vertex stabilizers of order
M=q^{binom(N,2)}, with injectivity and intersections preserved for every m>=2.
The source action preserves types and is transitive on every face type.
Its nonempty face stabilizers are subgroups of vertex stabilizers. There
are at most binom(N,d+1)|G_m| d-faces and each edge-type orbit has at least
|G_m|/M members. Every edge has positive top incidence, so its weight is at
least 1/[binom(d+1,2)f_d]. These estimates give gamma>=1/K for the K in the
frozen statement. Taking the image of G_m in Aut(X_m) preserves its orbits.
No transitivity on all edges, altered complex or coefficient change is assumed.
The source degree bound is exactly D=M binom(N-1,d), and its growth formula
gives n_m>=Nq^m/M -> infinity for every fixed admissible d,q.

## P7. Weighted distances and every finite level

For a pure d-complex with at most D top faces through each vertex,
n/(d+1)<=f_d<=Dn/(d+1), so 1/(Dn)<=mu(v)<=D/n. Every neighbour is witnessed
in one of those top faces, whence maximum graph degree<=dD=Delta.
For mass(S)<=1/2, expansion gives crossing-edge mass>=epsilon*mass(S).
The incident marginal at the outside endpoints is at most twice their
vertex mass. Thus the neighbour ball gains mass at least
epsilon*mass(S)/2. Starting from mass>=1/(Dn), the stated

    R=ceil(log(Dn)/log(1+epsilon/2))+1

forces a ball of radius R to have mass>1/2: otherwise iterative growth would
give mass>1. Two such balls intersect, proving D_G<=2R without regularity.

Here Delta>=2. If r=max(0,floor(log(n/(2D))/log Delta))>=1, a ball of radius
r-1 has at most sum_{j=0}^{r-1}Delta^j<=Delta^r vertices and therefore mass
at most D Delta^r/n<=1/2. A second independent vertex has distance>=r with
probability>=1/2. Hence bar_d>=r/2; for r=0 this is immediate. The floor,
maximum and the small-level cases introduce no exceptions.

Substitution into (A) gives exactly every inequality in (C):

    epsilon*r_m/12-1/3 <= L(X_m) <= K(4R_m+1)/epsilon,
    epsilon*r_m/4-1   <= R(X_m) <= K(4R_m+1).

For fixed d,q, D,Delta,K and epsilon are fixed and n_m tends to infinity on
the whole tower. Thus r_m is asymptotic to log(n_m)/log Delta, R_m=O(log n_m),
and both positive leading lower terms eventually dominate their constants.
Both optimal constants are Theta_{d,q}(log n_m). No subsequence, extra
prime assumption or smaller dimension enters this deduction.

## P8. Uniform ordinary filling and L1 separation

Minimum representatives satisfy lambda(b)<=||b||_2/epsilon, the asserted
ordinary C^1-to-B^2 cofilling bound. Independently, P1 and P2 give L1
distortion at most 3/epsilon for the entire fibre-law W1 metric. Ordinary
filling controls one representative's norm and L1 embedding controls an
unconstrained image of the quotient; neither supplies jointly distributed
representatives with the required fibre marginals and uniformly small
all-pair cost. There is therefore no contradiction with either logarithmic
coherent constant. The auxiliary collective union-support discussion is
consistent with vector coefficient expansion; it is not used to replace
the all-pair conclusion or assigned a separate verdict.

## P9. Evidence and scope of the review

The six externally supplied anchors were independently matched before using
the local SHA256SUMS. The complete, nontruncated 13223-entry preprints tree
matched its supplied SHA256. Nine canonical raw files were independently
re-downloaded at the pin and matched tree path, size, Git blob identity and
SHA256. All five operative mathematical source sections were read in full.
The protected source/primary/history bodies stay private under their original
rights. The primary and history reading record specifies actual extents,
late reads, derivative-search errors and unread transitive proofs. These
limits do not stand in for any mathematical step above.

The author freeze receipt records 2026-10-20T23:39:29.214730Z. The scope bytes
match its receipt and the external anchor. Some source/primary recovery and
the author's 18 named-original captures were late; I do not backdate them or
independently certify first-read chronology from a late packet. All reviewer
reads occur after the author freeze. The review's own 21 named-original
observations are also late. The mutable campaign ledger differs from the
author's early late snapshot; this is an observation, not a proof premise.

Only disposable copies of the read source code were executed. The copied
verifier accepted its 85 payload files; all seven copied integrity controls
and the finite diagnostic passed. The latter covered 19 sampled nonlinear
sections, 157 pair-Fourier checks and 168 upper inputs on three small
complexes. These tests are neither a universal proof nor mathematical gates.
All 89 incoming files matched their intake bytes across the replay and later
observation. The original proof was not edited.

The initial unguarded filename inventory and later derivative false
admissions are disclosed in the reading record. No other T177C143 role body
or findings were read. No perfect isolation, exhaustive history/primary
coverage, priority, absence, or whole-parent preservation certificate is
claimed. The prospective structural r144 exclusion was added on receipt;
earlier searches are not retrospectively certified for it. No active r144
work is consumed.

All P1--P8 mathematical obligations close at the full frozen scope. Required
mathematical repairs: none. Unresolved frozen clauses: none. Evidence limits
remain explicit; contribution and all downstream gates belong elsewhere.
