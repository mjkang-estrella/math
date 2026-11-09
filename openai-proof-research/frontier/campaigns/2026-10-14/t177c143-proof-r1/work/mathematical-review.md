# Independent correctness working notes

Reviewer: Codex / GPT-6.1-Sol / high / default service tier. First independent
T177C143 correctness round. No inherited objections, desired grade, or
contribution assignment. Only the exact incoming r143 author root is inspected;
no other T177C143 role output is read. Source pin and its proof operations are
stipulated true. Artifact authentication is independent of mathematical judgment.

## Initial independent reconstruction (before controls)

P1: For each vertex, top-face counting gives sum incident edge weights = 2 mu(v).
For each edge, triangle weights sum to 3 nu(e). Thus all weight marginals are
probabilities, sum_e ||delta 1_e||=3, and ||delta x||<=3||x||. Purity supplies a
triangle at every edge, hence nonzero syndrome directions. H^1=0 identifies the
entire kernel with cuts, so every fibre is a coset of B^1 and
dist(x,B^1)=lambda(delta x). Hence ||b||/3<=lambda(b)<=||b||/beta.
The triangle-coordinate inclusion has bi-Lipschitz constants beta and 3
relative to lambda. No restriction on b is needed.

P2: Any cross-fibre difference maps to b+c; therefore every transport cost is
at least lambda(b+c). Translation by one minimum preimage pairs the uniform
cosets at constant cost. A joint law of all fibres is a law on sections, because
the finite intersection of the membership events still has probability one.
Conversely add one independent uniform cut to ALL outputs of a sampled section.
Each marginal becomes uniform while every difference is unchanged. This
preserves arbitrary nonlinear/nonzero s(0) and one common random seed.

P3: q(x)=x+s(delta x) lies in cuts and satisfies q(x+delta a)=q(x)+delta a
without any symmetry hypothesis on s. Connectedness makes a cut potential
unique modulo constants; path parity is independent of the path. Translating
a nonzero Walsh coefficient yields boundary A={u,v}; handshaking in the
component of u forces a u-v path. For u=v the constant sign suffices. Normalized
Parseval and influence use uniform edge-cube measure: I_e=sum_{A containing e}
hat F(A)^2, so total influence>=dist(u,v).

P4: The ordered pair separation of a potential of vertex mass t is 2t(1-t),
bounded by 2 min(t,1-t), then by 2||delta a||/alpha. The direction difference
of q is 1_e plus the section difference. Its norm is at most nu(e) plus that
difference; sum nu=1 is essential. The linear syndrome map pushes uniform
edge cube to uniform B. Thus S(s)>=alpha*bar_d/2-1 pointwise in deterministic
s, and hence for every section law. The law's maximum L_s bounds S by 3L_s;
R_s bounds S by R_s sum_e lambda(delta 1_e)<=R_s. Extracting a fixed pair is
after expectation over the law, never after observing its seed. Negative
lower bounds remain valid and do not need division by the lower bound.

P5: Tree restriction is a bijection from cuts to tree-edge assignments.
The cut correcting an arbitrary preimage gives a unique output with tree
coordinates zero; H^1 makes it independent of the preimage. This is a linear
right inverse. The f-row (f outside T) is the parity on C_T(f), so summing
column norms gives sum_{f outside T}nu(f)|C_T(f)| <=2 diam+1. Conjugating by
uniform H averages columns uniformly over their edge orbit. Since nu is
constant on each orbit, |O|nu(e)>=gamma implies the column estimate with
factor (2 diam+1)nu(e)/gamma. For EACH b+c fix a minimum preimage before
applying the triangle inequality. The section law itself is identical for
all pairs; it does not depend on the minimizing preimage or selected pair.

P6: Actual source construction/expansion/geometry/homology bodies were read.
They explicitly define the unchanged skeleton for all m>=2, fix all required
odd-prime largeness assumptions, and prove F_2 expansion against B and
vanishing. Their operations are assumed, not audited. Vertex stabilizers
have order M; action preserves tags, so face stabilizers fix their vertices
and have order <=M. G is transitive on faces of each type. At most binom(N,d+1)
|G| top faces and at least |G|/M edges per edge-type orbit give gamma>=1/K.
Passing to the image of G in Aut(X) changes neither orbits nor averaging.

P7: Incidence counts give n/(d+1)<=f_d<=Dn/(d+1),
1/(Dn)<=mu(v)<=D/n, and max vertex degree<=dD. For mass(S)<=1/2,
cut-mass>=epsilon*mass(S); the outside incident marginal is at most twice
the outside-neighbour vertex mass, giving growth >=1+epsilon/2.
Starting mass>=1/(Dn), if the R-ball still had mass<=1/2 then iterated
growth would give mass>1, impossible for the stated R. Two balls of mass
>1/2 intersect; diam<=2R. For r>=1 a radius-(r-1) ball has at most Delta^r
vertices, hence mass<=D Delta^r/n<=1/2. Thus bar_d>=r/2. r=0 is trivial.
All finite C constants follow: epsilon*r/12-1/3, epsilon*r/4-1 and
K(4R+1)/epsilon, K(4R+1). Fixed d,q gives fixed positive epsilon and fixed
Delta>1; n_m tends to infinity on the whole tower. Both constants are
Theta(log n_m), eventually absorbing the subtractive constants.

P8: Ordinary cofilling follows from choosing a minimum representative and
beta expansion; it constrains one filling at a time, not all differences
of one shared section. The uniform lambda-to-syndrome L1 comparison remains
compatible with the all-sections obstruction. Grand-coupling equivalence
has been checked above. Collective union-support filling is auxiliary
context, not a replacement for any frozen clause.

## Navigation error and limits to retain

The first command erroneously used rg --files one directory above the project
without the prospective pruning. Its truncated filename listing included
copy paths and another project; no bodies were selected from those names.
This fails the requested before-traversal policy for that initial inventory.
No perfect isolation certificate will be claimed. A subsequent direct read of
the first 160 campaign-ledger lines exposed unrelated historical dispositions
as well as the acceptance rules; none is a mathematical premise or used to
infer this verdict. All later broad searches must prune before descent and
body selection. These errors do not entail reading another T177C143 role body.

Outstanding work: independent source-byte authentication, bounded primary
proof and operative-original reads, guarded authored search, disposable
code checks, honest current-original observations, and final analytic verdict.

## Prospective steering during final assembly

The user subsequently added every component/filename containing structural
and r144, including role briefs and parent intakes, to the existing prospective
exclusions. The guarded walker and named-original safety check were updated
before any further external selection. No broad search was rerun after this
receipt. Earlier search records are not retrospectively certified for r144.
This supplies no mathematical premise or different verdict assignment.

## Completion checkpoint

All nine canonical raw source files were independently re-downloaded and
matched complete-tree sizes, Git blob SHA1, SHA256 and authenticated incoming
bytes. The full mathematical source sections were read. Strongest named
Fourier, quotient-transport, coupling/right-inverse and random-cofilling proof
portions were read; their operations agree with the self-contained finite
argument. FRT's actual journal proof of the random tree bound was also
acquired/read as a transitive comparison. No transitive proof is substituted
for a missing step in the finite argument. Unread portions remain explicit
in the final reading record.

Copied incoming verifier: 85 payload files accepted. Seven copied synthetic
controls and the copied diagnostic passed. The latter has 19 sampled nonlinear
sections, 157 Fourier vertex-pair checks and 168 upper inputs on three small
complexes. They do not certify universal statements or source-sized examples.
All 89 incoming files (including envelopes) matched the intake observation
after replay. Twenty-one named original files were captured late; only the
mutable campaign ledger differed from the author's late snapshots among the
18 common named files. No first-read or whole-parent preservation is inferred.

Mathematical conclusion after independent P1--P8 reconstruction: full-scope
correctness PASS, conditional only on the stipulated source177 operations.
No required mathematical repair and no unresolved frozen clause. P9 evidence
limits, search mistakes and late readings qualify the evidence coverage; they
are not asserted mathematical premises. No contribution/novelty or other gate
is assigned.
