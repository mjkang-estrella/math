# Structural discovery round 19 — no substantial nomination

Myeongjin Kang; no affiliation. 2026-10-16. Original prose CC BY 4.0;
original code MIT. Third-party source files retain their rights and stay private.

Status: **SCREEN_ONLY / NO_NOMINATION / counted=false**. No full new target
was frozen. The two concrete mechanisms examined below reduce to already
available source operations. They should not consume independent full-proof
or contribution review slots on the present evidence. This is an author
screen, not an independent TECHNICAL verdict or a worldwide-priority claim.

## 1. Family 198: changing the coefficient field does not pay a new operation

The pinned paper's headline is a complex algebra of infinite little
finitistic dimension. Its actual `thm:realization`, however, is already over
an arbitrary field k. The selection construction is a finitely presented
abstract group G with central involutions z_j, an automorphism shifting them,
and finite quotients with independent images of z_0,...,z_(m-1).

For every field k with char(k) != 2 the same algebra kG has the same central
idempotent e=(1+z_0)/2. If Z_m is the elementary abelian central subgroup in
the source finite quotient F_m, prescribe signs +1 through m-2 and -1 at
m-1. Put

    p_chi = 2^(-m) sum_(z in Z_m) chi(z)^(-1) z,
    Y_m = k[F_m] p_chi.

The identity coefficient is nonzero, so Y_m != 0. Centrality gives the
prescribed character on every vector of Y_m. No semisimplicity of k[F_m]
is needed; only 2 is inverted, since |Z_m|=2^m. The source identity

    H^j(Y) = restriction_(alpha^j)(e_0 ... e_(j-1)Y)

therefore gives exactly the same extinction times. The source arbitrary-field
realization and square-zero transfer produce unbounded finite projective
dimensions with the same quantifier order: one algebra fixed before m.
This is a direct coefficient transfer, not a new selection mechanism.

The argument does not cover characteristic two: the displayed idempotent
and character projector are undefined there and +1=-1. Replacing the group
by a group with odd-order central elements would be a different construction
requiring its own verification. No such characteristic-two construction is
asserted or frozen here. This is not a resumption or resolution of FT2 in
family 199, whose target is a symmetric algebra with a self-orthogonal
nonprojective module, not merely infinite finitistic dimension.

## 2. Family 178: a radius exclusion is only a collision-bound extension

The deterministic Ramanujan source already retains logarithmic girth before
its last spectral repair. Its setup takes a=10^(-4), q=d-1 and
q^(g_0) asymptotic to n^(.002a). Its boundary-completion proposition explicitly
preserves the girth exclusion. The last repair uses M=n^(1/3+10a+o(1))
edge-pair draws. Its Step 3 bounds each ordered pair probability by
C_d/(dn)^2. Step 4 uses only pairwise independence across draws and bounds
endpoint collisions/adjacencies by O_d(M^2/n). Step 7 enumerates the entire
polynomial-size pairwise-independent sample space.

Here is the extra operation required to preserve logarithmic girth, stated
independently of the lengthy spectral construction.

**Separation lemma.** Let G be a simple graph of maximum degree d and girth
greater than g, g>=3. Select distinct edges e_1,...,e_(2M) whose endpoint
sets have pairwise graph distance greater than g. Pair these edges in any
way. For each pair ab,cd, delete those two edges and add ad,cb. The resulting
graph is simple, preserves degrees, and has girth greater than g.

Proof. Separation excludes common endpoints and existing inserted edges.
Every endpoint belongs to exactly one inserted edge, so the inserted edges
form a matching. If a new cycle of length at most g contains no inserted
edge, it was already a cycle of G. Otherwise consecutive inserted edges
along the cycle are joined by a positive-length path in G after the selected
edges were deleted. Its endpoints lie either on different selected old
edges, contradicting their separation, or on the two endpoints of one old
edge. In the latter case, restoring that old edge makes a cycle in G, so
the path has length at least g. That also exceeds the total length budget
of the proposed new cycle after including an inserted edge. Contradiction.

**Probability estimate.** In a d-regular n-vertex graph, for independent
uniform oriented edges E,F,

    P(dist(endpoints(E),endpoints(F)) <= g) <= C_d (d-1)^g/n.

For fixed E, the vertices within distance g of its two endpoints number at
most 2(1+d sum_(j=0)^(g-1)(d-1)^j). At most d times this many oriented edges
have a designated endpoint there; a further factor two pays for either
endpoint of F. Divide by dn. A bounded joint-density ratio changes only
the constant. The source supplies precisely that bound within a draw;
between draws pairwise independence and bounded marginal densities give it.
A union bound over O(M^2) pairs therefore gives failure probability at most

    C_d M^2 (d-1)^g / n.

At g=g_0 this is n^(-1/3+20.002a+o(1))=o(1). Thus this event can be
intersected with the existing 1-o(1) spectral success event without changing
the law, its tilt, or its moment estimates. One merely rejects seeds failing
the distance test. Breadth-first search computes the test in polynomial
time. No conditioning of the law and no new spectral estimate are needed.

Consequently the tempting high-girth exact-Ramanujan extension uses the
same source spectral repair and a larger finite collision event. This is
the kind of routine robust transfer explicitly excluded by the brief. I do
not nominate it as a substantial new result. The separation lemma and
probability estimate are complete elementary supporting arguments, not a
claim to independently reprove the source's spectral theorem.

## 3. History and limits

Family 172 has an already developed I17 track and was not reopened.
Family 199 FT2 and family 210 Foulkes have prior unresolved/technical tracks.
The earlier I72/I76 logarithmic-girth work concerns microscopic GOE statistics
in a rare conditioned random ensemble (family 219), not deterministic
construction. Nothing here supplies that missing conditional spectral input.
The family 177 puncturing and family 174 thin-tree screens also already
occur in older history and were not developed further.

No proof of a new substantial full theorem, counterexample to an original
campaign target, manuscript, formalization, acceptance, or submission is
claimed. No existing scope was narrowed or replaced. No nested agent,
shared-index edit, staging, commit, or external write occurred.
