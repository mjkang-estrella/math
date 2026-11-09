# Integrated reduction: biclique routing, not a substantial nominee

**PREFREEZE / no nominee.** The calculations below close the elementary prescribed-biclique routing question. They are durable feasibility notes, not a frozen author-proof submission, independent grade, acceptance or count. No pinned graph-immersion input was located in either of the two permitted catalogue screens; no pinned statement/proof has been used. The source-development requirement for an upstream-dependent nominee is therefore unmet. The operation found here also reduces to classical factorization/lifting and a fixed routing gadget. There is no claim of new-to-literature status or exhaustive clearance.

## Exact parameters of the calculation

Take integers a,b>=0 and x,y with 0<=x<=a,0<=y<=b,t=x+y>=1. In the simple complete bipartite graph K_{a,b}, prescribe x branch vertices X on the a side and y branch vertices Y on the b side. A strong K_t routing means one simple path for every unordered pair of distinct prescribed vertices, with pairwise disjoint edge sets and no prescribed vertex internal to any path. Vertices other than branches may be shared by paths. Let U,V be the nonbranch vertices on the two sides, p=a-x,q=b-y.

Necessary degree conditions are (x>0 implies b>=t-1) and (y>0 implies a>=t-1). Under these conditions define

  d_X=max(0, x(x-1)/2-q floor(x/2)),
  d_Y=max(0, y(y-1)/2-p floor(y/2)).

The only possibilities for a positive d_X are x>=3 odd and q=x-1; then d_X=(x-1)/2. Similarly d_Y>0 precisely when y>=3 odd and p=y-1. Put flags f_X=(d_X>0),f_Y=(d_Y>0).

The constructive calculation yields a strong routing unless one of these explicit obstructions holds:

1. The necessary degree conditions fail.
2. f_X holds, f_Y does not, and p=0; or the symmetric condition f_Y, not f_X, q=0.
3. Both flags hold and min(p,q)=2.

In every remaining case the paths can have lengths only1,2,4, and their total number of used edges is

  L=xy+x(x-1)+y(y-1)+2(d_X+d_Y).

The argument below attains the elementary universal lower bound L. This exact cost is a counting consequence of the construction, not an independent substantial operation. t=1 has the empty routing. x=y=1 also has no parity deficit. Zero-sized parts and one-sided branch sets are included by the degree conditions and the flags, without interpreting chi'(K_1) as1.

## Normalize all cross demands simultaneously

An edge joining two prescribed vertices can only be used by the path whose endpoints are those two vertices: otherwise a prescribed vertex would be internal. If a cross-demand path has length>1, its direct host edge is therefore unused. Replace the path by that edge. This releases edges, creates no collision, and preserves all other demands. Repeating gives every cross demand its one-edge path. The remaining demands are precisely K_X and K_Y in the host with internal vertices U union V.

This simultaneous shortcut is important: arbitrary terminal-pairability permits other terminals internally, whereas the present original demand problem does not. The terminal-pairability theorem is used, if desired, only AFTER the residual demands have moved into U union V, where sharing intermediate vertices is allowed.

## What ordinary factorizations already do

For n odd, label K_n by Z/n. The matching F_c consists of the pairs {c+i,c-i},1<=i<=(n-1)/2. It misses vertex c. Every edge occurs exactly once because its midpoint is uniquely defined modulo odd n. For n even, write the vertices as {infinity} union Z/(n-1); matching F_c contains {infinity,c} and {c+i,c-i},1<=i<=(n-2)/2. These n-1 perfect matchings partition K_n.

Assign each color to a distinct nonbranch vertex on the opposite side and route its matching by paths of length2. This is exactly the proper-edge-coloring/splitting operation of DDFMMS11 Lemma2.1. When n is odd and only n-1 nonbranches are available, remove F_0 and assign the other n-1 colors. At the nonbranch assigned c, exactly the edge to terminal c is unused. The deleted matching F_0 pairs these n-1 residual stubs. Thus the only leftover task is a perfect matching on the nonbranch vertices corresponding to those stubs. No original branch vertex is used as a helper.

With only f_X positive, all residual pairs are on V. If p>=1, route all these disjoint pairs through any one U vertex, then append their two unused terminal stubs. The resulting original paths have length4. The Y-side length2 paths use only Y-U edges, so they are compatible with these U-V core edges. The symmetric case is identical.

## The joint parity task closes, rather than remaining a gap

When both flags hold, p=y-1 and q=x-1 are even. The core demands consist of one perfect matching on U and one on V. If p,q>=4, enumerate their pairs consecutively as (u0,u1),(u2,u3),... and (v0,v1),(v2,v3),.... Use the following four two-edge core paths:

  u0-v0-u1,
  u2-v2-u3,
  v0-u2-v1,
  v2-u0-v3.

Their eight edges are distinct. They form a four-cycle on u0,u2,v0,v2 with four different pendant edges. For every additional U pair use its two edges to v0; for every additional V pair use its two edges to u0. All added edges have a new endpoint and cannot collide with a previously used edge. The resulting core routing uses exactly p+q edges, with every core demand length2. Attaching the residual terminal stubs yields length4 original paths, with no prescribed vertex internal.

The earlier single-helper attempt used the same edge for both repairs; that was only a failed construction. The four-cycle resolves it completely. Even the existence of the base routing is covered by CEGM17v4 Theorem4: on K_{4,4}, the demand graph has four matching edges, maximum degree1, and4<=2*4-3. Its full lifting proof was read. The explicit eight-edge form additionally makes the cost count immediate. Larger rectangular cores add ordinary stars, not a new integral-flow mechanism.

The first bounded core search returned a nonminimal ten-edge witness. That was not a lower bound or an obstruction. The eight-edge construction supersedes its length as a mathematical calculation; the original receipt remains unchanged.

## Actual obstructions, not merely failed factorizations

If f_X holds and p=0, internal vertices are only V. Every X-X path then has length2. Each of q=x-1 vertices can pair at most floor(x/2)=(x-1)/2 incident X edges; this serves fewer than binom(x,2) demands. Symmetrically for f_Y,q=0. Thus these are genuine nonexistence cases for strong routing.

Suppose both flags hold and p=2 (the q=2 case is symmetric). After shortening all cross demands, every branch vertex must use every edge to the appropriate core side: its degree is exactly t-1. At each v in V, all x incident terminal edges are therefore used. Since x is odd and every used internal vertex has even used degree, its used core degree is odd. It is at most p=2, hence equals1. Consequently every nontrivial component of the used U-V core is a star containing exactly one U vertex. That U vertex has y odd incident Y terminal stubs, all used. Each remaining path has both ends in X or both ends in Y, so each core component must have an even number of Y stubs. The odd number y is impossible. This argument applies to arbitrary path lengths and arbitrary internal transitions; it is not restricted to the displayed matching construction.

## Cost lower bound and attainment

Each cross pair needs at least one edge, each same-side pair at least two. In any normalized routing, at most q floor(x/2) of the X-X paths can have length2, because paths through one v in V pair distinct X-v edges. At least d_X of the X-X demands therefore need length>=4. Likewise at least d_Y Y-Y demands need length>=4. This proves the lower bound L. All positive constructions use exactly d_X+d_Y length4 paths and all other paths have their shortest possible lengths, so attain L.

The degree conditions ensure that no other deficits occur. Extra nonbranches can be ignored except when needed as the helper; if sufficient colors exist, direct factorization already routes that side. This checks the slack and one-sided cases at the same quantifiers, rather than silently claiming only a=b=t-1.

## Strongest comparison and stopping decision

DDFMMS11's actual Lemma2.1 proof pays factorization-to-immersion. DY15's opening of section2 already credits unrooted K_{t-1,t-1} to K_t and its Lemma5 proves the common-neighbor list-color lifting; Lemma6 treats multipartite hosts. CEGM17v4's actual residual-demand formulation and full Theorem4 proof pay the terminal-pairability core operation, with the necessary distinction between weak demand routing and avoidance of original branches. Its bipartite-demand companion's complete proofs were also read. The explicit module above is a small compatible composition of those operations, not evidence that the failure of a naive length2 or single-hub route created a substantial gap.

The all-parameter biclique calculation closes. There is no unresolved existence claim in it left for the parent to repair, and no original frozen theorem has been weakened. No nonroutine operation after the strongest integrated reduction has been identified. A substantial full-scope campaign nominee therefore does not emerge. This is a decision not to nominate these calculations, not an independent contribution grade. General arbitrary demand routing, multipartite strengthening and minimum-degree conjectures are NOT proposed as parked replacement targets. The unmet research obligation is to find a distinct proof-feasible nonroutine result, not to rename this parity calculation or improve its presentation.

## Bounded finite support

code/biclique_routes.py constructs and checks all parameter choices1<=a,b<=16,0<=x<=a,0<=y<=b,x+y>=1:22848 cases. It checks10129 constructed routings for complete pair coverage, vertex simplicity, edge disjointness, branch avoidance, lengths<=4 and exact cost L. Rejected cases are classified by the symbolic conditions; these are not independently disproved by enumeration. Separately, a generic simple-path search on148 tiny instances1<=a,b<=4,x+y>=2 agrees with feasibility, using338 recursive states and no cap hit. Its cross-demand normalization relies on the proved shortcut; it is otherwise independent of the constructive routine. These finite computations are support only, not full mathematical verification or independent review. The earlier three core-search results are retained separately.
