# Family 171: multicolor cube Ramsey pre-freeze barrier

Status: no candidate frozen, no nomination, no proof or contribution verdict, and no count. This is a diagnostic of two attempted transfers. It does not settle three- or four-color cube Ramsey numbers. The upstream two-color theorem and its proof operations are stipulated true at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## Exact source and potential direction

The pinned `The-hypercube-Ramsey-number-has-linear-order-September-23-2026` proves an absolute C with R_2(Q_n) <= C 2^n for every n. Its introduction already derives linear bounds for dense cube subgraphs and Cartesian powers of a fixed spanning cube subgraph. Those are paid corollaries, not candidates. The earlier project proposal `proposals/combinatorics.md`, line 140, likewise screens monotonicity/product transfers as too thin.

A possible genuinely stronger direction was a fixed-color extension R_r(Q_n)=O_r(2^n). It was not frozen: the all-r formulation is false, and even the r=3/4 formulation lacks a paid construction here. No narrower substitute is being offered as a result.

## First-moment boundary (classical, not a discovery)

Fix an integer r>=5 and 0<c<1. Write v=2^n and e=n2^(n-1), and N=floor(c r^(n/2)). Color all edges of K_N independently and uniformly with r colors. For each injective map of Q_n's vertex set into [N], the probability its edges have one color is r^(1-e). There are at most N^v such maps. Hence the expected number of monochromatic labeled copies is at most

    N^v r^(1-e) <= r c^v,

which tends to zero. For every sufficiently large n, some coloring has no monochromatic Q_n and therefore R_r(Q_n)>N. Since sqrt(r)>2, the ratio N/2^n diverges exponentially. Thus an all-fixed-color linear conclusion is false. This says nothing adverse about linear order for r=3 or 4. The source introduction already credits first-moment edge-density obstructions; the calculation is recorded only to prevent an invalid proposed target.

## Why palette merging does not iterate the two-color theorem

A two-color theorem on complete hosts can be applied after merging palettes, but a cube found in a merged color need not contain a monochromatic smaller cube in the original colors. For every m, color each edge xy of Q_m by the parity of the Hamming weight of its lower endpoint. Every 4-cycle is a two-coordinate face: after fixing the other coordinates, its four vertex weights are k,k+1,k+1,k+2. Two edges have lower weight k and two have lower weight k+1. Consequently neither color contains a 4-cycle, hence neither contains Q_n for any n>=2. A cube host cannot be used as a replacement complete host for another application of the source.

The actual primary Alon–Radoičić–Sudakov–Vondrák paper, *A Ramsey-type result for the hypercube*, introduction and Section 2 setup (PDF pages 1–3), already discusses C4 avoidance by alternating levels and parameterizes edges by lower-level weight. That primary concerns cube hosts, unlike the complete-host number under consideration. The elementary obstruction is therefore credited, not nominated. URL and immutable retrieved PDF/text hashes are in `primary-receipt.json`.

## Exact source interfaces that a new proof would have to replace

In source Section 4, `lem:bias-purity`, the available surplus is measured from 1/2. Its density plateau starts at P_0>=1/2+a_*, picks one of the two complementary colors, and writes p=1/2+a_i. The second hypothesis excludes nearly pure patches in either complementary color. A balanced three-color instance can have every single-color density near 1/3; merging two colors gives density 2/3 but absence of a single-color cube does not imply absence of a cube in that merged graph. Thus the source's bad-sequence premise cannot simply be asserted for a palette merge.

Section 12, `cor:deep-discrepancy`, controls either color at density 1/2 in both orientations. With f_x=2*1_G(x,.)-1 and D_pi=(1+m_pi)/2, `lem:homogeneous-peeling` explicitly requires

    max_x tau(x) D_pi(x)^(-d) exp(C_* Q) <= Gamma < 1.

The proof deletes an excluded label coordinate at cost D_pi(x)^(-d); its extension count is at most exp(C_*Q). This is an actual quantitative contract, not an estimate inferred from the title.

For the naive flat full-degree transplant, take tau uniform on N=C_n2^n labels, d=n, and D_pi identically 1/r. The left-hand side is

    exp(C_*Q) (r/2)^n / C_n.

In the source's bad-sequence normalization one may take C_n<=n. For r=3 and Q>=0 this expression is already at least (3/2)^n/n, so cannot satisfy Gamma<1 for large n. The same exponential mismatch survives d=n-o(n) and D_pi=1/3+o(1). At r=2 the factor r^n cancels 2^n; the remaining exp(C_*Q)/C_n is NOT automatically small. The source's further patch, dimension, gain, and allocation operations still pay its actual applications. This record does not claim that the displayed flat substitution describes every source application or every possible multicolor construction.

Even the conditional flat calculation assumes an analogue of the half-density interaction hypotheses that has not been proved at density 1/3. Both the structural dichotomy and the exponential deletion cost therefore remain unpaid. A successful multicolor construction would need a new label-sharing/colored-neighborhood mechanism, rather than replacing the constants 2 and 1/2 by 3 and 1/3. No such mechanism was found or claimed.

## Limits

The full 9,875-line section corpus was fetched and authenticated, but not fully read. Reading covered the complete introduction, reduction/notation, proof-input list and Section 12; Section 4 was read only through line 215. The other sections were not used as if audited. The source is accepted as true, not reviewed for correctness. Current primary searches were bounded; Tikhomirov's paper was identified via its primary abstract and source bibliography, not read in full or used as a sufficient antecedent. No claim about the strongest worldwide multicolor theorem or novelty follows from search absence.
