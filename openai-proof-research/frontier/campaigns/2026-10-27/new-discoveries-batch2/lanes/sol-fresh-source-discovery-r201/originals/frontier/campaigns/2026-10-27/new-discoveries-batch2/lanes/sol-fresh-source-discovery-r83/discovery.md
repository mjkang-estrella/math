# Source screen and unresolved full target

## Scope and attribution

The selected primary source is Das, Sarkhel and Nath, Palestine Journal of Mathematics 14(1) (2025), 813–838. Canonical publisher body:
https://pjm.ppu.edu/sites/default/files/papers/PJM_14(1)_2025_813_to_838.pdf .
Conjecture4.1 is printed on p.837 and appears at lines1818 onward in sources/hansen.txt. Definitions are on printed pp.813–814; Theorems2.1–2.2 and their actual bodies were read. Publication metadata: received27May2024, accepted21July2024. The earlier preprint is2304.02230. MathDB357982 was used only as an attribution locator, never as novelty evidence.

Exact universal target: for EVERY finite nonabelian group G, let C(G) have vertex set G minus Z(G), distinct vertices x,y joined iff xy=yx, and let NC(G) be its simple complement on that same vertex set. For EACH choice Γ in {C(G),NC(G)}, conjecture

    M2(Γ)/|E(Γ)| >= M1(Γ)/|V(Γ)|,
    M1 = sum_v deg(v)^2,
    M2 = sum_{unordered edges {u,v}} deg(u)deg(v).

This is the authors' actual universal conjecture, not an extrapolation of a heuristic. The quotient formulation presupposes a nonempty edge set. This lane seeks a substantive result on the intended nondegenerate class; no zero-edge/domain correction is nominated. No universal proof or counterexample is supplied.

## Three-question screen before sustained investment

1. Lin–Zhou2501.18656v1, Section7: for m>=3, n the integer with binom(n-1,2)<m<=binom(n,2), s=m-binom(n-1,2), and the remaining small-s range, the unique distance-spectral minimizer among all connected m-edge graphs is the complement of the balanced union of s+1 paths. Read source definitions and Section7. Exclude: Chen–Li–Li2604.26385v1 Theorem1.2 proves the remaining range 1<=s<(n-2)/2; Theorem1.3 gives the all-range result. Actual theorem bodies were read, with balanced-path notation checked. This is prior posted resolution, not independent verification of every line of their proof.
2. Arvind–Cameron–Ma–Maslova2305.07301v5: class2 groups with isomorphic full commuting graphs are isoclinic. Introductory prose suggests this, but Section9 explicitly credits Eamonn O'Brien with counterexamples SmallGroup(64,18) and SmallGroup(64,215), and orders3^6,5^6. Exclude by the SAME current source. Also read Jezernik–Moravec1510.01536 Example4.13 and Cameron–Kuzma2012.03789 Section5: commutativity-preserving central quotients/covers are a classical mechanism. In particular, killing the nondecomposable e12+e34 commutator relation and padding the center is not a fresh discovery. No attempt to promote the introductory heuristic was made after the actual body was read.
3. The selected universal Zagreb conjecture above survived this bounded screen. Closest bodies read: source Theorems2.1–2.2; Vukičević et al., MATCH66 (2011), 627–645 Theorem2 with its proof (regular/biregular cases already classical); Das–Nongsiang–Nath, Algebra Discrete Math.37 (2024), 191–214 Theorems6–7 (complement identities and double-toroidal restriction); Das–Nath–Shang2026 DOI10.1007/s00010-026-01314-5 (different vertex set: commuting CONJUGACY CLASSES, not noncentral elements). Its Question3.5 is not substituted for Conjecture4.1.

## Sustained algebra on the selected full target

Put X=G\Z(G), n=|X|, and let C be the REFLEXIVE commuting matrix on X: Cxy=1 iff xy=yx, including the diagonal. Define

    t_x = |C_G(x)|-|Z(G)|,
    T1 = sum_x t_x, T2 = sum_x t_x^2,
    Q = sum_{ordered commuting pairs x,y in X} t_x t_y.

Then C1=t. The simple commuting adjacency is C-I and its degrees are t-1. Direct expansion gives

    2 M2(C(G)) = Q-3T2+3T1-n,
    2 |E(C(G))| = T1-n,
    M1(C(G)) = T2-2T1+n.

Consequently its twice-cleared Zagreb gap is exactly

    2n M2 - 2|E| M1 = nQ-(T1+2n)T2+2T1^2.                 (L)

For the noncommuting graph, adjacency is J-C and degrees are n-t; therefore

    2 M2(NC(G)) = (n^2-T1)^2-n^2 T1+2nT2-Q,
    2 |E(NC(G))| = n^2-T1,
    M1(NC(G)) = n^3-2nT1+T2,
    2n M2 - 2|E| M1 = (n^2+T1)T2-n T1^2-nQ.              (U)

These identities follow by multiplying out the quadratic forms. They hold for ANY symmetric reflexive zero-one matrix; they are routine helpers, not discoveries. A full proof requires BOTH L>=0 and U>=0 uniformly for all finite nonabelian groups. Equivalently Q must lie between

    ((T1+2n)T2-2T1^2)/n
and
    ((n^2+T1)T2-nT1^2)/n.

The interval has nonnegative width (n-2)(nT2-T1^2)/n by Cauchy–Schwarz, but this does not locate Q inside it. Group-specific control of Q remains missing. No passage from a finite group list or nilpotency-class2 subclass to all groups is justified.

### Failed general positive-matrix route

In S4 take a=(12), b=(12)(34), c=(1324). The commuting matrix on these three noncentral elements is

    [1 1 0; 1 1 1; 0 1 1].

Its quadratic value at (1,-1,1) is -1. Thus C need not be positive semidefinite, and a Gram-matrix argument for L cannot be assumed. This does NOT refute either source inequality. Literal S4 checks give n23, edges25, M1=164, M2=280 for the commuting graph, and positive gaps in both cases.

The general graph K1,5 disjoint K3 has n9, edges8, M1=42, M2=37, hence nM2-|E|M1=-3. This is the source's already-known classical nongroup counterexample. No group realization is established, and none is claimed. The algebraic identities alone cannot establish L>=0 for all reflexive graphs.

### Bounded class2 construction and exact checks

For V=F2^d and W=F2^r, choose coefficients c_ij in W, i<j, and set f(v,w)=sum_{i<j}v_i w_j c_ij. On V×W define

    (v,a)(w,b)=(v+w,a+b+f(v,w)).

Bilinearity is the cocycle identity, hence the law is associative. The commutator is B(v,w)=f(v,w)+f(w,v). For radical-zero B the center is 0×W. On nonzero V form the reflexive matrix A_vw=1[B(v,w)=0], put k=A1 and z=2^r. Each nonzero fiber has z vertices, degree d_v=zk_v-1, and

    M1=z sum_v d_v^2,
    2M2=z^2 sum_{v,w} A_vw d_v d_w-z sum_v d_v^2.

check.py uses fixed seed830029, d4..8 and90 trials per dimension; it retains442 radical-zero cases. Integer arithmetic finds no negative commuting or noncommuting gap. These are bounded sampled cases only. Numpy int64 intermediate dot products fit the caps' bounded parameter range; final gaps use Python integers. validate.py independently checks the identities with Python integers for S4 and a literal order64 group, checks all4096 cocycle triples for that group, and matches its compressed/full graph indices. No floating-point eigensolver is used.

## Freshness, full-scope gap and strongest objection

All campaign dates were searched, filenames FIRST via rg-l, including arbitrary *.md/*.json/*.txt names, then bounded FINDINGS/discovery/SUMMARY/provenance/progress sections. Named search false positives were read where relevant. A later exact numeric boundary gate avoids accidental matches inside enormous integer certificates. No exact selected-target prior report was located in this bounded search. This is not a repository-wide semantic nonduplication theorem.

The supplied complete snapshots' hashes and counts were verified. Live HTTP at18:30Z found OpenAI head unchanged, Omega head23a4ae6f843d1635869b7656fb6bd681121447a8. A single compare request from supplied Omega1b999d9f returned45 commits and a bounded changed-file inventory, preserved in sources/omega-compare.json. No matching Zagreb/isoclinism path was found; a loose NoncommutingGraph path is an Artin-group parabolic-intersection file and supplies no finite-group Zagreb statement. Blueprint and Lean paths are never equated. No global current semantic audit or priority clearance is claimed. HTTP errors/challenges would remain access holds; no bypass, proxy or retry loop was used.

Strongest objection/falsifier: the two bounds on Q are UNPROVED for the full group class. One valid finite nonabelian group with a negative exact gap would refute the source; alternatively an actual full universal primary proof would remove discovery eligibility. The442 cases and failed PSD route establish neither. No accepted family, regular/biregular special case, new parameter instance, helper or source correction is nominated. No independent review, PROOF.md, Lean or paper is appropriate for this unresolved packet.
