# Selected primary-body review, bounded scope

Every downloaded original was saved and SHA256/size/URL/UTC recorded before extraction. The arXiv download URLs are unversioned; the retained PDF headers identify versions below. This is not a claim that an unversioned URL is immutable. Original bytes, rather than the future response at that URL, are bound by the payload manifest. No live registry clearance was obtained. No exhaustive successor search is claimed.

## 381643: source-internal successor already proves existence

The retained arXiv2112.08503v1 concludes with Conjecture1: existence of graphs not 2-OR-PCG, after its through-ten-vertices observation. Definition5 in v5 defines a k-OR-PCG as a union of k PCGs on the same labelled leaves, each with its own weighted tree and interval. A PCG is induced-hereditary: restrict to the chosen leaves and their spanning subtree, retaining distances; suppress degree-two vertices by adding lengths if necessary.

The retained v5 (2 October2024) identifies itself as DMTCS26:3#10 (2024), accepted10 September2024. This identifies the accepted-text correspondence reported by that PDF, not a separately verified publisher file. Theorem14, pp18-19, explicitly proves nonexistence of a universal fixed t-OR k-interval-PCG representation for t>=2,k>=1. Specializing t=2,k=1 answers the exact existential record. The proof body uses Theorem2's finite bipartite obstruction H_k to k-interval representations and Theorem13's induced-density Ramsey theorem. Choose epsilon=1/t and a host R such that every edge-subgraph with at least |E(R)|/t edges contains an induced H_k. If R were a union of t such representations, one represented subgraph has at least that many edges, hence contains H_k induced, contradicting hereditary closure. This is the complete applicable specialization, not a claim from the abstract.

Theorem2's obstruction proof and its conclusion were read; Theorem13 is a quoted Dudek et al.2013 result, not independently audited. Its full proof dependency tree is unread. The existential certificate may be enormous; no smaller graph is needed for exclusion, and a smaller witness earns no new source-question credit. No new proof proposed.

## 373857: disjoint union only adapts a printed obstruction

The retained arXiv2603.25113v1 defines S-packing coloring by distances: color i vertices must be farther apart than s_i. Proposition10's proof says G11 has diameter3 and four disjoint triangles. Each triangle forces a vertex outside the two independent color classes, while each of the three distance3 colors can occur at most once. Thus four required vertices cannot fit three available slots. Conjecture7 then calls G11 the only exception among claw-free subcubic graphs.

For literal graphs not required connected, G11 disjoint-union G11 is still claw-free and subcubic, is not isomorphic to G11, and any purported coloring restricts to a forbidden coloring of either copy. This supplies the full bridge for a wording/domain exclusion. It is entirely inherited from the source's own witness, rather than a substantive new obstruction. The connected unique-exception classification remains unproved. The graph drawing/adjacency certificate was not independently reconstructed; no complete dependency audit is claimed. The source proposition's proof was read, not its full surrounding paper.

## 352845: full classical bridge for the exact series

The retained arXiv2112.03361v1, section2.7, pp16-17, Fact2.25 and Conjecture2.26, is the exact source. It already gives

S = (1/2) integral_0^1 arcsin(x) log(x)^2 / x dx.

This follows from the arcsine power series and integral_0^1 x^(m-1) log(x)^2 dx=2/m^3. All summands are nonnegative, so Tonelli justifies exchanging sum and integral, including the endpoint limit. Integration by parts with v=log(x)^3/6 gives

S = -(1/6) integral_0^1 log(x)^3 / sqrt(1-x^2) dx
  = -(1/6) integral_0^(pi/2) log(sin t)^3 dt.

Boundary terms vanish since arcsin(x) log(x)^3 tends to zero at0 and log(1)=0. Define

F(a)=integral_0^(pi/2) sin(t)^a dt
    =sqrt(pi) Gamma((a+1)/2)/(2 Gamma((a+2)/2)), a>-1.

The beta identity follows directly by substituting u=sin(t)^2. Three derivatives at a=0 may pass inside the integral: for |a|<=1/2, sin(t)^(-1/2)(1+|log sin(t)|^3) is an integrable dominating function. Put L=log F. Standard gamma differentiation gives

F(0)=pi/2,
L'(0)=-log2,
L''(0)=pi^2/12,
L'''(0)=-3 zeta(3)/2.

For completeness, the last two constants follow from
psi_m(z)=(-1)^(m+1) m! sum_(j>=0) (j+z)^(-m-1) for m>=1:
psi_1(1/2)=pi^2/2, psi_1(1)=pi^2/6;
psi_2(1/2)=-14 zeta(3), psi_2(1)=-2 zeta(3).
The first difference psi(1/2)-psi(1)=-2log2 follows by differentiating gamma duplication (or subtracting harmonic series).

Using F'''=F((L')^3+3L'L''+L'''),

S = pi log(2)^3/12 + pi^3 log(2)/48 + pi zeta(3)/8,

exactly Conjecture2.26's RHS. This is a full applicable beta-derivative bridge starting at the source's own integral, not an assertion that shortness makes a theorem routine. Its constants, endpoint/exchange justifications and universal series endpoint are explicit. The source's preceding theorem proofs are not used. No independent literature-priority assertion or claim that a specific prior paper states this exact endpoint is made. Published correspondence, current registries and a complete external dependency audit remain HOLD. This is uncredited classical source adaptation, not a proposal, manuscript or formal certificate.

## 404655: source-qualified route parked

The retained published OWR6/2024 report, Christian Bean with Anders Claesson, pp293-294, explicitly states the Av(231,1324) inversion-monotonicity question. It defines the inversion statistic, gives the maximum-element structural decomposition, two-variable q-generating-function equations and finite verification through n=240. Those are primary-body statements, not a proof of the conjecture.

Appending a new maximum to 132 creates1324. Prepending a new minimum to213 also creates1324 (after standardizing to1324). Both input permutations avoid231 and1324, so the simplest inversion-preserving injections fail on valid inputs. The report's q-integral equation mixes size and inversion weights and is not by itself a coefficient-positive proof for the difference of consecutive size slices. No replacement injection or positive coefficient identity was obtained. No finite sweep undertaken. Closest successor-body search and live registry clearance remain incomplete; PARK rather than a novelty claim.

## 336882: fixed-rank scheme, not just invariant lines

The retained arXiv1708.06076v2 (14 June2018), Definition5.37, defines G^T inside Gr(k,V) by vanishing of E -> V -> V/E, functorially on test schemes. Thus the scheme structure matters; the reduced variety of invariant subspaces is not the question. Example7.6 gives a single-Jordan-block dual-number tangent witness at its unique closed point. Conjecture7.7 then asks nonreducedness for nonzero nilpotent T in general. Conjecture7.8 is a distinct reduced-subscheme/shuffle-equation claim.

For k=1 one might study the eigenline scheme; that does not answer all intended nontrivial ranks. A tangent vector at an arbitrary mixed-block point need not witness nilpotents, since a positive-dimensional reduced scheme also has tangent vectors. Endpoint k=0 or dim V would merely expose missing rank restrictions. No full mixed-Jordan-block mechanism survives these objections. Source version2 read; separate published correspondence, closest successor proof bodies, and current registry coverage not checked. PARK; no general nonreducedness claim.

Precision on the 381643 obstruction index: Theorem2 literally states H_j is not a (j-1)-interval PCG. Thus to obtain an obstruction to k-interval PCGs use H_(k+1). Theorem14's proof calls the needed obstruction H_k informally; its argument is read with this harmless reindexing. In the exact t=2,k=1 specialization, H_2 (15 vertices) is the obstruction fed into the induced-density theorem, not the final host R. No certificate-size improvement is credited.
