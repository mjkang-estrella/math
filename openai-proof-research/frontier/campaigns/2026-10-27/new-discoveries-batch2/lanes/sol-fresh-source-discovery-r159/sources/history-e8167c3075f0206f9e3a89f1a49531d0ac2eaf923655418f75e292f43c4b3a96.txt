# Gösmann nilpotent Kac conjecture: unresolved, eligibility HOLD

No full discovery, nomination, formal proof, or count credit.

## Exact primary question and chronology

Lydia Gösmann, *A nilpotent version of the first Kac conjecture*, arXiv:2610.37207v1, submitted 27 October 2026 13:24:38 UTC. Read the actual HTML and source, especially Definition 3.1, Conjecture 3.3, Proposition 4.2, Lemma 4.3, Sections 5–6. The current abstract record was obtained at 09:40:55 UTC on 29 October; no journal counterpart is identified in the retrieved record. This is a preprint target, not a claimed published open question.

For **every finite quiver Q**, with loops and parallel arrows permitted, and **every dimension vector d**, the question is

    dim g_Q^nil[d] = A_d^nil(0).

Here A_d^nil(q) counts absolutely indecomposable nilpotent representations over F_q. With Euler form <e,d> = sum_i e_i d_i - sum_(i→j) e_i d_j, the Lie algebra has a generator of degree s_i for each loopless vertex, and one generator of degree d whenever its support is strongly connected and both <d,s_i> and <s_i,d> are nonpositive for every i. Relations are commutation when the symmetrized Euler pairing is zero, and the stated real-simple-root Serre relations. This is the whole conjecture, not positivity of the polynomial or a fixed degree.

**Major eligibility warning visible in the actual introduction:** the author announces that a proof will appear in a forthcoming joint paper with L. Hennecart. Exact-title/author public searches did not locate that joint proof. This is an announced resolution, not evidence that the conjecture remains genuinely unclaimed. No priority clearance is possible from this lane. Do not invest in Lean on this evidence.

## Economical exclusions before selection

The complete-evolution-algebra paper 2512.12418v1 was read. Its Conjecture 3.6 (solvable iff no nonzero idempotent) is already publicly refuted, including Meta's 2 October publication. Omega's actual pinned `barei-2026-remark-3-5-minimal-idempotent.md` was fetched and read: it supplies a five-dimensional evolution algebra with a three-dimensional minimal idempotent subspace, and even a written arbitrary-dimensional family. Those questions are excluded, not proposed here. The Toeplitz paper's actual June 2026 journal body already characterizes rank-one/determinant preservers over R/C; its finite-field/quaternion suggestions are broad classification projects. A few small-field exceptions would be parameter cases and do not meet the mission. No theorem-error correction is nominated. The lattice paper did not supply a precise fresh numbered conjecture in the inspected text.

## Source and classical subsumption comparison

Bozec–Schiffmann–Vasserot, 1701.01797v1, actual Sections 1.1, 1.4–1.5: Proposition 1.2 constructs integer nilpotent/1-nilpotent counting polynomials; Theorem 1.4 concerns point counts and generating functions. The distinction is material: without loops, 1-nilpotence imposes no condition, but full nilpotence still does. The primary preprint lists the published counterpart Ann. Sci. ENS 53(6) (2020), 1501–1544, DOI 10.24033/asens.2452; the journal body was not independently fetched, so its final textual equivalence is not certified here.

Gösmann–Reineke's actual published SIGMA 22 (2026), 020, *Motives of Nullcones of Quiver Representations*, DOI 10.3842/SIGMA.2026.020, was fetched and text-read at Theorem 2.1, Corollary 3.3 and Section 3.2(3). It already gives the all-one acyclic-support stratification used below. Thus that mechanism is known, not a new theorem of this lane.

Davison–Hennecart–Schlegel Mejia, 2303.12592v4 (14 February 2024), actual Theorem 1.1 and Section 9.4 Proposition 9.13, gives a universal-enveloping/BPS generalized Kac–Moody framework. A description by unspecified cohomological generator spaces is not the explicit generator multiplicity statement above. The missing step is exactly the degree-zero generator-space calculation in Gösmann's Conjecture 6.1: dimension one on the Definition 3.1 degrees, zero otherwise. The retrieved v4 has not been established as the latest version; no claim to have cleared its later revisions or a published counterpart.

The original source already proves the no-oriented-cycles-except-loops case and the negative-enough Euler-form case. Reproving them earns no credit. The classical ordinary Kac theorem, or the symmetrized Euler matrix by itself, cannot identify the fully nilpotent invariant: the exact triangle comparison below obstructs that shortcut.

## Exact squarefree stress test

Restrict temporarily to loopless simple directed quivers, and d=(1,...,1). This restriction is an experiment, not the target.

For any subset F of arrows, give those arrows nonzero scalars and all others zero. Nilpotence is equivalent to F being directed acyclic. Absolute indecomposability is equivalent to connectedness of the underlying undirected support: an endomorphism acts by scalars at the vertices and each nonzero arrow forces the two scalars equal. This endomorphism algebra stays the base field after extension. On a connected support, the base-change torus has stabilizer the diagonal scalars. Its orbits number (q-1)^(|F|-n+1), by normalizing a spanning tree, independently of field. Therefore the exact polynomial is

    A_1^nil(q) = sum_(F connected and directed acyclic) (q-1)^(|F|-n+1).

No interpolation or floating-point arithmetic is involved.

For the Lie side in squarefree degrees, the usable generators are single vertices and strongly connected induced vertex sets of size >=2. Positive-degree relations involving a repeated real vertex cannot contribute to a squarefree degree (apart from the exponent-one commutations for zero pairing). Two disjoint generator supports commute exactly when there is no arrow between them in either direction. Thus the squarefree component can be tested by the usual partially commutative enveloping-algebra clique series and PBW logarithm.

The script constructs a squarefree polynomial D with constant term one. For a vertex set S, D[S]=(-1)^c if every connected component of Q[S] is either a singleton or strongly connected, where c is the number of such components, and D[S]=0 otherwise. Products are computed in Z[x_1,...,x_n]/(x_i^2). The proposed Lie multiplicity is the coefficient of -log D. The code computes it integrally by -D^(-1)*(x_1 partial_1 D): at the full squarefree monomial this derivative does not change the desired coefficient. This avoids rational rounding and explains the independent combinatorial calculation. The classical clique/PBW reduction is not an independently formalized certificate in this lane.

Results: all simple directed loopless quivers on n=1,2,3,4 vertices (1+4+64+4096=4165), and 80 seeded five-vertex sparse quivers, agree exactly: 4245 comparisons, zero mismatches. No claim for loops, parallel arrows or repeated dimension coordinates. The script imposes hard 512 MiB address-space, 50 CPU-second and 60 wall-second limits before enumeration, with BLAS thread variables one and seed 20261029.

## Strongest concrete falsifier of a tempting route

Take the directed triangle 0→1→2→0, and the acyclic triangle 0→1→2 with 0→2. Their symmetrized Euler matrices are identical. In the cyclic case every connected acyclic support is one of the three spanning paths, so A_111^nil(q)=3. In the acyclic case the three spanning trees and the full support all contribute, giving A_111^nil(q)=3+(q-1)=q+2. The constant terms differ, 3 versus 2. Thus symmetrized-form-only or ordinary orientation-invariant Kac arguments fail. The proposed source algebra correctly compensates with a degree-(1,1,1) generator for the strongly connected orientation. This is **not** a counterexample to the conjecture; it explains why the conjecture has its orientation-sensitive definition. Source tables already contain the directed-cycle value. No novelty credit for this example.

## Precise remaining gap and recommendation

No uniform identity for arbitrary dimension vectors has been proved, and no literal in-scope counterexample has been found. Repeated coordinates require the full Serre ideal, nontrivial automorphism groups and plethystic Adams terms; none is controlled by the squarefree support calculation. Neither more small-quiver tests nor a proof restricted to all-one dimensions would fulfill the full source question.

Strongest objection in full: an author-announced full proof may already exist or follow from the BPS restriction theorem with its intended local cohomology calculation. Moreover, all computational progress here is a restricted check built from published support stratification and classical PBW machinery. It is ineligible as a substantive new discovery even if the finite results are correct. The exact unresolved mathematical bridge is Conjecture 6.1 for all degrees; the exact eligibility gaps are the announced joint proof, later companion versions, current registry heads, and full classical subsumption. Recommend HOLD/no further formal investment, credit 0.
