# Source203: effective classification, prefreeze derivation

PREFREEZE. One selected family only: Donovan finiteness and its integral companion. No exact full theorem has been frozen. The working question is a uniform algorithm taking a prime p and an integer M and returning a finite, complete list of ACTUAL finite-group blocks, up to integral Morita equivalence over W(Fbar_p), for all defect groups of order at most M, with a certificate that no class is missing. No abelian-defect, bounded-ambient-group, split-fraction-field, or restricted-residue replacement is intended. This is an exploratory question, not a claim that a project or literature novelty gap has been established.

The source's exact integral comparison and all actual inner factors are paid inputs. Integral03's grading rigidity includes all finite grading groups; integral07 already treats each fixed ramified complete DVR by Witt/Cohen extension and central-idempotent lifting. r32's action family collapses under equivariant Morita equivalence and is not a counterexample to these operations. r75 already credits Eisele's Proposition5.1 conditional bound on transported p-permutation module ranks; no Puig/Broue/G104 target is replaced here. I104's stopping concern is credited rather than reintroduced as a new discovery.

## First integrated reduction: finite fields do not need an extra cyclic descent cocycle

For an integral basic order R, a Morita equivalence R~sigma^m R is an isomorphism of basic orders. If all periods are bounded by m0, let L=lcm(1,...,m0). Iterating yields an isomorphism R~sigma^L R. EEL2020 Proposition3.2 and Theorem3.3 prove the full integral Lang descent: write this map as a semilinear operator, solve a matrix Lang equation over W(Fbar_p), and take a fixed basis. The order then has a W(F_(p^L))-form. It is WRONG to leave a cyclic cocycle obstruction unpaid here: the matrix Lang construction already removes it. Its iterative equation x-x^(p^L)=z has solutions over Fbar_p at every step. At finite precision the coefficients are computable over finite extensions if the input comparison is computably supplied. No infinite precision algorithm is asserted from this observation.

This says nothing about the minimal coefficient field of the original group block idempotent. Defect-zero blocks can have unbounded coefficient fields, but all their basic W(Fbar_p)-orders are W(Fbar_p). Confusing these two fields would fabricate an obstruction.

## Second integrated reduction: explicit finite-index enumeration

EEL2020 Proposition3.8 supplies the stronger operation than generic compactness: if a symmetric order Lambda over O0 has defect d and generic rank r, after placing it in a maximal order Gamma one has length_O0(Gamma/Lambda)<=e*d*r/2, where e=v_pi(p). In the unramified Lang descent e=1. Put t=floor(d*r/2). The elementary-divisor theorem then gives p^t Gamma subset Lambda subset Gamma. Thus every such order is the inverse image of a unital subalgebra of the FINITE ring Gamma/p^t Gamma. For t=0, the only lattice is Gamma; this case is handled separately. Multiplicative closure and containment of 1 are finite tests. This is stronger than producing increasingly accurate multiplication tables: an inverse image is an actual complete order, with its multiplication inherited from an explicitly specified generic algebra.

For rank r and q=p^L, the additive group of Gamma/p^t Gamma has q^(tr) elements. Brute force over its subsets, followed by additive, O0-scalar, unit and multiplication checks, is finite. A coarse upper bound is 2^(q^(tr)); no useful complexity bound is claimed. Enumerating submodules in Hermite form is a more efficient but unnecessary improvement. Maximal orders are unique up to generic conjugacy for these local semisimple algebras, so one representative per generic algebra suffices. The generic algebra need not be split over O0's fraction field; it is a product of matrix algebras over division algebras with finite-extension centers. Passing to a split generic algebra without retaining this data is not justified.

EEL Proposition3.4 identifies the finite remaining generic-algebra data via finite extensions and local Hasse invariants. Actual primary algorithmic local-field enumeration must still be read before claiming this enumeration as implemented. Symmetry descent and the defect-index bound are taken with EEL's actual hypotheses, not asserted for arbitrary finite orders. Keeping all intermediate suborders as an OVERLIST avoids needing a symmetry recognition algorithm; it does not turn them into actual group blocks.

## Third integrated reduction: actual crossed systems

Integral04 proves exact Teichmuller normalization, and integral05's induced comparison gives an actual Morita equivalence of Sylow crossed orders. The group Gamma_S is built on Nbar times S with (g,s)(h,t)=(g alpha_s(h)n_(s,t),st). Its defect is bounded by |S| times that of the identity block. Consequently the preceding finite-index list applies to actual Sylow restriction blocks once the numerical Cartan/period bounds are supplied.

Integral03 then retains group labels and identity marking, using fixed total rank, HH1=0 and finite Out. Integral06 removes the unbounded p'-kernel without bounding its matrix sizes: determinant-one implementers have discrepancy gamma with gamma^n=1 and p not dividing n, hence gamma in the Teichmuller group. This preserves the ACTUAL based Sylow restrictions. A naive central-unit cocycle obstruction is therefore already paid.

For a bounded quotient Q with order h, the remaining factor torsor has fibers bounded by H2(Q,T). Principal-unit restriction is injective since cor res=[Q:S] is an automorphism there. The exact sequence for h-th powering on T makes H2(Q,T) a quotient of H2(Q,mu_(h_(p'))). Its cardinality is at most h_(p')^(h*h), by the raw number of 2-cochains. This is deliberately coarse but explicit. If the restricted list has a representatives and the outer action is fixed, there are at most a*h_(p')^(h*h) compatible factor classes. This does not require H2(S,principal units)=0, which is false in general. Computing the fibers requires actual representatives, not just this upper bound.

## Unresolved at this checkpoint

The composition pays finite descent, finite-index order enumeration, exact Sylow comparison, markings, and finite-fiber kernel removal at the stated inputs. It does not yet give a UNIFORM computable p,M bound for every intermediate numerical and representative datum from the actual field companion proof; its geometry/runner/endpoint bodies have not all been read. More significantly, an overlist of algebra orders is not an exact list of actual group-block Morita classes. Enumerating groups and matching encountered basic orders is a positive witness procedure. An upper bound on the number of possible classes alone does not certify that all realizable entries have appeared: unused entries may never be blocks. No block-realizability decision or uniform group-representative-order bound has been produced. This is not a noncomputability claim.

No nominee follows from the finite overlist calculation. Its operations are explicitly from the source, EEL and elementary finite algebra; any quantitative repackaging must face that strongest reduction. No proof/contribution grade is assigned.

## Local-field enumeration closes the generic-algebra navigation gap

After the first checkpoint, Pauli–Roblot (2001), Sections2–5 and Section8 through Algorithm8.5, were read. Their proof gives a finite set, not merely a convergent search: a degree-a extension first has an unramified degree f dividing a, followed by a totally ramified degree n=a/f extension. Over that unramified field, Ore's bound has 0<=j<=n*v_p(n), and the Eisenstein coefficient precision C>1+2j/n suffices by their Corollary5.3. Because the starting field here is unramified, the uniform choice C=2*v_p(n)+2 suffices. Enumerating every residue tuple at that precision, and filtering Eisenstein polynomials, gives a finite covering list; the discriminant restrictions only shrink it. Irreducible finite-field polynomials can be enumerated deterministically instead of the paper's random search. The mass formula is not needed to finish this overlist. Algorithm8.4/8.5 additionally give the isomorphism test and deduplication; their displayed proofs were read, whereas the mass-formula proof and later optimization were not.

For clarity, the Krasner implication used here has a short direct proof. If gamma is closer to beta than to any other conjugate of gamma, every automorphism fixing the base and beta must fix gamma: otherwise the ultrametric inequality bounds |gamma-sigma(gamma)| by max(|gamma-beta|,|sigma(gamma)-beta|)=|gamma-beta|, a contradiction. In characteristic zero, the fixed-field statement gives gamma in the field generated by beta. This is a classical operation, not a fresh bridge.

A very loose explicit bound for the number of degree-a centers over the unramified q-residue field is

    a*q^(a*(2*floor(log_p(a))+2)).

Indeed sum over at most a inertia degrees f; each degree-n Eisenstein tuple at the stated precision has at most (q^f)^(C*n)=q^(C*a) choices. Let E be the sum of these bounds for 1<=a<=c. The local Hasse-invariant classification used in EEL Proposition3.4 allows at most c^3*E possibilities for simple generic factors of dimension at most c: the center, the denominator and numerator of a local invariant, and the matrix size are all bounded by c, with the crude c^3 allowing all three integer choices. Products with total rank at most c have at most c*(max(1,c^3*E))^c possibilities. This is an overcount; the original local Brauer-classification proof and maximal-order algorithms were not freshly read here, so this paragraph is a conditional bookkeeping consequence of that standard EEL input, not a newly verified implementation of it.

The submodule enumeration can also be made much smaller than the first checkpoint's subset bound. Every Oq-submodule of (Oq/p^t)^r is generated by at most r elements, by Smith normal form. Enumerating ordered r-tuples gives at most q^(t*r*r) candidates. For d<=d0 and r<=c, one may thus bound the finite order overlist by

    c*(max(1,c^3*E))^c * q^(floor(d0*c/2)*c*c).

Each actual suborder is recovered as the inverse image of a finite-ring subalgebra, so it is closed at ALL p-adic precisions. No Artin-compatible infinite branch is needed for this step. None of these estimates is nominated: they are direct enumeration consequences of the actual EEL proof, local-field enumeration and elementary divisors. Parameter explicitness alone is not evidence of substantiality.

## A sharp elementary diagnostic for why one reduction modulo p is insufficient

For t>=1, let

    Lambda_t={(a,b) in Z_p x Z_p : a=b mod p^t}.

It has basis 1=(1,1), x=(p^t,0), with x^2=p^t*x, hence Lambda_t=Z_p[X]/(X*(X-p^t)). Its generic algebra is Q_p x Q_p and its maximal order is Gamma=Z_p x Z_p. The index length is t. The bilinear form

    T((a,b),(c,d))=(a*c-b*d)/p^t

has matrix [[0,1],[1,p^t]] in this basis, determinant -1, so the order is symmetric. The two generic trace coefficients are p^(-t),-p^(-t), making the EEL numerical defect t. Therefore their length bound d*r/2=t is attained in this elementary family. The ordinary algebra-trace discriminant is p^(2t), so different t give nonisomorphic integral orders. Yet all reductions modulo p are F_p[X]/X^2. This does not assert that every Lambda_t is a group block. It illustrates exactly why the defect-index operation must be retained instead of replacing integral classification with the field list. It is not offered as a new obstruction theorem or a sharp-parameter nominee.

## Trying to recover actual group realizations

A natural compatible next attempt is to realize a finite-algebra candidate using its finite unit group, rather than to wait blindly for all finite groups. This gives quotient maps, not block summands. For example take A=F_4[X]/X^3 in characteristic2. Its units form a group U of order3*4^2=48; the radical has16 elements. Every radical element z=(1+z)-1 is a difference of units and scalar multiples of1 are in their span. Thus the natural map F_4[U] -> A is surjective. The resulting A-module cannot be projective over F_4[U]: restriction to a Sylow2 subgroup preserves projectivity, projectives over a finite p-group algebra are free, and its dimension3 is not divisible by16. Hence this particular quotient cannot be a block direct summand. This calculation only excludes that unit-group realization; it does not exclude a different group, a Morita realization, or a stronger compatible construction. Adding symmetry to a quotient alone does not supply the missing projectivity.

For the actual source reductions there is more structure: the original automorphisms and actual factors DO construct Gamma_S and an actual Sylow block. That step has been used above, rather than replaced by the failed unit-group route. But after compression and kernel removal the chosen finite representative orders and central factor torsors are not accompanied here by bounded finite-group witnesses for every realizable final Morita class. The source proves coverage of the actual family; it does not supply a rejection certificate for every extra algebra in the numerical overlist.

Suppose, even favorably, that one has computed numerical bounds c(p,M), m(p,M), all comparison/outer-action bounds, and a complete finite overlist. Enumerating group multiplication tables, block idempotents over finite residue extensions, lifted basic corners and possible Morita certificates can witness realizable entries. It cannot stop merely after the observed set has been unchanged for a long time. An upper bound N on the number of classes is not their exact number, and the overlist can have unrealized entries. A compatible operation which either bounds the orders of needed representing groups, decides realizability of each candidate, or gives an independently certified exact realized list would close this route. None is constructed here. Conversely, this is not a proof that such an operation is impossible or absent from all literature.

## Final prefreeze conclusion

The source's numerical and representation-theoretic bounds are accepted as true. The complete extension/periodicity sections now show many of their choices are finite lattice, root-system, character, and group calculations; they should NOT be labeled noncomputable merely because the paper writes “bounded.” The original geometry/families/labels/runners/endpoint proofs and all their transitive primary references were not read in full in this round. Accordingly no claim of having extracted, or refuted the extractability of, a uniform computable bound from the ENTIRE source proof is made. This read limit is distinct from the exact-realization obligation above, which remains in the attempted algorithm even when every numerical bound is granted as an input.

No identifiable nonroutine operation was completed, no full effective classification was obtained, and no statement was frozen. The strongest integrated reduction and its precise remaining obligation are preserved as research. There is no assertion of exhaustion, worldwide priority, impossibility, correctness grade, contribution grade, acceptance or campaign count.
