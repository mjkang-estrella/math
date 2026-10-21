# Source019: full affine reduction and the actual contribution boundary

PREFREEZE / no nominee. This is a feasibility and strongest-reduction note, not a frozen theorem, manuscript, independent review, or supporting-result submission. All statements below are deductions relative to the stipulated pinned proper-curve theorem. The exact explored scope is retained throughout: every prime p; every finite k/Q_p; every smooth geometrically connected affine k-curve U whose smooth proper completion X has genus g and reduced geometric boundary cardinality r with 2g-2+r>0; the FULL geometric and arithmetic étale groups; EVERY continuous section; geometric conjugacy; every rational boundary packet. No good-reduction, rational-point, genus>=2-on-X, prime-to-p, finite-extension, tangential-only or birational-lift assumption is added. Characteristic zero is essential to the local tame description. This scope is exploratory, not an immutable claim freeze.

## 1. Exact paid interfaces

Pinned Source019, October6 main paper, theorem `thm:section`: every proper geometrically connected smooth genus>=2 curve over every finite k/Q_p has bijective point-to-full-section map. Its proof was read, including every analytic collar stage and completion/decomposition-group endgame. Its stronger completion theorem concerns the chosen embedded fields, not just abstract embeddings. None of that is truth-audited. The September24 exterior-sheet companion was also read completely. Neither requires us to redo the analytic argument on a punctured curve: the actual proper theorem can be applied to compactified neighborhoods of a given affine section.

Tamagawa, *The Grothendieck conjecture for affine curves*, Compositio109(1997),135–194, actual Proposition2.8(iv) and proof, pp152–154, already gives the relevant inverse-limit criterion. Its condition(C) explicitly includes p-adic local fields (p151). His word “geometric” includes containment in a boundary decomposition group; it is broader than “point of U”. Every compactified section neighborhood having a rational point implies containment in one decomposition group of the universal normalization. His proof uses compactness of proper rational-point spaces and retains the entire section image. Lemma1.10 supplies arbitrarily high genus covers, and its proof is labeled an exercise using abelian/metabelian covers. These are existing operations, not newly discovered bridges.

Stix, arXiv0809.0017v1, Proposition8, Lemmas9–10, Proposition11/Corollary12, Theorem14 and its actual proof, and AppendicesA–B supply the full cusp packet, injection and disjointness. A local parameter splits the boundary extension; the packet is a torsor under H^1(k,hat Z(1))=lim_n k^*/k^{*n}. Proper injectivity over all finite extensions suffices for packet injection. The source supplies it, and Stix also gives its classical Jacobian-Kummer proof. Reading a published proof that already handles the needed operation rules out claiming that operation as our nonroutine contribution.

The following calculation makes all compatibility steps explicit so that the full scope is actually tested, rather than stopping at a loose appeal to compactness.

## 2. Cofinal high-genus neighborhoods WITHOUT assuming that X has high genus

Fix a representative s:G_k->Pi=pi_1(U) and write Delta=pi_1(U_bar k), S=s(G_k). Then Pi=Delta semidirect S. Delta is a topologically finitely generated profinite surface group. Its open characteristic subgroups form a cofinal system: inside any open subgroup take the intersection of all open subgroups of at most that index; there are only finitely many. Such a characteristic subgroup N is normal in Pi. The subgroup H_N=N S is open, projects onto all G_k, and intersects Delta in exactly N. Its connected finite étale cover U_N->U is geometrically connected over k; s lifts to it. No extension of k is needed to make this neighborhood.

Each geometric cusp inertia group I_i in Delta is an embedded copy of hat Z(1). This is the full horizontal inertia: the residue characteristic at a geometric cusp is zero, although k has residue characteristic p. Injectivity is in Stix Lemma10 (proved after passing to covers with at least two cusps), and Tamagawa Lemma2.2 gives the corresponding full local extension. For any positive integer m, choose an open subgroup of I_i contained in m I_i and extend its neighborhood of the identity to an open subgroup of Delta. By taking characteristic refinements and the finite intersection over the r cusps, one obtains N with I_i intersect N contained in m I_i for every i. Thus the ramification index e_i=[I_i:I_i intersect N] in the geometric Galois compactification cover is divisible by m, in particular e_i>=m.

Put a=2g-2+r>0 and d=[Delta:N]. Riemann–Hurwitz in characteristic zero gives EXACTLY

    2g(X_N)-2 = d(2g-2 + sum_(i=1)^r(1-1/e_i))
                 = d(a - sum_i 1/e_i).

Take m>r/a. Then the bracket is positive, hence g(X_N)>=2. This covers (g,r)=(0,3), (1,1), and all other hyperbolic affine types. It uses no divisibility by a residue-characteristic prime. Since further characteristic refinement increases every e_i, these high-genus neighborhoods are cofinal. Given any open H containing S, first choose N inside H intersect Delta, then impose the same inertia conditions; H_N lies in H.

This is classical cofinal-cover algebra and Riemann–Hurwitz, spelling out Tamagawa's genus step at the required fixed base field. The inequality is not a quantitative nominee; no degree bound or effective construction is asserted. The group may require a very large finite quotient to achieve the chosen inertia orders.

## 3. Source points on the entire cofinal tower are compatible

For each such N, let X_N be the smooth proper completion of U_N. The lifted s maps to a section of pi_1(X_N). Source019 gives a unique x_N in X_N(k) inducing that section. If M is contained in N, the finite map U_M->U_N extends to X_M->X_N. Functoriality sends the section of x_M to the section induced by s on X_N. Source injectivity for X_N therefore forces x_M to map to x_N. This proves compatibility, not just nonemptiness of unrelated rational-point sets.

Consequently every compactified neighborhood X_H has a k-point: refine it by one of these X_N and take the image of x_N. The hypotheses of Tamagawa2.8(iv) now hold. Notice the order: first use proper source existence on the cofinal high-genus tower; then pass to EVERY neighborhood; then apply the classical containment criterion. Merely observing that the pushforward to pi_1(X) is point-theoretic would not have achieved this when g(X)<2, nor would it have identified the full section image over a cusp.

One can also replay the group-theoretic compactness step explicitly. The compatible x_N have one image x in X(k). Choose a geometric prolongation of x to the universal étale normalization and let D be its closed decomposition subgroup of Pi. For a characteristic N as above, the rational point x_N yields a conjugate of D whose image in Pi/N contains S modulo N. Indeed its stabilizer inside H_N projects onto G_k, and H_N/N is precisely the image of S, isomorphic to G_k. A conjugator can be chosen in Delta since S projects onto G_k. Thus

    C_N={delta in Delta : S is contained in delta D delta^-1 N}

is nonempty. It is closed: the quotient modulo N has finite geometric part, the conjugator condition depends on finitely many geometric cosets, and it is the intersection of the closed conditions for elements of S. When M is contained in N, C_M is contained in C_N. For any finite collection choose a common refinement, so these compact sets have the finite intersection property. A delta in their intersection satisfies S contained in delta D delta^-1: for any closed D, intersection_N D N=D when the characteristic N are cofinal in Delta (and conjugation preserves N).

This removes the potential incoherent-conjugator issue. The inverse-limit/prolongation operation is exactly the one in Tamagawa's proof; it is not new. A claim that separate finite-level rational points cannot be assembled would be too weak here.

## 4. All points, all cusps, and all packet parameters

If x belongs to U(k), horizontal inertia is trivial in its étale tower, and D->G_k is an isomorphism. Hence S=D after geometric conjugation and s is the ordinary point section.

If x belongs to (X minus U)(k), the local horizontal sequence is

    1 -> hat Z(1) -> D_x -> G_k -> 1.

A parameter t at x gives a splitting by a compatible system of roots t^(1/n). Every s whose image lies in D_x is a splitting of this entire extension. Modulo its inertia, these splittings form a torsor under H^1(k,hat Z(1)). Hilbert90 and inverse-limit Kummer theory give lim_n k^*/k^{*n}. No prime is omitted, including p; horizontal residue characteristic is zero. A non-rational boundary point cannot support a section of all G_k, since its decomposition-group image is the proper subgroup G_{k(x)}.

Stix Theorem14 gives injectivity of each entire packet into Sect(U/k), disjointness of different packets, and disjointness from U(k). Its proof is stronger than normalizer-of-inertia alone: if two local sections are globally conjugate, apply proper injectivity to their induced points on all high-genus neighborhoods, showing that the conjugator fixes the universal cusp and hence belongs to its inertia. This is precisely why one must not assert injection merely from a chosen local splitting. Ordinary point injection is likewise classical: conjugate point sections lift the same rational point to each neighborhood, then proper injectivity on a high-genus one distinguishes them.

Thus the explored full classification is accounted for by the disjoint union

    U(k)  disjoint_union  union_(x in boundary(k)) Sect(D_x/G_k)
                -> Sect(Pi/G_k),

with each boundary term an H^1(k,hat Z(1))-TORSOR. A canonical identification with the group is NOT claimed without choosing a parameter/tangential origin. With a uniformizer of k, the parameter group has a noncanonical decomposition

    lim_n k^*/k^{*n} = hat Z x O_k^*.

To justify the unit factor: O_k^* is finite-by-Z_p^[k:Q_p], and its power quotients recover its ordinary compact topology. k^* embeds, corresponding to Z x O_k^*. Actual nonzero k-rational tangent vectors supply only this embedded subgroup-torsor; the full cusp packet includes valuation parameters in hat Z outside Z. Replacing all cuspidal sections by tangential sections would silently weaken the explored scope. This distinction is standard Kummer theory, not a new result.

## 5. Two further compatible operations eliminate apparent gaps

First, no extra birational-lift assumption remains in this local full-group discussion. At a rational boundary point, the horizontal birational decomposition group maps isomorphically to D_x in the full U-étale tower: its complete local extension already occurs, as in Tamagawa2.2. A cuspidal section therefore lifts birationally. At an interior rational point, choose a parameter splitting of the horizontal birational decomposition group; it projects to the point section. All such choices are compatible classical operations. Consequently removing additional finitely many points presents no new existence obstruction: a point section at a newly removed point is replaced by any local cusp splitting; previously cuspidal sections lift through the identical horizontal local group. No global number-field conclusion is inferred.

Second, even the natural approximation observation does not supply a nonroutine residual. A basic neighborhood of [s] in the finite-cover topology on section classes is obtained from a finite section neighborhood U_H->U. Its proper completion has a rational point by section3. If this point is a cusp, smoothness and a local parameter give k-points of U_H arbitrarily close to it in the p-adic topology, since only finitely many boundary points were removed. Choose one and map it to U(k). Its point section lies in that finite-cover neighborhood. For a finite collection of conditions use a common section-neighborhood refinement first. This pays density of ordinary point sections in the finite-cover topology, without claiming that the cusp packet is exhausted by tangent vectors or that its valuation coordinates must be actual integers. The local parameters can have valuations tending to +infinity while taking any prescribed residue classes modulo finitely many n: choose A representing the desired compatible congruences modulo M=lcm(n), then A+Mq for q sufficiently large. This gives the elementary compatibility of proximity to the cusp with finite Kummer requirements.

No claim that this topology is the ordinary p-adic topology on the union, no uniform effective degree/radius bound, and no metric assertion is made. These observations are still ordinary finite-cover and p-adic smoothness arguments; no topology-based nominee is submitted.

## 6. Comparison with operative project history and decision

T019S59 has a different scope: every section of the geometrically pro-{p,ell} quotient on proper genus>=2 curves, without a full-section lift assumption. Its r60 source-proof transfer and cyclic-collar argument, and the completed contribution review calling the full target TECHNICAL conditional on correctness, were actually read. They are unchanged. Here we use the full Delta and its available finite covers. We neither deduce the quotient statement from the full theorem nor reuse it as a premise. No renamed quotient target, new grade, or prime restriction is proposed.

R114's symplectic reconstruction is a separate unchanged incomplete exploration. The other protected full/technical/failed scopes named in the standing brief are not weakened or regraded.

The research question initially seemed to require new cuspidalization or relative local lifting. The strongest compatible primary composition instead supplies the full affine classification and the elementary lifting/approximation follow-ons at the explored scope. The low-genus and all-packet quantifiers do not leave an identified nonroutine operation. This is a feasibility conclusion about the deduction, not an independent correctness or contribution verdict.

There is NO substantial full author-proof nominee and NO theorem freeze. The missing campaign objective is an identifiable nonroutine mathematical contribution beyond the credited proper-source/Tamagawa/Stix composition; it has not been found in this one-family investigation. There is no honest reason to invent an unpaid affine bridge after reading Tamagawa2.8(iv). A general global finite-descent equality is NOT supplied by this local argument; Source019 itself retains it as a separate arithmetic hypothesis. We do not turn that statement into a new conjectural nominee or assert its current worldwide status. No impossibility, exhaustion, novelty or priority claim is made. Independent acceptance stages belong to the parent and have not been run.
