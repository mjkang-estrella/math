# TS132: a transitive superquadratic sensitivity separation

Author proof for independent review; no mathematical PASS, contribution verdict, acceptance or count is asserted. The full scope is the unchanged `original-scope.md`, SHA256 `4f4f5103561d77dd475a5b8f50bbcd0d8989e102c18392ace80cb0b52a735984`.

**Theorem.** For every real C>0 there is a nonconstant total Boolean function f on finitely many bits, invariant under a group transitive on all its input coordinates, with f(0)=0 and bs(f,0)>C s(f)^2. Moreover there are a fixed alpha>2 and such functions F_m with bs(F_m,0)>=s(F_m)^alpha and bs(F_m,0) tending to infinity.

Here s is maximum ordinary single-bit sensitivity over all inputs, not spectral sensitivity or an average. Blocks in bs(f,0) are nonempty and pairwise disjoint. Transitivity means an actual coordinate-permutation subgroup of S_n preserving f, not merely an action on some selected certificates or rows.

## 1. Credited source operations and the new interface

Let S denote the pinned OpenAI manuscript *A superquadratic separation between sensitivity and block sensitivity*, September25,2026, at revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The seven retained non-PDF blobs are authenticated against the complete preprints tree; the full four mathematical sections were read. S is stipulated true, not audited.

S supplies the nested Hamming-ball predicates, gated-tournament recursion, four ordinary/joint sensitivity inequalities, OR balancing, and composition amplification. Its independent random edge labels need not preserve any transitive action on the entire child-coordinate set. The new operation below supplies a deterministic labelled tournament with both the required constant forbidden-pattern bound and a transitive action on row-position pairs. The recurrences are reproduced with their exact dependence on the gate degree, label count and forbidden-pattern bound, so the replacement does not rely on a numerical experiment or an unstated invariance of a random realization.

Gated tournament clauses and Paley/cyclotomic symmetry have close antecedents in Meiburg, arXiv:2608.00851v1, especially §§3.1,5.1–5.3,6.1. We do not claim these ideas, OR balancing, wreath-product symmetry or powering as new. The contribution question concerns the uniform first-difference exclusion mechanism combined with the all-input ordinary/joint recursion; it requires a separate review.

## 2. An equivariant labelled tournament

Let p be a prime congruent to3 modulo4. Write H=(F_p^*)² for the nonzero quadratic residues, so |H|=r=(p−1)/2 and −1 is not in H. Let V_h=F_p^h. For distinct u,v, let j(u,v) be the first coordinate where they differ, and set

  u→v iff v_j−u_j belongs to H;
  a(u,v)=v_j−u_j in H when u→v.

Exactly one orientation holds because exactly one of a nonzero element and its negative is in H. This is the h-fold lexicographic product of the Paley tournament of order p. Its outdegree at every vertex is

  r sum_{j=1}^h p^(h−j)=(p^h−1)/2.

Call I⊆V_h head-constant if there are labels m_v∈H, v∈I, with a(u,v)=m_v for every internal edge u→v.

**Lemma 1 (uniform exclusion).** Every head-constant I⊆V_h has |I|≤3^h.

*Proof.* For h=0 there is only one row. For h≥1 partition I into nonempty first-coordinate fibers I_c. The distinct first coordinates form a tournament with c→e iff e−c∈H. If two distinct first-coordinate values c,c' both point to e, choose u∈I_c, u'∈I_c', and v∈I_e. Then head-constancy gives e−c=a(u,v)=m_v=a(u',v)=e−c', impossible. Thus each vertex of the quotient tournament has indegree at most1. If there are b fibers, b(b−1)/2≤b, so b≤3. Within a fiber, delete the common first coordinate. Every internal edge and its label is defined by the remaining coordinates; the same m_v certify head-constancy there. Induction bounds each fiber by3^(h−1), giving |I|≤3^h. This includes fibers of size1 and labels unconstrained by incoming edges. ∎

**Lemma 2 (full child transitivity).** The maps

  (v,c)↦(λv+b, λc),  λ∈H, b∈F_p^h,

form a group of permutations of V_h×H. They act transitively on this set, preserve tournament orientation on rows, and satisfy a(λv+b,λw+b)=λ a(v,w) for every edge v→w.

*Proof.* A nonzero scalar preserves the first differing position. Multiplication by a square preserves membership in H and multiplies that coordinate difference by λ. Translations cancel from differences. Given (v,c),(w,e), choose scalar λ=e/c∈H and translation b=w−λv. This sends the first pair to the second. Composition and inverse have the same affine form. ∎

For the rest of the proof use h=4, k=p^4 and t=82. Lemma1 says no set of t rows is head-constant. Write A=(k−1)/2 for the gate degree and M=ceil(sqrt(A)). In particular A≤M². The letters k,r,M,t now refer to these values, not to S's original relation k=2M²+1 or t=16.

## 3. Nested total predicates with a common transitive group

Fix an integer depth d≥1, set L=d+2, H_l=d+1−l for0≤l≤d, and N_l=LM(kr)^l. On the LM base coordinates choose M disjoint blocks E_1,...,E_M of size L. Let z_i be the indicator of E_i, and D(x)=min_i dist_Ham(x,z_i). For1≤q≤H_0 set

  P_{0,q}(x)=1 iff D(x)≤H_0−q.

At level l≥1 put Q=H_{l−1}=H_l+1 and arrange the input in kr disjoint children x_{v,c}, v∈V_4,c∈H, each of length N_{l−1}. Define P_{l,q} to be the OR, over rows u∈V_4, of the clause

  P_{l−1,Q}(x_{u,c})=1 for every c∈H,
  P_{l−1,Q−q}(x_{v,a(u,v)})=0 for every edge u→v.

All predicate indices are valid:1≤Q−q<Q. The predicates decrease with q, since the gate tested at a smaller child index is larger and harder to require zero. Every clause uses r+A distinct children: its own row and one position in each outgoing row. This defines total functions, including at all malformed or unstructured raw bit inputs.

At level0 the group permuting the M equal blocks and independently permuting their L bits acts transitively and preserves every P_{0,q} simultaneously. Inductively, take independent copies of the common child group on every child and the affine row-position group from Lemma2, acting by permuting whole children with the canonical identical coordinate indexing. The child groups preserve all tests. The affine group sends the entire clause of u to the clause of au+b, by covariance of the labels, including both targets and gates. Thus it preserves every parent predicate. To send one raw coordinate to another, first use the affine action to send its child to the destination child, then the destination child group to send its internal coordinate to the required coordinate. The generated group is therefore transitive on all N_l bits and preserves the whole nested family simultaneously. This simultaneous invariance is essential because each clause uses two different child indices.

## 4. All-input sensitivity bounds

For b∈{0,1}, let S_{l,b} be the largest b-side ordinary sensitivity of any P_{l,q}. Let J_{l,b} be the maximum number of single raw bits which change both P_{l,q} and P_{l,q'} from b to1−b at the same input, over distinct q,q'. Empty maxima are zero.

At level0,

  S_{0,0}≤L, S_{0,1}≤LM, J_{0,0}=J_{0,1}=0.             (1)

Indeed, at a rejecting input a successful flip approaches a center at distance R+1≤d+1, where R is the predicate radius. At most one center can lie this close: centers have mutual distance2L=2d+4. There are at most R+1≤L successful flips. The one-side bound is the number LM of coordinates. D is1-Lipschitz in Hamming distance, so one flip cannot cross two distinct integer radii in the same direction; this proves both joint bounds.

For each l≥1 the exact recurrence interface is

  S_{l,1}≤A S_{l−1,0}+r S_{l−1,1},
  J_{l,1}≤A J_{l−1,0}+r S_{l−1,1},
  S_{l,0}≤t S_{l−1,0}+S_{l−1,1}+3J_{l−1,1},
  J_{l,0}≤t S_{l−1,0}+3J_{l−1,1}.                       (2)

These are S's four recurrences with A in place of M² and t=82, justified as follows.

For a transition from one, fix a satisfied clause. Every successful flip must break one of its A gates or r targets, giving the first inequality. For a joint transition at q<q', fix a clause satisfied for the stronger parent q'; it also holds for q. Breaking a target costs at most r S_{l−1,1}. If no target breaks, making even the weaker parent q false must break a gate at index g=Q−q. Initially the two gate indices g'=Q−q'<g are both zero; afterward the larger index g is one, so nesting makes g' one also. Each gate therefore costs J_{l−1,0}. This proves the second inequality.

At a zero input and fixed parent index q, list clauses failing exactly one target and no gates (T), and clauses failing exactly one gate and no targets (G). The lists are fixed before selecting a flip. Each raw flip affects only one child, hence only one condition of each clause, so every clause it can make true is on one of these lists.

For v∈T let m_v be its unique failed target position. If u,v∈T and u→v, the passing gate of u in row v says the weaker child predicate at position a(u,v) is zero, and hence the strongest predicate is zero. Uniqueness of the failed target gives a(u,v)=m_v. Lemma1 bounds |T|≤81<t. Each such clause has at most S_{l−1,0} repairs.

All target predicates in each row belonging to G are true. Every internal edge u→v in G therefore forces a failed gate of clause u. Since a member of G has just one failed gate, its induced outdegree is at most1, and |G|≤3. At most one member has induced outdegree0. Every other member has its unique failed gate in a row whose targets are all true. Repairing it from one to zero changes both its weaker gate index Q−q and the strongest child index Q, which are distinct, from one to zero. Thus its cost is at most J_{l−1,1}; the possible exceptional member costs at most S_{l−1,1}. This proves the third inequality, with harmless overcount3.

For a joint zero-to-one transition at q<q', form these same fixed lists for the weaker parent q. A clause true for q' after the flip is also true for q afterward and so lies on one of those lists. T costs at most t S_{l−1,0} as before. For a G witness, its unique failed gate at the weaker parent q has child index g=Q−q initially one. The smaller index g'=Q−q' is initially one by nesting. The final stronger parent clause requires g'=0 and hence g=0. Both distinct indices change, even for the exceptional member of G; each costs at most J_{l−1,1}. This gives the fourth inequality. A clause that has another unrepaired failure at q' cannot be a final witness and contributes nothing. Union bounds allow the same raw bit to affect several clauses. Thus (2) holds at every raw input, without restriction to the zero witness or to distinct Hamming balls.

Choose the prime p≡3 mod4 so large that

  p≥max(167,3^(d+1)).                                    (3)

Such primes exist arbitrarily far out by the elementary infinitude of primes3 mod4. For example, if all such primes divided a fixed product P, a prime factor congruent to3 mod4 of4P−1 would not divide P.

Since M≥p²/2, r=(p−1)/2 and t=82, we have

  epsilon=max(r,t)/M≤1/p≤2/3^(d+1).                      (4)

(The estimate t/M≤164/p²≤1/p uses p≥167.) Define u_l=max_b S_{l,b}/M^(l+b) and v_l=max_b J_{l,b}/M^(l+b). From A≤M² and (1)–(2),

  u_0≤L, v_0=0,
  u_l≤(1+epsilon)u_{l−1}+3v_{l−1},
  v_l≤epsilon u_{l−1}+3v_{l−1}.                           (5)

For completeness, compare with equality sequences U_0=L,V_0=0 and the right-hand sides of(5). Their coefficients are nonnegative. Simultaneous induction gives U_l≤2L and V_l≤epsilon L(3^l−1) for0≤l≤d. For V_l this follows from U_{l−1}≤2L. For U_l, sum its increments using the bounds at earlier indices:

  U_l≤L+epsilon L[(3/2)(3^l−1)−l]<2L,

because (4) makes the bracketed increment factor at most
(3^(l+1)−3−2l)/3^(d+1)<1. Consequently

  S_{l,b}≤2L M^(l+b).                                    (6)

## 5. Disjoint witnesses and the every-C conclusion

At level0 every predicate is zero at0, and flipping any E_i makes all predicates one. Inductively there are M k^l pairwise disjoint sensitive blocks at0, all of size Lr^l, whose flips make every P_{l,q} one. Given a preceding-level block B, take its identical copy in every one of the r children of one row and take their union. Flipping that union makes all strongest targets in that row one; every outgoing gate is in another row left at zero, where every child predicate is zero. Unions for different rows or disjoint child blocks are disjoint and nonempty. This proves the assertion and also P_{l,q}(0)=0, since at zero every target fails.

Let f be the OR of M disjoint copies of P_{d,1}. It is a total Boolean function on

  n=L M²(kr)^d

coordinates. Independent copies of the common transitive child group, together with all permutations of the M equal copies, preserve f and act transitively on all n coordinates. At a rejecting input every copy rejects, so sensitivity is at most M S_{d,0}. At an accepting input, if two copies accept no single flip changes the OR; if exactly one accepts, all sensitive bits belong to that copy. Therefore (6) and the disjoint witness construction give

  s(f)≤2L M^(d+1),  bs(f,0)≥M² k^d,  f(0)=0.             (7)

In particular f is nonconstant and s(f)>0.

For p≥167 we have M≤sqrt(A)+1≤3p²/4+1≤4p²/5, since p²≥20. Hence

  k/M²≥25/16>3/2.

It follows from(7) that

  bs(f,0)/s(f)²≥(k/M²)^d/(4L²)≥(3/2)^d/[4(d+2)²].       (8)

The last expression tends to infinity with d. Given C>0 first choose d making it greater than C, then choose a prime satisfying(3), and construct f. This proves the full every-C statement, not only a fixed factor or a spectral variant.

## 6. One fixed power and transitivity under composition

Take d=20 and any one prime satisfying(3). For the resulting fixed seed put

  A_*=44 M^21,  B_*=M²k^20.

Then s(f)≤A_*, bs(f,0)≥B_*, and

  B_*/A_*²≥3^20/(2^20·1936)>1,

because3^20=3486784401 and2^20·1936=2030043136. Thus alpha=log(B_*)/log(A_*)>2.

Define F_1=f and F_{m+1}=f composed with independent copies of F_m in its n input positions. For total functions g,h, every sensitive bit of g∘h lies in a child sensitive for h whose output coordinate is sensitive for g, so s(g∘h)≤s(g)s(h). If h(0)=0, disjoint sensitive block families C_i for g at0 and D_j for h at0 give disjoint nonempty blocks C_i×D_j for g∘h at0. Thus bs(g∘h,0)≥bs(g,0)bs(h,0). These are the credited composition operations in S.

Coordinate transitivity also persists: use an automorphism of the outer function to move the child index and then an independent automorphism of the inner function to move the coordinate within that child. Both operations preserve the composition; their generated subgroup is transitive on the product coordinate set. Therefore every F_m is total, coordinate-transitive and zero at0, and

  s(F_m)≤A_*^m,  bs(F_m,0)≥B_*^m≥s(F_m)^alpha.

Since B_*>1, these block sensitivities tend to infinity; in particular every F_m is nonconstant. This completes both parts of the unchanged target. ∎

## 7. Review boundaries

No numerical test establishes an infinite-family claim here. All parameters and inequalities are analytic. The small finite diagnostics separately test the new label action and pattern bound, including the sharp p=3 boundary; they are not proof certificates for the huge seed. No claim of cyclic invariance, full symmetric invariance, graph-property structure, minterm-transitivity, optimal exponent, small circuit or efficient truth-table construction is made. No theorem is formalized here. Primary literature limits and the comparison with Meiburg's already symmetric cyclotomic suggestion are recorded separately for independent contribution review.
