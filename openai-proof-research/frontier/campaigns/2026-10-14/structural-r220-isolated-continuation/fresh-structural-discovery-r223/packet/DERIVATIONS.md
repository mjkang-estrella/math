# Source347: integrated prefreeze derivations

Status: PREFREEZE working mathematics, not a frozen author-proof nominee. Codex / GPT-6 Astra / xhigh / default service tier. All five operative source papers at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and their proof operations are stipulated true. The constructions below use those paid operations. Numerical improvements obtained by composing them are not, by themselves, submitted as a substantial discovery. No correctness, contribution, acceptance, or count is assigned here.

## 1. Conventions and interfaces actually used

All homology in the calculations is integral, with ordinary integer homological grading, until an explicitly stated cyclic reduction. Let b(W) be the sum of integral free ranks and let t_i(W)=d(Tor H_i(W;Z)), where d is the minimum number of generators of the finite abelian group. Put

    lambda(W) = b(W) + 2 sum_i t_i(W).

The source stable Morse invariant allows every finite stabilization W x R^k and every signature of a nondegenerate quadratic form, with equality to that quadratic form off a uniform compact core. The integer-chain Smith-form argument gives SM(W)>=lambda(W). For the simply connected closed manifolds of dimension at least nine used below, the supplied handle realization gives an ordinary Morse function with exactly r_i+t_i+t_(i-1) critical points of index i. Consequently Morse(W)=SM(W)=lambda(W). We never infer attainment merely from the chain lower bound. The strongest source attainment is used, including its compatibility with the closed manifolds at hand.

For a finite abelian group with only elementary 2- and 3-primary factors,

    d((Z/2)^a + (Z/3)^q) = max(a,q).

This is not a field-rank statement: the upper bound pairs generators of coprime order to produce generators of order six, and the lower bound follows after quotienting by 2 or 3. At several degrees, the maximum is taken degree by degree before summing. After cyclic grading, the primary ranks are first summed over all degrees in a residue class, then a maximum is taken. The two operations do not generally commute.

The two source projective surfaces S_2 and S_3 have free homology ranks (1,2,2,2,1). Their only integral torsion is T_p in both H_1 and H_2, with T_2=(Z/2)^2 and T_3=Z/3. Thus b(S_p)=8. Product calculations below have a torsion-free second factor, so the integral Kunneth Tor term vanishes. The source integral blowup operation is

    H_i(Bl_Z A;Z) = H_i(A;Z) + sum_(j=1)^(c-1) H_(i-2j)(Z;Z)

for a smooth complex center of codimension c>=2, including all torsion. The normal bundle need not be trivial. The exceptional divisor is its projectivization, with tautological normal line O(-1). The paid proof uses integral Leray-Hirsch and the Thom/Gysin sequence; it is not only a rational Betti formula.

The source simultaneous-projection operation embeds any finite disjoint union of smooth projective surfaces into CP^5. The secant/tangent avoidance includes different components. No uniform embedding or geometric bound as the number of components tends to infinity is asserted.

Let Y be the blowup of CP^1 x CP^1 at its four torus-fixed corners. It is closed, simply connected, Kähler, with free even homology polynomial

    e(u)=1+6u+u^2,

where u records homological degree two. The half-turn g has exactly four fixed exceptional CP^1 components. Its differential is +1 tangentially and -1 normally. It belongs to the Hamiltonian circle action. An exceptional line has Chern number one, so every product X x Y has minimal Chern number one provided X is simply connected (indeed the exceptional sphere alone suffices to make the image of c_1 all of Z).

For a Morse function h on F=Fix(g), average an extension over g to obtain an invariant f. Write psi^t for the Hamiltonian flow of f, with omega(X_f,.)=df, and Phi_epsilon=psi^epsilon g. The supplied proof gives, for sufficiently small positive epsilon, precisely Crit(h) as the fixed points. It proves absence of all other fixed points using Phi_epsilon^2=psi^(2epsilon) and a short-period bound on the compact ambient manifold. Tangentially the derivative is exp(epsilon A)-I with A invertible; normally it is -exp(epsilon A)-I. Both are invertible for small epsilon. The argument is global, not merely persistence of individual points. Concatenating/reparametrizing Hamiltonian paths gives a smooth one-periodic Hamiltonian. For a simply connected ambient manifold every resulting orbit loop is contractible. These are paid source operations, not fresh bridges.

## 2. Profile calculus and the strongest common reduction

Suppose the only torsion of X occurs in pairs of degrees 1+2j and 2+2j, with the same 2-primary multiplicity a_j and 3-primary multiplicity q_j in each pair. All lists are finitely supported, extended by zero. Write a,q for these lists, delta=a-q, A=sum a_j, Q=sum q_j, b=b(X). If B has torsion-free even homology with polynomial k(u), then Kunneth gives profile lists k*a and k*q in the two parities. Therefore

    lambda(X x B) = k(1)b + 4 sum_j max((k*a)_j,(k*q)_j)
                   = k(1)b + 2k(1)(A+Q) + 2 ||k*delta||_1.

There is no hidden torsion cancellation in this equality: the torsion group in each degree is the direct sum of the two elementary primary groups displayed above. A positive convolution coefficient is a free Betti multiplicity of B, not a new primary torsion order.

For c(u)=1+u and e(u)=1+6u+u^2, put C=X x CP^1 and M=X x Y. When the source handle hypotheses hold for both C and M, the involution construction gives

    F := #Fix(Phi) = 4 lambda(C)
      = 8b+16(A+Q)+8 ||c*delta||_1,
    SM(M) = 8b+16(A+Q)+2 ||e*delta||_1,
    SM(M)-F = 2 (||e*delta||_1 - 4||c*delta||_1).

Because N(M)=1, the relevant integral Floer grading is Z/2, not the original integer grading. Each parity contains 8A elementary 2-primary summands and 8Q elementary 3-primary summands. The algebraic minimum rank of the free cyclic integral model in the supplied convention is

    beta(M)=8b+32 max(A,Q).

This is the cyclic integral Floer bound appearing in the sharp source, not ordinary SM and not a sum of maxima taken at integer degrees. Its finite algebraic definition is over Z: the homology is direct-summed by parity and one minimizes the total rank of a finite free Z/2-graded Z complex with that homology. The supplied Floer theorem interprets this invariant as a fixed-point lower bound. This does not assert that a Floer differential is defined over ordinary Z without Novikov completion. The Bai–Xu2022 primary comparison uses the integral Novikov ring Z((T)) after its stated rationalization/approximation step; that analytic coefficient issue is not silently replaced by a field computation here. Assume Q>=A. Since sum c*delta=2(A-Q) and sum e*delta=8(A-Q), the positive-part identities are

    F-beta(M) = 16 sum_j (c*delta)_j^+,
    SM(M)-beta(M) = 4 sum_j (e*delta)_j^+.

In particular the source involution construction attains the cyclic bound exactly when c*delta<=0 coefficientwise. It can simultaneously violate SM precisely when e*delta has a positive coefficient. This separates the two conditions and makes the compatibility question explicit.

Field bounds are different: over F_2 the total Betti number is 8b+32A, over F_3 it is 8b+32Q, and over Q or other prime fields it is 8b. These formulas use universal coefficients, including the shifted torsion contribution. Their maximum happens to equal beta in this paired-parity N=1 situation; that equality is a computed feature, not a general identification of field and integral bounds.

## 3. First combined construction: the seven-center sharp example in CP^9

The sharp source uses two S_2 x CP^1, three S_3, and two S_3 x CP^2 centers. Their maximum complex dimension is four. The simultaneous-projection operation of the dimension-twenty-two source puts any finite disjoint collection of these centers in CP^9. Thus one may use m copies of the seven-center collection there, without retaining the large embedding dimension in the sharp paper.

Set L=6 and f_r(j)=#{(k,l):1<=k<=L-r, 0<=l<=r, k+l=j}. The profiles are a=4m f_1 and q=m(3f_0+2f_2). Then A=40m, Q=42m, b(X)=10+496m, c*delta<=0, and the positive coefficients of e*delta total 8m. The full compatible source construction therefore gives

    dim_R M=22,  N(M)=1,
    #Fix(Phi)=beta(M)=80+5312m,
    Morse(M)=SM(M)=80+5344m.

The deficit is 32m. The geometric and dynamical proofs are exactly the compatible source operations above. This is a useful baseline: neither multiplying the sharp paper's numbers nor retaining its original ambient dimension is the strongest available reduction. It is not advanced as a nominee.

## 4. A stronger ambient product construction in real dimension sixteen

### 4.1 Simultaneous geometry and all parameters

Let a,b be nonnegative integers. In CP^5 embed a+b pairwise disjoint copies of the source surfaces, a of type S_2 and b of type S_3, using simultaneous projection. In A_0=CP^5 x CP^1, take the a centers

    U_i = S_(2,i) x CP^1

and the b centers

    V_j = S_(3,j) x {p_j}.

The surfaces have disjoint images in the first factor, so the centers are pairwise disjoint even if all p_j are equal. There is no false packing or independently free dimension parameter. U has complex dimension three and codimension three; V has dimension two and codimension four. All centers are smooth compact complex submanifolds. Blow them up to obtain X_(a,b). Disjointness means the centers retain the stated normal bundles throughout the finite sequence of blowups. No equivariance of a center under an action on X is required: the eventual involution acts only on Y.

For U the normal bundle is the pullback of N_(S_2/CP^5), of complex rank three. For V it is N_(S_3/CP^5) plus the trivial line T_p CP^1, of rank four. Both are legitimate holomorphic normal bundles; none is assumed trivial. The usual complex blowups are smooth and closed and carry a Kähler form, obtained for sufficiently small positive exceptional sizes from the projective ambient space and projective centers. The construction is also projective. No uniform lower bound on the exceptional sizes as a+b grows is claimed.

A_0 is simply connected. Removing a real-codimension-at-least-four center does not change pi_1, by transverse perturbation of loops and nullhomotopy disks. In the blowup gluing, the sphere boundary of the normal disk bundle has simply connected fiber and pi_1 equal to the center's; the exceptional neighborhood also has pi_1 equal to the center's because its projective fiber is simply connected. The boundary-to-exceptional map is an isomorphism on pi_1. Van Kampen consequently leaves the complement's pi_1 unchanged. Iterating over disjoint centers proves pi_1(X_(a,b))=0. This supplies the actual compatibility even though the centers themselves are not simply connected.

### 4.2 Full integral homology

Use t for homological degree one and u=t^2. Let P_S(t)=1+2t+2t^2+2t^3+t^4. The free-rank polynomial of X is

    P_X(t)=(1+u+u^2+u^3+u^4+u^5)(1+u)
             + a(u+u^2)(1+u)P_S(t)
             + b(u+u^2+u^3)P_S(t).

All integral torsion is described by the two profile lists

    a_profile = 2a(1,2,1),
    q_profile = b(1,1,1),

in paired degrees (3,4), (5,6), (7,8), respectively. This follows directly by shifting the two original surface torsion groups once for each blowup summand. There is no other torsion and no unresolved extension. In particular

    b(X)=12+32a+24b,   A=8a,   Q=3b.

The notation b(X) for a Betti sum is distinct from the integer parameter b in these formulas.

Now set M=X x Y and C=X x CP^1. Their complete integral homology is obtained by multiplying the displayed free polynomial by e(u) or c(u), and convolving each displayed torsion list by the same polynomial. This is a full degree-by-degree specification, not just totals. M is real sixteen-dimensional; C is real fourteen-dimensional. Both are simply connected, closed and Kähler, so the supplied exact handle realization applies. In particular an actual Morse function on each of the four C components has lambda(C) points; its existence is not inferred from a formal complex alone.

### 4.3 Exact cyclic-sharpness cone and deficit

Write x=2a-b and y=4a-b, so delta=(x,y,x). Then

    c*delta=(x,x+y,x+y,x),
    e*delta=(x,6x+y,2x+6y,6x+y,x)
           =(2a-b,16a-7b,28a-8b,16a-7b,2a-b).

If b>=3a, then Q>=A, all coefficients of c*delta are nonpositive, and every coefficient of e*delta except its middle one is nonpositive. Thus the fixed-point construction attains beta and has a positive stable-Morse deficit exactly in the integer cone

    a>=1,  3a<=b<7a/2.

In this cone the formulas simplify to

    #Fix(Phi)=beta(M)=96+256a+288b,
    Morse(M)=SM(M)=96+368a+256b,
    SM(M)-#Fix(Phi)=112a-32b=16(7a-2b).

These are compatible parameter values, not an empty purported regime: b=3a works for every a>=1. The upper endpoint b=7a/2, when integral, has zero deficit and is not included in the positive-deficit statement. If b>7a/2 the source construction remains cyclic-sharp but SM equals beta in this profile family. If 0<=b<=2a, the 2-primary profile dominates degreewise and again there is no stable-Morse deficit; the reverse cyclic-sharpness condition is exactly b<=2a. For 2a<b<3a neither prime dominates c*delta coefficientwise, so this construction does not attain beta. These statements exhaust cyclic sharpness for this two-parameter family, including a=0 and b=0. The paired source mechanism does not produce a cyclic-sharp stable deficit in those boundary cases.

Take a=m,b=3m, m>=1. Then

    dim_R M_m=16, pi_1(M_m)=0, N(M_m)=1,
    #Fix(Phi_m)=beta(M_m)=96+1120m,
    Morse(M_m)=SM(M_m)=96+1136m,
    deficit=16m.

Every fixed point is nondegenerate, every orbit loop is contractible, and there are no other fixed components or points, by the full invariant-extension argument in section 1. The underlying symplectic form is one of the Kähler forms just constructed, times the chosen Kähler form on Y; no monotonicity or asphericity is asserted. The rational field bound is 96+832m, the F_2 bound is 96+1088m, and the F_3 bound is 96+1120m. The ordinary and stable Morse numbers agree here, but neither is identified with the critical number or rational cup length. Those two other invariants have not been computed for M_m.

The normalized deficit tends to 1/71 as m tends to infinity; for m=1 it is 1/77. More generally within the cyclic-sharp positive-deficit cone the ratio tends, along rays b/a=r, to (112-32r)/(368+256r), a strictly decreasing function of r on [3,7/2). Its maximum limiting value is at r=3. This is an exact optimization within this construction, not a universal symplectic inequality.

### 4.4 Why this is not the requested substantial nominee

The lower ambient dimension is obtained by using the CP^1 factor in the ambient space to contain the CP^1 factor of one center, after embedding only the surface in CP^5. All subsequent steps are the supplied simultaneous embedding, integral blowup, handle realization, involution perturbation, and cyclic-chain computations. The parameter-cone calculation is elementary arithmetic of those operations. There is no identified nonroutine operation after that combined reduction. These are retained derivations, not a renamed source theorem offered for acceptance.

## 5. A precise limitation of a smaller source-generated class

There is a provable limitation, but it is restricted and cannot be promoted to a global dimension theorem. Consider only a torsion-free simply connected complex ambient manifold of complex dimension n<=5, blown up at disjoint centers of the exact forms S_p x product CP^(r_l), p=2 or 3, with codimension at least two. Then each center has complex dimension 2+r with r=sum r_l, and r<=n-4. For n<4 there are no such centers. For n=4 only r=0 is allowed: the torsion profile has one entry. For n=5, either r=0 with the two shifts (1,1), or r=1 with a CP^1 factor and one shift, again (1,1). Consequently every center's two paired torsion profiles are scalar multiples of a common nonnegative kernel, the same for both primes. The sums retain that proportionality.

After either c or e convolution, the same prime dominates in every degree. The max operation therefore commutes with both convolutions, lambda(X x Y)=4lambda(X x CP^1), and the source involution cannot yield a stable-Morse deficit. Within exactly this class and using exactly Y, complex dimension six for X, hence real sixteen for M, is the first possible dimension; section 4 realizes it and attains the cyclic bound.

This does not exclude other projective torsion centers, torsion already in the ambient space, odd free homology of an auxiliary factor, non-disjoint or nested centers, different finite-order factors, or a different fixed-point mechanism. The proof is an enumeration of this source-generated center class. It supplies no general lower bound on the dimension of Hamiltonian stable-Morse counterexamples and no priority assertion. It is not a substantial nominee by itself.

## 6. Profile realization and the cost of apparent extra freedom

For the CP^N source constructions let L=N-3. A center S_p x CP^r contributes the symmetric profile

    f_r(j)=#{(k,l):1<=k<=L-r,0<=l<=r,k+l=j}.

If L=2s, then r=0,...,s-1 is simultaneously compatible with the generic projection dimension bound N>=2(r+2)+1. On the first half j=1,...,s, f_r(j)=min(j,r+1). Hence these s lists form an integral basis of all palindromic integer lists of length 2s. Explicitly, for such a list v, put v_0=0 and d_j=v_j-v_(j-1). Its expansion is

    v=sum_(r=0)^(s-1) c_r f_r,
    c_(j-1)=d_j-d_(j+1) (j<s), c_(s-1)=d_s.

Verification: the first differences of f_r on this half are one until j=r+1 and zero thereafter, so d_j=sum_(r>=j-1)c_r; subtraction gives the inverse. Symmetry supplies the second half.

Thus any even palindromic difference profile 2v can be realized using c_r>0 copies of S_2 x CP^r and -2c_r copies of S_3 x CP^r for c_r<0. All multiplicities are nonnegative integers. The simultaneous projection operation puts these finitely many centers into the same CP^N. This proves actual existence, rather than treating delta as an arbitrary formal list. It also shows why this is not a free improvement: signed oscillations require positive geometric multiplicities, each of which contributes its full free Betti and torsion costs. One cannot minimize the fixed count using delta alone while independently fixing b,A,Q. In particular a profile inequality does not establish an optimized geometric example until these costs and the compatible ambient dimension have been included.

The inverse basis is elementary and the geometric realization is supplied. It is useful for executing alternatives, but not a new substantial operation on its own.

## 7. Iteration and quantitative limitations of the actual maps

For the invariant construction Phi=psi^epsilon g with g^2=id, commutation gives Phi^k=psi^(k epsilon)g^k. For an odd fixed k with 2k epsilon below the global short-period threshold, exactly the same fixed-point proof works, with the same count and the appropriate derivative avoidance. A single sufficiently small epsilon works for any prescribed finite set of odd k. This is a finite-window consequence of the source proof, not a theorem about all odd iterates.

For even k, Phi^k=psi^(k epsilon). If f was chosen supported in a proper neighborhood of Fix(g), the complement contains an open set on which psi is the identity. Every even iterate then has nonisolated fixed points there. Even when f has a global Morse extension, the even iterates detect Crit(f), including points off Fix(g). A small time-one perturbation preserving the selected fixed points does not establish any all-iterate nondegeneracy or a count for all simple periodic orbits. One must distinguish a fixed point of Phi^k, a simple k-periodic orbit, and the set of its k images.

No infinite sequence of inequalities 2k epsilon<tau can hold for a fixed positive epsilon. Uniform control of all odd iterates would require new control of long periodic orbits, not just the compact short-period estimate. Likewise, scaling a symplectic form or shrinking epsilon already supplies certain small numerical bounds after changing the scale; this does not constitute a new fixed-scale Hofer/action/spectral estimate. No such quantitative claim is made here.

## 8. Scope of the other two source mechanisms

The nondegenerate ordinary-Morse example uses G=A_5^k, a two-generated augmentation ideal but unbounded minimum number of group generators, a symplectic four-manifold X with pi_1=G, a fixed eight-variable relative model, and an exact capped Hamiltonian construction on X x (S^2)^4. The relative handle counts (1,b,chi(X)-2+2b,b,1), b=2, give 16(chi(X)+8) fixed points. The ordinary Morse obstruction uses d(G), not integral homology alone. Its endpoints' equal rotations do not imply equal Hamiltonian paths: full-turn differences and an explicit contraction inside caps are essential. This source is fully paid. Its fundamental group is not removed by multiplying with Y, and its ordinary-Morse deficit cannot be silently turned into a stable-Morse deficit. Damian-type sufficiently large stabilization does not automatically supply the specified eight-variable model; that stronger model is read in and supplied by the canonical paper itself.

The degenerate quadric example has a clean finite-order fixed locus Q_2, a function on Q_2 with precisely three critical points, and a transfer that remains valid at degenerate critical points. The source computes critical number and unit-inclusive rational cup length four for Q_3. Its one degenerate critical point has rank-two Hessian, so ordinary persistence of nondegenerate points is inapplicable. Perturbing that point may split it and does not preserve a three-point nondegenerate count. The critical-number conclusion does not impose the value of SM on the dimension-sixteen examples above.

Neither mechanism furnishes a missing nonroutine operation for section 4 merely by being included in a longer proof.


## 9. A stronger obstruction with a sharp realization, still prefreeze

The narrow enumeration in section 5 can be strengthened without restricting the centers to products of the two source surfaces. Here is the actual algebraic obstruction, including arbitrary prime powers.

Let X be a simply connected closed oriented manifold of real dimension eight or ten, and assume Tor H_2(X;Z)=0. Integral Poincare duality and universal coefficients give

    Tor H_i(X;Z) is isomorphic (noncanonically) to Tor H_(dim X-i-1)(X;Z).

Since H_0 and H_1 are torsion-free, and H_2 is torsion-free by hypothesis, all torsion is confined to degrees 3 through dim X-4. Thus in dimension ten each parity has at most two consecutive positions in the degree-two indexing; in dimension eight each has at most one. This is a topological restriction on X, independent of a chosen blowup presentation.

For each prime p, parity epsilon, and position j, put v_(p,epsilon,j)=d(Tor H_(epsilon+2j)(X;Z)_(p)). Prime powers are allowed; this number is the dimension of the primary group's quotient by p, not its order or exponent. Only finitely many primes occur. Integral Kunneth with a torsion-free even factor gives

    lambda(X x CP^1)=2b(X)+2 sum_(epsilon,j) max_p (c*v_(p,epsilon))_j,
    lambda(X x Y)=8b(X)+2 sum_(epsilon,j) max_p (e*v_(p,epsilon))_j,
    beta(X x Y)=8b(X)+16 sum_epsilon max_p sum_j v_(p,epsilon,j).

The last equality uses minimal Chern number one and the Z/2 cyclic integral convention; it follows from summing each prime's torsion multiplicities over a parity before taking the maximum. The cyclic Smith-form lower bound and its algebraic realization are paid source inputs.

Suppose the four fixed components of the Y involution are perturbed using arbitrary Morse functions on X x CP^1, and the resulting nondegenerate map has exactly beta fixed points. Each component's Morse function has at least lambda(X x CP^1) critical points. Hence

    beta >= 4lambda(X x CP^1) >= beta.

All inequalities are equalities. For each parity, equality in

    sum_j max_p(c*v_p)_j >= max_p sum_j(c*v_p)_j

forces a prime p_epsilon attaining the right side to dominate every coefficient of every other c*v_p: the nonnegative differences have sum zero. The c-convolution of a list of length at most two is (v_0,v_0+v_1,v_1), so the two endpoint coefficients show that this same prime dominates the original v_p coefficientwise. It therefore dominates e*v_p as well. Substitution into the displayed formula gives

    lambda(X x Y)=beta(X x Y).

The supplied simply connected handle realization applies to X x Y (dimension at least twelve); therefore SM(X x Y)=Morse(X x Y)=beta. A cyclic-sharp stable-Morse deficit is impossible for this precise involution/Morse-extension mechanism under Tor H_2(X)=0 and dim_R X<=10 in the stated dimension range. No attainment of lambda(X x CP^1) was needed for the obstruction; the chain lower bound alone sufficed there.

The blowup class in section 5 has H_2 torsion-free much more generally: blowing up a torsion-free ambient space along any smooth complex centers of codimension at least two adds to H_2 only copies of H_0 of those centers. Thus allowing arbitrary projective threefold centers in a complex fivefold would not evade this cyclic-sharpness obstruction, even if a compatible embedding were supplied. This is stronger than merely naming an embedding gap.

Section 4 supplies real dimension sixteen examples with H_2(X) torsion-free and unbounded deficit, attaining beta, so the obstruction has a sharp dimension endpoint within the specified Y mechanism and this topology hypothesis. It does not exclude non-cyclic-sharp deficits in lower dimensions, manifolds X with torsion in H_2, or entirely different Hamiltonian realizations. The obstruction is an equality case of a finite max-convolution inequality combined with paid duality and source realization. It is retained as an integrated deduction, but no nonroutine operation beyond that reduction has been established for nomination.

## 10. Executed alternative: higher-dimensional free affine quotients

A prospective way to change center torsion is to replace a source bielliptic surface by the projective threefold

    T_p=(E x E_p x E_p)/< (z,w_1,w_2) -> (z+1/p,zeta_p w_1,zeta_p w_2) >,
    p=2 or 3.

The action is free because of the nontrivial translation on E. The finite quotient is smooth projective: an ample line bundle on the product can be tensored over the finite group, and a positive power gives a descended ample bundle. Choose a real lattice coordinate of E in the translation direction. Topologically T_p is the product with S^1 of the mapping torus of the automorphism A_p on T^4. Here A_2=-I_4, and A_3=diag(B,B), B=[[0,-1],[1,-1]].

The integral mapping-torus Wang exact sequence gives

    0 -> coker(wedge^k A_p-I) -> H_k(mapping torus;Z)
      -> ker(wedge^(k-1) A_p-I) -> 0.

The kernel is free, so this sequence splits as abelian groups. Thus it gives the actual torsion, not merely rational ranks. Taking the product with S^1 adds the adjacent homology group, with no Tor term.

For p=2, wedge^k A_2-I is zero for even k and -2I for odd k. For p=3, B-I has Smith factors (1,3); wedge^3 A_3 is integrally conjugate to the dual of A_3 because det A_3=1, so it has the same Smith factors as degree one, namely (1,1,3,3). In degree two, the two volume classes are fixed and the cross-term block B tensor B-I has rank two and a unimodular 2x2 minor, giving Smith factors (1,1,0,0) on that block. These are exact integer calculations. The retained tiny script computes all determinantal divisors from integer minors as a check; it is not a substitute for the Wang-sequence proof and introduces no external package dependency.

Consequently the complete free ranks of T_2 are (1,2,7,12,7,2,1), and its torsion is (Z/2)^4 in each of H_1,H_2,H_3,H_4 and zero otherwise. Those of T_3 are (1,2,5,8,5,2,1), with (Z/3)^2 in each of those four degrees and no other torsion. Their torsion profiles are still proportional, now (4,4) and (2,2) in each parity. This alternative does not create the required sign-changing degree profile. In a complex fivefold blowup it also remains subject to section 9, irrespective of embedding details.

An auxiliary elliptic factor on a source surface gives a different, unpaired list: S_2 x E has 2-primary ranks (2,6,6,2) in H_1 through H_4, while S_3 x E has 3-primary ranks (1,3,3,1). However, after any codimension-two insertion into a torsion-free complex fivefold, each parity still has only two positions. Section 9 again rules out cyclic-sharp positive deficit for the Y mechanism. Therefore neither a more flexible threefold center nor its assumed embedding closes the lower-dimensional cyclic-sharp extension. The missing topology would have to evade Tor H_2(X)=0, or the Hamiltonian operation itself would have to change.

No construction of a simply connected Kähler X with the necessary H_2 torsion and a compatible fixed-point realization is supplied here. No claim is made that such X cannot exist. No global dimension threshold is inferred.
