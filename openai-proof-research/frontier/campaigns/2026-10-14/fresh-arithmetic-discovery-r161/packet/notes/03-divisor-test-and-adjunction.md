# An actual defect-two test and the adjunction attempt

## 1. A smooth Fano test at every i>=3

Let X_i be the blow-up of P^(2i) along a linear P^(i-2). Its exceptional divisor is

    E=P^(i-2) x P^(i+1).

Let H be the pullback of the hyperplane class of P^(2i), and L=H-E the pullback of the hyperplane class under projection from the center to P^(i+1). Resolving that linear projection realizes X_i as the incidence subvariety in P^(2i) x P^(i+1); the second projection is a P^(i-1)-bundle. Both H and L are nef and integral, and H+L is ample, since it is the restriction of O(1,1) under the closed incidence embedding.

The center has codimension i+2, so the blow-up canonical formula gives

    -K_X=(2i+1)H-(i+1)E=iH+(i+1)L.                         (1.1)

Thus X_i is Fano. For every nonconstant irreducible rational curve C, the integers H.C,L.C are nonnegative and not both zero; (1.1) gives -K.C>=i. A line h in a fiber of the second projection has (H.h,L.h)=(1,0), and a line e in an exceptional fiber of the blow-down has (H.e,L.e)=(0,1). Their anticanonical degrees are i and i+1, respectively, so the actual pseudoindex is i, the actual Picard rank is two, and

    dim X_i - rho(X_i)(iota(X_i)-1)=2.

On E the restrictions are H=O(1,0), L=O(0,1), E=O(1,-1). Since i>=3, both factors have lines. They give two independent numerical classes, so N1(E,X_i)=N1(X_i). In particular, an effective divisor containing a full numerical spanning set is perfectly compatible with the actual target hypotheses.

## 2. The divisor-square cycle really acts nontrivially

The algebraic cycle E x E has dimension 4i-2=2 dim X_i-2 and its action is

    alpha -> (integral_X alpha*E) E

on H_(n-1), with zero action on the point and on every other codimension. For the dual curve classes h and e, it sends h to E and e to -E. In divisor basis (H,L), the resulting middle-block matrix is

              [ 1 -1 ]
         B =  [ -1 1 ].                                    (2.1)

It has rank one and is nonzero. This is an ACTUAL Chow correspondence on a smooth Fano in the proposed defect-two range, not an arbitrary abstract matrix. However it is NOT asserted to be the source's selected quantum word, nor is E a saturated class for all the low-degree families. Its role is precise: the dimension, full numerical span, and vanishing on point classes alone do not annihilate a divisor-square correspondence. Any proof eliminating (3.2) in note02 must use additional quantum or saturated-chain geometry.

Matrix multiplication of (2.1) with itself is not the composition of the graded cohomology operator: the displayed matrix maps H_(n-1) to H_1, which are different graded pieces. The actual composition of this correspondence with itself is zero for n>=6 by grading. No spurious matrix-eigenvalue interpretation is used.

## 3. Why this example is not a counterexample

It has an explicit low-degree three-curve chain through EVERY pair x,y. Write p:X_i->P^(i+1). Choose any a in the center P^(i-2). Each p-fiber is P^(i-1) and meets E in its hyperplane P^(i-2). A line in p^{-1}(p(x)) joins x to (a,p(x)); a line in {a} x P^(i+1) joins (a,p(x)) to (a,p(y)); a line in p^{-1}(p(y)) joins (a,p(y)) to y. Omit any constant segment. Their degrees are i,i+1,i, all <=i+2.

The full family containing a horizontal center line of E is allowed to leave E: that line has the same numerical class h as lines in the covering P^(i-1)-fiber family. Discarding that ambient full component and retaining only the divisor-contained subfamily would manufacture a false obstruction. This is exactly why note02 uses all full components of all degrees <=M. The example is a stress test of an incomplete inference, not a refutation of the exploratory theorem.

## 4. A concrete adjunction route and its missing hypotheses

There is a useful sufficient route for eliminating a PARTICULAR all-minimal divisor configuration. Suppose a single smooth prime divisor D contains an actual chain of r independent degree-i curves, and the full ambient families containing those curves ALL have locus D. Then those same families are full proper components on D: a larger component on D would map into the ambient RatCurves component and contradict its maximality; properness is inherited (with the usual finite normalizations).

A general member f of each such family is free on the smooth D because the family dominates D. If D.gamma>=0, the normal sequence

    0 -> f*T_D -> f*T_X -> O_(P1)(D.gamma) -> 0

has globally generated ends and H1(f*T_D)=0. Global sections lift the normal directions, and H1(f*T_X)=0. Thus the ambient deformations move off D; equivalently f*T_X is globally generated, so its full ambient family dominates X. This contradicts its assumed locus D. Therefore D.gamma<=-1 for each family.

Adjunction gives

    -K_D.gamma = -K_X.gamma - D.gamma >= i+1.

The CORRECTED BCDD ordered-chain theorem can now be applied on the smooth projective (n-1)-fold D. Independence survives there, since a dependence would push forward to one on X. It gives

    n-1 >= sum_j(-K_D.gamma_j-1) >= r*i.

But n-1=r(i-1)+1, so this forces r<=1. Thus such a smooth common-divisor configuration is impossible for r>=2.

This calculation uses actual adjunction and full-family geometry; it is stronger than simply naming an exceptional-divisor gap. It does NOT eliminate the actual residual tensor. A product D_a x D_b in a chain support need not put every intermediate full family on one smooth prime divisor, nor force every family to dominate that divisor. Boundary divisors can be singular and chains can pass among components. Resolving a divisor changes the canonical degrees by discrepancy and exceptional terms; pseudoindex of the ambient smooth Fano does not control them. Proper full ambient families need not become full proper components of the desired degrees on a resolution. No adjunction inequality is silently extended to this setting.

There is also no valid shortcut from a family degree i to an extremal-ray length i. Source numerical independence does not identify the Mori cone. Occhetta's positive-coefficient argument needs covering families, all ordered permutations and exact full-dimensional chain loci. Fujita's ray argument needs its separate count and defect-one budget. Replacing those inputs by the divisor matrix (2.1), or by a merely nonempty chain, fails at their explicit hypotheses.

The remaining operation must control the actual divisor-supported quantum word and saturated low-degree classes, including singular divisors and intermediate loci, or produce a different low-degree connecting construction at the same full scope. Neither the actual blow-up test nor the smooth-divisor calculation supplies that operation.
