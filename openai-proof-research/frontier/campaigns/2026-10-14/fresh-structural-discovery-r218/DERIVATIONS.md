# r218 prefreeze mathematical notebook

No target is frozen. These are feasibility calculations and auxiliary derivations, not an author-proof nominee or an assigned contribution grade.

## Operative source, read before extended deductions

October Source342 uses a closed connected smooth four-manifold X, smooth fixed J, its complex orientation and real cohomology. A closed form taming J need not be J-invariant. The main result permits changing the class. Put V=(H_J^-)^perp, C=K_J^t intersect V. October gives K_J^t=C+H_J^- and K_J^c={a in C: a.y>0 for every nonzero y in closure_V(C)}. The zero vector must be excluded from the positivity test. In signature (1,b-) on V, i.e. h_J^-=b+-1, it gives C=K_J^c. All these operations are paid.

The source's closed lift is B=dd*G+H with R B=Id and dB=0, where R is the anti-invariant projection, L=Rdd* on anti-invariant forms, H its harmonic kernel projection, and G its generalized inverse. For exact input alpha, H R alpha=0, so (1-BR)alpha is exact invariant. This distinction is crucial to class control.

The current proof, all read: positive separation with mass one; corrected radial tests log(s^2+t^2)/2 plus A sqrt(s^2+t^2); quadratic mass; S_r=(1+r^2 Delta)^-3; nonnegative kernel leading term of size r^-4 and error r^-2; angular moment O(r^4); relative projection estimate ||Pi S_r W||_2<=Cr||S_r W||_2; Q in L2; density at every point; constant-polarization planar tangents; transverse moment o(r^2); r^-3 sqrt(I_r)sqrt(N_r)=o(1); successive cutoff limits; positive-density restriction closed. Source cone section already extends estimates to arbitrary-class separators, proves mixed-current zero-density pairing by a bounded-overlap covering and Cauchy--Schwarz, places the residual class in closure(C), and completes prescribed-class separation. None is an unpaid bridge.

Source's flat four-torus example is also paid: U=e12+e34, V=e13-e24, W=e14+e23, f=sin(2pi x1)/4, k=sin(2pi x2)/4, F=(U+fV+kW)/sqrt(1+f^2+k^2), eta=U+2f e13+2k e23, class [U], h^-=0, and the tamed classes U+V and U-V pair to zero. Do not nominate this example or its rescalings.

## First changing-J reduction: unrestricted class

Potential mechanism, to compare with actual primary proofs before any freeze. Fix J0 and a compatible eta0. Let E0=Lambda^-_{J0}, choose source B0, and for J near J0 let U_J=R_J|E0:E0->E_J. U_J is a pointwise isomorphism near J0. A_J=U_J^-1 R_J B0 is an order-zero operator on E0, equal to Id at J0. In a fixed C^{k,alpha} (or H^s with s>2) norm, it is invertible for J sufficiently close. Set

    eta_J = eta0 - B0 A_J^-1 U_J^-1 R_J eta0.

Then d eta_J=0, R_J eta_J=0, eta_J->eta0; positivity follows by C0 openness. Elliptic regularity of A_J and smooth Banach inverse dependence should give smooth joint parameter dependence for smooth finite-dimensional J families. This uses the fixed full closed lift B0; it does NOT require constant dim ker(L_J). The H0 component allows the class to move. Local sections can then be patched with functions of the parameter only: at each parameter all summands are closed and invariant for that SAME J. A relative collar can be fixed by including the given section with weight one there. Thus free-class relative existence looks like a standard local solvability/convex-selection consequence, not a substantial target.

## Fixed-class wall: a concrete stronger alternative to naive projection

For flat T4 and J_t defined by F_t=(U+t f V+t k W)/r_t, every invariant form has selfdual part q_t(U+t f V+t k W). If a closed form has class [U], the mean of its selfdual part is U. Thus for t!=0,

    mean(q_t)=1, mean(q_t f)=0, mean(q_t k)=0.

At t=0 only mean(q_0)=1 is imposed by cohomology/invariance. Therefore a continuous family in class [U] through a chosen J0-compatible eta0 must have mean(q_0 f)=mean(q_0 k)=0. This supplies a concrete candidate obstruction to arbitrary prescribed relative values despite pointwise existence. Source's eta_t gives one smooth compatible family in [U] for all t, so failure would concern extension of an assigned value, not existence of some family.

Strongest local reconstruction to execute: for a selfdual sigma with harmonic part U, eta=U+2 dd* G_Delta(sigma-U) is the unique closed representative of [U] with selfdual part sigma. Indeed for mean-zero selfdual zeta, (dd*G zeta)^+=zeta/2. The difference of two such closed forms is exact anti-selfdual, hence harmonic and zero. For q satisfying all three means, use sigma_t=q(U+t fV+t kW); this gives a smooth exact-class extension, positive for small t if eta0 is positive. Hence the moment conditions may be sufficient as well as necessary. This is being compared to the classical Hodge/deformation operations; it is not frozen as a substantial theorem.


## Prefreeze explicit degeneration construction (after primary comparison)

The earlier concentration/Hodge sketch simplifies completely. Use fixed nonnegative p on S1, supported in a small arc, with mean 1. Choose 0<=f(x1,x3)<=1 smooth, nonzero, whose support avoids supp(p(x1)) union supp(p(x3)); put c=mean(f)>0. For 0<s<1 set A_s(x)=s+(1-s)p(x), q_s=(A_s(x1)+A_s(x3))/2. Then mean(q_s)=1 and q_s f=s f exactly. Define

    a_s=s(f-s c), r_s=sqrt(1+a_s^2), F_s=(U+a_s V)/r_s,
    eta_s=A_s(x1)e12+A_s(x3)e34+2s^2(f-c q_s)e13.

All coefficients depend on only the coordinates appearing in their wedge factors, so d eta_s=0. The off-diagonal coefficient has mean zero. Hence [eta_s]=[U]. Its selfdual part is q_s(U+a_s V): the key equality is q_s f=s f. Its square is 2 A_s(x1) A_s(x3) dV>0 because e13 wedges to zero with both diagonal terms. The selfdual coefficient is positive, so eta_s is positive for the orthogonal J_s with fundamental form F_s. No Green-operator norm or small-error absorption remains necessary.

For ANY compatible alpha in [U], write alpha^+=q(U+a_s V). Then q>0, mean(q)=1, and the harmonic V coefficient vanishes. Thus mean(q f)=s c. If s->0, no distributional limit of such forms can be J0-compatible: at such a limit q0>0 and mean(q0 f)>0. The moment identity survives distributional convergence since f is fixed smooth. Choosing s(t)=exp(-1/t^2)/4, s(0)=0, makes J_t-J0 flat to every order at t=0. Nevertheless the endpoint fibre contains U.

This differs from the simpler earlier finite-moment obstruction through a specified eta0: it blocks extension to EVERY compatible endpoint value. It also removes the initially contemplated shrinking support and elliptic correction; those were prefreeze alternatives, not frozen scope.

The strongest free-class alternative is explicit: zeta_s=U+2a_s e13 is closed, has selfdual part U+a_s V, square 2 dV, and is J_s-compatible, including at s=0. Its class is [U]+2s c(1-s)[e13], so the successful extension necessarily changes the class in this construction. This agrees with Donaldson's positive-plane cohomological freedom and DLZ's local openness, rather than contradicting them.

Actual primary comparison already read: DLZ 2008 Lemma 2.4 gives the Hodge reconstruction (paid); DLZ 2011 3.3 and 3.4.3 give metric-related deformations and rank computation (paid); DLZ 2011 Section 5 and Donaldson 2006 Section 2 give local solvability allowing positive-plane period changes (paid). Donaldson 5.5 produces a different nonextension through unimodular nonlinear constraints on b+=1, using a nontrivial loop and Seidel; it does not supply this fixed-tamer, nonempty-endpoint, flat-in-parameter compatible-class construction. Li--Ning 2.2 uses taming convexity/Moser or integrable Kodaira--Spencer, and the pinned hypersymplectic companion's compatible-family lemma uses a constant rank-two kernel and allows the class to vary. No theorem is nominated merely from these standard mechanisms.
