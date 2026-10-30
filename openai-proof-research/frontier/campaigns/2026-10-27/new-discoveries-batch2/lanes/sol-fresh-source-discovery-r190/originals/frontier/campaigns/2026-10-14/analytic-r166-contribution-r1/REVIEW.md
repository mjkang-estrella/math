# T366A166 — first independent substantial-contribution review

## Verdict and scope

**TECHNICAL, conditional on correctness of the entire unchanged frozen statement.** The strongest compatible reduction pays the construction: the actual primary proofs supply the corrected conjugate with bounded-fidelity errors, coarse decay, parity cancellation, the complete homogeneous spectral system including its generalized zero mode, and the elliptic trace improvement. The additional state-space completion, forced high-mode estimate, finite decay bootstrap and extraction of the first coefficient follow by explicit elementary Hilbert-space, scalar Green-kernel and local elliptic estimates. Sections 2–8 below integrate those operations through all three frozen limits. No fully closed nonroutine operation remains after this reduction.

This is a contribution judgment, not correctness PASS, an acceptance, a count, a repair or an assertion that the precise theorem already appears verbatim in print. It covers every bounded Lipschitz domain, every bounded measurable datum, every specified reduced absolute minimizer, and every loose end in STATEMENT.md, including zero leading coefficient. It retains the uniform function and first-derivative limits, the essential-uniform second-derivative limit, W^{2,infinity} and the one-sided second derivative zero at the endpoint. There is no symmetry, uniform scale, finite global component count, continuous fidelity, or nonzero-coefficient restriction.

The immutable statement is SHA256 c518b1e730585463899f83a6c1aa1023717817671ecdcd540245024745a1cd33; the unchanged proof is 5a5877d58132597566ba6fed1cd376501810dc4294270c84f14b3d65325a8828. The upstream pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and operative upstream proofs are stipulated true. This review tests compatibility and contribution, rather than revisiting that stipulation. No correctness sibling, parent assessment, response or other independent verdict was an input.

## 1. Actual predecessors and the strongest comparison

SOURCE366's entire main, six operative sections, bibliography and figure include were read from the nine canonical objects authenticated against the complete pinned tree. Its initial reduction supplies local boundedness in the original compact-comparison class; its geometric theorem supplies the tangent and charts. Classification, translation interactions, model-chart assembly and weak L4 are already paid. None is nominated here.

The operative endpoint source is De Lellis–Focardi, arXiv2308.14660v2, 5 January 2025, complete Chapter 5 (physical PDF pages 125–160), together with setup 1.1, Proposition 2.5.2 and Appendix A. In particular:

* Lemmas 5.0.3–5.0.4 supply the corrected harmonic conjugate and its equal boundary traces, the rough fidelity errors and the endpoint normalization.
* Lemma 5.1.3, equations (5.1.16)–(5.1.23), supplies the exact cylindrical system, trace regularity and decay of the fidelity errors.
* The actual proof of the first linearization in §5.2 uses the sequence normal trace in H^{1/2}, finite Lp bounds for the angle equation, boundary W^{2,p}, and C1 control. It handles the nonzero common boundary trace without differentiating a bounded fidelity datum.
* Lemmas 5.3.5–5.3.7 and Proposition 5.3.8 supply the homogeneous spectral decomposition, generalized zero sector and roots. The proof, not merely the spectral statement, was read.
* The unnormalized estimate immediately before (5.5.5), (5.5.6), and Corollary 5.5.2, especially (5.5.10), supply coarse odd/angle decay and full even C1 decay for bounded fidelity. The sharper homogeneous consequence is not assumed for nonzero fidelity.
* Proposition 2.5.2 and the full Appendix A provide the bounded variational representative g_K and local C1,1 regular-arc interface with measurable g. No restriction of an arbitrary L-infinity representative to K is needed.

The complete De Lellis–Focardi–Ghinassi arXiv2010.04888v4 proof was also read (all 27 PDF pages). Its equations (5.7), (5.9), the trace improvement on physical page 13, §§6–8 spectral/three-annuli/nonlinear construction, and corrected moment constraint make clear how much of the proposed mechanism is old. That paper is homogeneous; its endpoint conclusion cannot simply be imported into the bounded-fidelity problem. Its separately linked erratum was obtained as complete web-extracted text after this reviewer's direct download returned 403. The correction replaces the moment condition by the integral of v_phi against sin(phi/2), and the corresponding slow-mode calculation; the later monograph already uses that corrected condition. I do not certify raw erratum PDF bytes or a visual inspection. This correction is a version/interface observation, not an independent challenge to the stipulated upstream truth. [Erratum](https://www.math.ias.edu/delellis/sites/math.ias.edu.delellis/files/Errata-crackip.pdf).

Andersson–Mikayelyan arXiv1512.05094v5 was read in its introductory material, full §§7–8 and Appendix A. Its refined projections, quadratic remainder estimate (8.51), slow-mode estimate (8.60)–(8.61), symmetry cancellation (8.72), and rates (8.76)–(8.81) already combine the homogeneous spectral obstruction with nonlinear improvement. Appendix A proves an L2 spectral representation, including the exceptional logarithmic/generalized mode and endpoint data, by a near-Fourier argument. This reinforces, rather than replaces, the later monograph's operative spectrum. I did not read all its earlier §§2–6 proofs; the full later monograph proof supplies the dependencies used here. Neither AM's homogeneous assertion nor a claim of manifold C2 regularity beyond its actual statement is substituted for the frozen theorem.

Deangelis arXiv2609.26732v2 and Labourie–Lemenant, doi10.5802/crmath.826, were read completely. Their strongest operations respectively pay the Hodge/two-translation classification route and escape paths, finite complementary-component structure and finite-center trace chaining. They do not provide a separate sharp forced odd-curvature theorem. LL's convenient global-minimizer boundedness convention is not silently imposed on the frozen compact-comparison class; SOURCE366's local boundedness is sufficient instead.

The actual original I122 sections [1481,4543) and [16591,22447) were read. Their polynomial graph-complexity target, with normalized data and energy and a bound on the number of endpoints/triods, remains distinct and unchanged. This review neither retries that target nor uses an alleged history absence as contribution evidence. There was no new catalogue or family search.

## 2. Full-class applicability and the coarse estimates

Fix an arbitrary loose end p of an arbitrary minimizer in the frozen class. SOURCE366 supplies the local arc, tangent and local boundedness. A smaller disk compactly contained in Omega suffices. Subtract u(p) from u and g, choose the sign of u if needed, and rotate to the tangent. If the normalized primary setting on B2 is used, choose one fixed sufficiently small rho and set

    u_rho(x) = rho^{-1/2}(u(p+rho x)-u(p)),
    g_rho(x) = rho^{-1/2}(g(p+rho x)-u(p)), lambda = rho^2 <= 1.

Local boundedness makes the datum bound finite; setup (1.1.2) permits any fixed finite M0. This is a per-chart normalization, not a uniform bound over minimizers. Scaling back changes constants and the real leading coefficient. It does not alter any frozen quantifier or demand a global maximum principle unavailable for the specified comparison class.

Write r=e^{-t}, the curve r(cos theta(t),sin theta(t)), a=theta', S(phi)=sqrt(2/pi)sin(phi/2), c=1/sqrt(2pi). The corrected potential gives f=e^{t/2}w(r,phi+theta(t)). On fixed-width, padded strips, the actual primary equations are

    Lf = (a'-a)f_phi + 2a f_tphi - a^2 f_phiphi,
    L = partial_tt - partial_t + partial_phiphi + 1/4,
    f(0,t)=f(2pi,t)=H1(t),
    (a'-a-a^3)/(1+a^2)^{5/2}
       = f_phi(2pi,t)^2-f_phi(0,t)^2+H2(t).

Here H2 is a bounded measurable scalar error, with |H2(t)| <= C_s e^{-st} for every s<3/2. H1 has the corresponding first-derivative decay and the specified H^{3/2} trace control, as well as uniformly C^{1,alpha} regularity for every alpha<1. The variational g_K accounts for the curvature identity. There is no differentiation of H2 in this review's derivation.

The odd H2 and a H1 estimates in the unnormalized nonlinear three-annuli inequality decay exponentially. Integrating a to the known tangent limit supplies theta H2 decay. Full even C1 decay comes from (5.5.10). It is important that the projected even estimate (5.5.6) alone would not bound an undetermined even amplitude: use the actual full C1 conclusion as well. An ordinary fixed-strip elliptic estimate applied to f-S, with its C1 decay, the decaying a,a' terms and the decaying H^{3/2} boundary trace, then supplies full H2 decay. This closes that compatibility issue without assuming sharp decay.

The angle equation and bounded f_phi first bound a'. The full principal matrix in (t,phi) is

    [ 1   -a ]
    [-a  1+a^2],

with determinant one. For bounded small a and bounded a' it is uniformly elliptic and Lipschitz. The boundary datum C^{1,alpha}, alpha>1-1/p, lies in the needed W^{2-1/p,p} trace space. Fixed-strip estimates give uniform W^{2,q} bounds for every finite q. Interpolating the established H2 decay with a uniform W^{2,q} bound, q>p, gives some positive decay exponent epsilon_p in W^{2,p}. This is precisely the type of rough-data elliptic operation already performed in DF §5.2, not a new regularity hypothesis. Constants and rates may depend on the fixed minimizer and strip width.

## 3. Parity supplies a decaying coefficient, not a new source term

Put E=(f(phi,t)+f(2pi-phi,t))/2=S+e and O=f-E. O vanishes at 0, pi and 2pi. Reflection reverses a phi derivative. Thus the exact odd equation and endpoint equation are

    LO=(a'-a)S_phi+R,
    R=(a'-a)e_phi+2a e_tphi-a^2 O_phiphi,
    a'-a=-4c O_phi(0,t)+N,
    N=a^3-4[(1+a^2)^{5/2}E_phi(0,t)-c]O_phi(0,t)
          +(1+a^2)^{5/2}H2(t).

Indeed E_phi(2pi)=-E_phi(0) and O_phi(2pi)=O_phi(0); the difference of boundary squares is -4E_phi(0)O_phi(0). This fixes the sign and factor -4c. H1 cancels from the odd boundary condition. In particular there is no additive even-only error in R or the nonlinear part of N. Symmetry cancellation of this sort is already operative in DFG (5.7), (5.9) and AM §8.

Let X(t) be the padded-strip H2 norm of O plus the interval H2 norm of theta. With epsilon>0 below the coarse exponents, the trace theorem and one-dimensional H1 embedding give

    ||(R,N)||_{L2(strip_t)}
       <= C e^{-epsilon t} X(t) + C_s e^{-st},  s<3/2.       (3.1)

For example e_phi is a decaying supremum coefficient; e_tphi is decaying in L2 and a is controlled in supremum by X. O_phi(0,.) has its L2 trace bound from H2. Two coarse factors can be removed from a^3, and a^2 is a decaying coefficient of O_phiphi. Fixed padding avoids a loss at strip edges. Only the elementary product/trace estimates are required beyond the already-paid parity split.

## 4. Independent boundary state: completion, signs and domain

The need not to take the trace of an L2 bulk error is real. It is resolved by retaining the endpoint value as a coordinate; it does not require solving a new spectral problem. Set I=(0,pi) and

    H=L2(I) direct-sum R,
    ||(z,b)||_H^2 = integral z^2 + (pi/2)b^2,
    [(z,b),(h,d)] = integral zh - (pi/2)bd,
    D(A)={(z,z(0)): z in H2(I), z(pi)=0},
    A(z,z(0))=(z''+z/4, -(2/pi)z'(0)).                    (4.1)

The graph norm is equivalent to ||z||_{H2}: one direction is the interval trace estimate; in the other direction z''=(Az)_bulk-z/4 and interval interpolation control z'. Limits in the graph norm therefore preserve the traces and show closedness. Integration by parts gives [Az,h]=[z,Ah], because the boundary coordinate cancels the term at zero.

Define zeta=O-c theta cos(phi/2), Z=(zeta,-c theta). Its second coordinate equals zeta(0), and zeta(pi)=0. The bulk equation is Lzeta=R. At zero,

    zeta_tt(0)-zeta_t(0)=(2/pi)zeta_phi(0)-cN,
    Z''-Z'+AZ=(R,-cN).                                 (4.2)

Here 4c^2=2/pi; the sign in A is negative. Equation (4.2) never evaluates R at the boundary.

The known generalized zero modes, in this normalization, are

    e1=(cos(phi/2),1), e0=((phi-pi)sin(phi/2),0),
    Ae1=0, Ae0=e1, [e1,e1]=0, [e1,e0]=-pi/2.

Their Gram matrix is nonsingular. The entire operator is not asserted to be positive self-adjoint; that would lose this sector. For k>=2 the actual primary roots and modes give

    q_k=(sin(nu_k(phi-pi)),-sin(pi nu_k)),
    Aq_k=-lambda_k q_k,
    lambda_k=nu_k^2-1/4=mu_k(mu_k+1), mu_k=nu_k-1/2.

The first root nu_2 is in (3/2,2), the others lie in (k-1,k), and the primary proof supplies H1 completeness with the two exceptional modes. The energy identity

    lambda_k[q_k,q_k]=integral |q_k'|^2-(1/4)integral |q_k|^2>0

uses the interval Poincare inequality with Dirichlet value at pi; equality is only the cosine mode, not q_k. Distinct eigenmodes are bracket-orthogonal and orthogonal to the generalized zero sector by symmetry of A.

The root equation gives |sin(pi nu_k)|<=C/k, while the bulk squared L2 norm is pi/2+O(1/k). Consequently bracket-normalized h_k have |(h_k)_b|<=C/k. For every finite sum W=sum d_k h_k,

    sum |d_k|^2 <= ||W||_H^2
      = sum |d_k|^2 + pi |sum d_k(h_k)_b|^2
      <= C sum |d_k|^2.                                (4.3)

The last step is Cauchy–Schwarz and the summability of k^{-2}. Thus the high-mode synthesis has closed range Y and is a Riesz basis there. The Gram matrix gives a bounded projection onto the two-dimensional low sector. The direct sum of that sector with Y is closed and, by primary H1 completeness, contains all H1 trace states. Those states are dense in H: approximate a prescribed L2 bulk function away from the endpoints, then add a narrow boundary layer prescribing the independent scalar at zero with vanishing L2 cost. Hence H=span{e0,e1} direct-sum Y.

Finally D(A) is exactly the sequence domain sum lambda_k^2|d_k|^2<infinity, plus the finite sector. For sufficiency finite sums converge in the graph norm and closedness applies. For necessity bracket symmetry identifies the coefficients of AZ as -lambda_k d_k; (4.3) then gives square summability. This is an explicit domain argument, not just a formal expansion.

These steps fully address the difference between a primary H1 spectral statement and L2 bulk forcing with an independent boundary coordinate. They use the already-proved eigenfunctions/completeness, one trace-density approximation, a summable scalar sequence and closedness. Their length and the useful formulation do not make them a nonroutine new spectral operation.

## 5. Uniform forced Green estimates and the Jordan sector

Use the norm

    X_Z(t)=||Z||_{H2((t,t+1);H)}+||Z||_{L2((t,t+1);D(A))}.

On padded strips this is equivalent to the O H2 plus theta H2 norm needed in (3.1). The scalar boundary coordinate supplies theta and its two time derivatives; the graph domain supplies two phi derivatives. Mixed derivatives follow by the ordinary product Sobolev estimate, or extension and |xi_t xi_phi|^2 <= (xi_t^4+xi_phi^4)/2. Conversely the trace bound and H2 control give X_Z.

Suppose Z''-Z'+AZ=F and the already-paid coarse bound gives positive exponential decay of X_Z. If F has local L2 rate beta>0, the two low coordinates, in a suitable order, satisfy

    y0''-y0'=F0, y1''-y1'=F1-y0.

For a decaying h the unique decaying solution of y''-y'=h is

    y(t)=integral_t^infinity (1-e^{t-s})h(s) ds.          (5.1)

The excluded homogeneous modes are 1 and e^t. Applying (5.1) twice treats the Jordan coupling; local H2 bounds follow by the equation. Coarse decay already incorporates the original moment compatibility. One neither deletes the Jordan sector nor presumes new moment conditions on arbitrary forcing.

For a high mode the scalar equation is y_k''-y_k'-lambda_k y_k=F_k, with real-line inverse kernel

    G_k(tau)=-e^{-mu_k tau}/(2mu_k+1), tau>=0,
    G_k(tau)=-e^{(mu_k+1)tau}/(2mu_k+1), tau<0.          (5.2)

The derivative has jump one. Multiply Z by a smooth cutoff equal to zero before T and one after T+1. The additional forcing 2chi'Z'+(chi''-chi')Z is L2 and compactly supported. Unweighted L2 uniqueness identifies the high part with convolution by (5.2), so no artificial vanishing boundary data at T are imposed.

For 0<d<mu_2, conjugation by e^{dt} gives the multiplier denominator

    m_k(xi)=(i xi-d)^2-(i xi-d)-lambda_k,
    |m_k(xi)| >= xi^2+lambda_k-d(d+1)
                 >= c_d(xi^2+lambda_k).                (5.3)

Plancherel, (4.3), and (5.3) bound both A and two time derivatives uniformly in k. Weighted L2 of the forcing is finite for d<beta. There is no circular assumption that the solution already has weight d: construct the weighted inverse from this forcing, or conjugate the explicit kernel, and identify it with the unweighted decaying solution. The compact cutoff source only changes constants. Thus X_Z(t)=O(e^{-dt}) for every d<min(beta,mu_2).

If beta>mu_2, the first-mode convolution separates a coefficient

    D=-(2mu_2+1)^{-1} integral_R e^{mu_2 s} F_{cut,2}(s) ds

from two future integrals. The integral converges by Cauchy–Schwarz on unit intervals. Subtracting D e^{-mu_2 t} leaves a remainder with any rate below beta. Its second time derivative is estimated from the scalar equation, not a derivative of F. For k>=3 repeat (5.3) with d<mu_3. Formula (5.1) handles the low sector at every rate below beta. Therefore

    Z=D h_2 e^{-mu_2 t}+Z_*,
    X_{Z_*}(t)=O(e^{-gamma t}),
    mu_2<gamma<min(beta,mu_3).                          (5.4)

This is the required uniform high-mode graph estimate. Summing absolute values of unweighted modewise estimates would not justify it; the diagonal Fourier bound does. No trace of F_bulk and no derivative of the independent boundary forcing occurs. Once the primary spectrum and the elementary completion in §4 are available, this is a standard separated scalar resolvent calculation.

## 6. Finite nonlinear bootstrap and the first coefficient

Choose s with mu=mu_2<s<3/2, possible precisely because the first root lies below 2. If X has rate d>0, (3.1) makes the forcing in (4.2) have rate min(d+epsilon,s). Section 5 improves X to any rate below min(d+epsilon,s,mu). Increase d in finitely many steps of size less than epsilon/2 until d<mu and d+epsilon>mu. The next forcing then has some beta>mu, so (5.4) applies. This uses the established coarse norm at every step, rather than an assumed sharp weight.

Writing the boundary coordinate of (5.4) as theta=B e^{-mu t}+theta_*, theta_* has H2 rate gamma>mu. Consequently a=-mu B e^{-mu t}+a_* with a_* H1 at that rate, and both remainders have corresponding uniform bounds by one-dimensional embedding. The leading bulk odd profile is

    O0=D[(h_2)_bulk-(h_2)_b cos(phi/2)]e^{-mu t}.

It satisfies the exact leading bulk and boundary equations. There is no division by D or B. If B=0 the estimates are stronger and all the same conclusions follow. No resonance obstructs the extraction: the additive rough error has rate chosen strictly greater than mu, and the even interaction gains a positive coarse exponent. This finite bootstrap and stable coefficient integral are conventional asymptotic consequences of an exponentially decaying perturbation of the paid spectral system.

## 7. Essential-uniform trace upgrade with measurable fidelity

An H2 strip remainder alone does not give the frozen essential-supremum curvature limit. The missing norm is supplied by the very elliptic trace cycle already used in the primary proofs, with the faster remainder inserted.

Let V=O-O0, b=a-a0, a0=-mu B e^{-mu t}. The spectral conclusion gives V in H2 and b in H1 at rate gamma>mu. In one time dimension the trace V_phi(0,.) belongs to H^{1/2} and hence to every finite Lp, with the same rate on smaller intervals. The full O_phi trace therefore has Lp rate mu. From the formula for N, the coarse decaying supremum norm of e_phi, a=O(e^{-mu t}), and |H2|=O(e^{-st}),

    ||N||_{Lp} = O(e^{-beta0 t}),
    beta0 <= min(mu+epsilon,3mu,s), beta0>mu.

Subtract the leading angle equation:

    b'-b=-4c V_phi(0,t)+N.                              (7.1)

It follows that b' has an Lp rate strictly above mu for each fixed finite p. The exact bulk remainder equation, moving the harmless a^2 term to the left, is

    [partial_tt-partial_t+(1+a^2)partial_phiphi+1/4]V
      =(b'-b)S_phi+(a'-a)e_phi+2a e_tphi-a^2 O0_phiphi.   (7.2)

V has zero Dirichlet boundary values at 0 and pi. For a fixed p>2, §2 supplies decaying W^{2,p} of e, with some epsilon_p>0. Every right-hand term in (7.2) thus decays in Lp faster than e^{-mu t}. The H2 bound already controls ||V||_Lp at the faster rate. Uniform ellipticity and the bounded a,a' give fixed-strip boundary W^{2,p} estimates, then C^{1,alpha} by Sobolev embedding. One works on shorter time intervals so no corner boundary data are needed; reflection across the spatial sides is also available since the coefficients are phi-independent.

Consequently V_phi(0,t) has a supremum rate strictly greater than mu. In N, O_phi now has a supremum rate mu; all other factors have their previously recorded bounds. Therefore N has an L-infinity rate strictly greater than mu. Equation (7.1) gives an essential-supremum bound for b' at such a rate. Overlapping fixed strips and decreasing the exponent if necessary yield some eta>0 with

    theta=B e^{-mu t}+O(e^{-(mu+eta)t}),
    a=-mu B e^{-mu t}+O(e^{-(mu+eta)t}),
    a'=mu^2 B e^{-mu t}+O_ess(e^{-(mu+eta)t}).           (7.3)

At no point was H2 differentiated or assigned continuity. The exponent may depend on the solution and the chosen finite p. This is sufficient for the frozen statement. DFG's page-13 argument and DF §5.2 already perform the underlying trace-to-Lp-to-W^{2,p}-to-C1 operation; the new forcing enters as an undifferentiated scalar in (7.1). The last essential-supremum step is an algebraic use of that equation. Roughness therefore does not leave an unpaid analytic operation.

## 8. Graph coordinates and every endpoint conclusion

Set x(r)=r cos theta(t), y(r)=r sin theta(t), t=-log r. Direct differentiation gives

    x_r=cos theta+a sin theta, y_r=sin theta-a cos theta,
    x_rr=((a-a')sin theta-a^2 cos theta)/r,
    y_rr=((a'-a)cos theta-a^2 sin theta)/r,
    x_r y_rr-y_r x_rr=(a'-a-a^3)/r.                     (8.1)

By (7.3), x_r tends to one and is positive after shortening the chart; x=r(1+O(r^{2mu})). It is a locally bi-Lipschitz change of variable, preserving null sets. Thus y=psi(x), and for positive eta1,eta2 possibly smaller than eta,

    psi(x)=B x^{1+mu}+O(x^{1+mu+eta1}),
    psi'(x)=(1+mu)B x^mu+O(x^{mu+eta1}),
    psi''(x(r))=(a'-a-a^3)/[r(cos theta+a sin theta)^3],
    psi''(x)=mu(1+mu)B x^{mu-1}
                        +O_ess(x^{mu-1+eta2}).         (8.2)

The second-derivative assertion uses (8.1), not differentiation of a big-O remainder. Since mu>1, it gives an essentially bounded second derivative near zero tending essentially to zero. The local C1,1 arc interface covers the rest of the shortened interval. Together with the continuous tangent it yields C1([0,delta]) intersect W^{2,infinity}((0,delta)). The first-derivative expansion divided by x tends to zero, giving the classical one-sided psi''(0)=0. The positive power gains in (8.2) imply the three specified sup/essential-sup limits. B may vanish throughout this argument.

Because p was arbitrary and every normalization and estimate was local, no domain boundary regularity beyond the frozen class, uniform chart radius, global number of components, or extra differentiability has entered. The determinant and the change of variables close the full endpoint scope.

## 9. Disposition of the contribution objections

The coarse H2/W^{2,p} interface is supplied by full even C1 decay plus ordinary elliptic estimates, not the projected-even bound alone. The variational representative is the actual Appendix A object. The boundary-state sign is fixed in (4.2). The generalized zero sector is retained, its moment compatibility used only through the paid coarse decay, and the graph domain is established by closedness. The high-mode bound is uniform by (5.3). The first coefficient comes from a convergent scalar integral after a finite bootstrap, including the zero case. The rough-data improvement uses finite Lp estimates before the supremum trace and never differentiates fidelity. Formula (8.1) supplies the exact graph determinant. These are resolved compatibility issues in the strongest reduction, not a checklist of alleged gaps.

The author's independent boundary-coordinate formulation is useful and avoids a wrong naive boundary trace of R. However, avoiding that invalid route does not establish substantial contribution when (4.1)–(4.3), the diagonal resolvent and the primary elliptic cycle pay the same construction. Nor do an infinite spectrum, a Jordan block or measurable data by themselves establish nonroutine novelty: the displayed estimates explicitly handle each of them.

Accordingly there is no remaining contribution-specific mathematical obligation in this bounded comparison. The separate correctness review of the entire unchanged theorem remains necessary and is not discharged here. The judgment is conditional exactly in that sense; it is neither a correctness finding nor a request for a weaker theorem. I make no exhaustive worldwide-priority or perfect-history-clearance claim. Parent alone may integrate this review and adopt any disposition; campaign counts and latestR041 are unchanged.

## 10. Evidence boundaries

The exact dependency and actual semantic-reading record is private/READING-AND-ISOLATION.md, supported by private/actual-read-log.jsonl and the exact selected manifests. Reading extents include the whole operative later Chapter 5, full DFG proof, full Deangelis v2 and LL, AM's full §§7–8 and Appendix A, and the exact permitted original history sections. They do not include all DF chapters, all AM earlier proofs, every edition or a literature-wide search. Metadata, hashes and snippet navigation are not substituted for those proof readings.

Protected source, primary, original-history and copied-author material and their named metadata remain private under original rights. The detached seal and tiny copied integrity controls authenticate artifacts only. They assign no mathematical gates. Authorized provenance: Codex / GPT-6 Astra / high / default service tier, first independent contribution review, no nested agents.
