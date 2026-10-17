# Family225 nonlinear screen: the multiscale exponential interface

Myeongjin Kang; no affiliation. Original prose CC BY4.0.

No target was frozen and no result is nominated. This document records the exact unresolved operation after a technical partial deduction. It is not a counterexample to six-vertex multiplicative chaos, nor a claim of global novelty.

## Object screened

For the source's specific iterated balanced-torus plane state at fixed c in (0,2], pin the height by one smooth compact probability density rho. Put

    X_delta(x)=h_delta(x)-<h_delta,rho>,
    Y_delta(x)=sqrt(2pi)/sigma(c) X_delta(x),
    sigma(c)^2=1/arcsin(c/2).

The limit Y has logarithmic covariance coefficient one, with the bounded pinning terms retained. A natural nonlinear question asks whether, on compact planar sets, the measures

    exp(beta Y_delta(x)) / E exp(beta Y_delta(x)) dx

converge to the corresponding pinned Gaussian multiplicative chaos for fixed 0<beta<2. The exact expectation avoids assuming that half the variance is already the correct microscopic normalizer. Each finite-delta expectation is finite because the unit height jumps bound the pinned field on a fixed compact set by a deterministic O(delta^-1). This is a motivating question, not a frozen claim or claimed theorem.

## What is paid

The stipulated source establishes finite-energy neutral-test convergence, negative-regularity convergence, all fixed mixed smooth moments, and fixed-order moments of increments with mutually disjoint endpoint sets. The source covariance uses the actual height convention and retains the common pin. The technical note neutral-block-exponential-bound.md tracks the moment order in the source's energy argument, obtaining uniform small exponential moments for a neutral single-scale block when 0<c<2. This is a refinement of existing operations, not an independent substantial advance.

For every fixed smoothing radius epsilon>0, the continuous mapping theorem already gives convergence in law of the smoothed exponential random measure with a prescribed continuum variance normalizer. Taking delta to zero first and epsilon to zero second gives the usual sequential approximation of chaos. Selecting an unspecified sufficiently slow epsilon(delta) by a diagonal argument adds no microscopic theorem or substantial new mechanism. Neither construction is nominated here.

## Why the actual microscopic passage remains unpaid

Even in the L2 parameter range beta^2<2, one needs simultaneous control of the two scales epsilon and delta and of two points as they approach each other. A sufficient type of input would be uniform normalized exponential-transform asymptotics for finitely many differently smoothed fields, including the microscopic scale, together with an integrable bound of the form

    E[W_delta,epsilon(x) W_delta,eta(y)]
        <= C (|x-y|+max(epsilon,eta,delta))^(-beta^2),

where W denotes the correctly normalized exponential. Constants, pinning factors and a harmless large-distance cutoff are understood on a fixed compact set. Off the diagonal, the mixed expression must converge to the correct exponential covariance. The required statements are not established here.

The source's offdiagonal theorem excludes coinciding endpoints from different increments. Its proof expands each fixed-order product into dyadic endpoint blocks and obtains a tail C_k sum_j (1+j)^(k-1) 2^(-tau_k j). It does not control the sum over all orders under an exponential tilt. More importantly, its separated-block lemma requires spatially separated centers. Repeated blocks around one insertion share their center. No independence or conditional version is supplied by that lemma.

The one-block exponential bound supplies only an O(1/J) exponential neighborhood after J nested scales by Holder or Minkowski. J grows like log(delta^-1). The missing step is a fixed-charge estimate for the nested sum, including the two-point collision geometry and normalization. A sharper single-block constant does not remove this distinction.

## An exact countermodel to the moment-to-exponential shortcut

For each integer J let p_J=exp(-sqrt(J)), and let B_J equal +1 or -1 with probability p_J/2 each and zero otherwise. Set every one of J blocks equal to B_J. Every individual block has mean zero and E exp(s|B_J|)<=exp(s) for all s>=0, uniformly in J. Every fixed joint polynomial moment of the blocks tends to zero. Even their entire sum S_J=J B_J tends to zero in every fixed Lq, since

    E|S_J|^q=J^q exp(-sqrt(J)) -> 0.

Nevertheless, for every fixed nonzero gamma,

    E exp(gamma S_J)=1-p_J+p_J cosh(gamma J) -> infinity.

Thus all fixed moments and uniform one-block exponential bounds do not by themselves identify the exponential transform of a growing nested sum. This is only a countermodel to that inference; it is not a six-vertex field and does not satisfy every spatial source identity.

## Primary proof comparison

Lambert–Ostrovsky–Simm, arXiv:1612.02367v2, Section2.1, Assumptions2.1–2.4 and Theorem2.1: the L2 mechanism compares microscopic and fixed-smoothed chaos by expanding their squared difference. Uniform exponential asymptotics cancel its terms; the logarithmic covariance bound supplies an integrable collision majorant. The fixed-order field CLT is a separate premise. That proof provides a sufficient transfer mechanism once the stronger hypotheses hold; it does not derive those hypotheses from moment convergence. Our missing operation is precisely upstream of that transfer.

Duminil-Copin–Kozlowski–Lammers–Manolescu, arXiv:2603.06268v1, Theorem4.5 and Section21: the regularity proof expands fixed-order increment products through the level-line tree, pairs intersection counts, extracts disjoint annuli and bounds their arm counts. The annular shrinking loss and exponent depend on the moment order (the displayed exponent is proportional to 1/k^2). These are meaningful correlation bounds, not already the required uniformly charged transform asymptotics. Their actual proof body was read; no inference was made just from its GFF headline.

Averous–Duminil-Copin–He–Lammers–Manolescu, arXiv:2610.07454v1, Theorem1.4 is conditional on full-plane GFF convergence in its stated c>=1 setting. Its finite-domain extension should not be renamed as a fresh source225 consequence. Lemma4.1's proof also uses an existing uniform exponential oscillation tail for explored flower boundaries to bound a conditional averaged Laplacian. That additional primary operation is acknowledged; it is not itself the microscopic fixed-charge height-transform assertion above. Only the stated portions of this paper were read, not the whole manuscript.

## Decision

No substantial complete candidate emerged. The single-block Lq/exponential estimate is technical and retained honestly. The exact unpaid mechanism is a dimension-two, merging-point, fixed-charge tilted estimate down to the lattice scale (or another construction that supplies the same normalization and uniform-integrability passage). No endpoint, parameter-window, slowly smoothed or finite-domain substitute is submitted. The screen ends before freeze rather than claiming a narrowed theorem.


## Earlier transfer/generating-function operations checked before closure

At the parent's request, the preceding sections were inspected beyond Section7. The following distinctions are operative, not an inference from the absence of the word cumulant.

1. Section2, Exact finite-word expansion, gives a finite sum of explicit deleted-root determinants for arbitrary auxiliary marks. A microscopic exponential string can indeed be represented using diagonal marks exp(t_j Z) at successive sites. However its word length grows with the lattice path. Section3 fixes word lengths, matrices, derivative orders and compact sets before its limiting procedures and expressly disclaims uniformity in an unbounded word length. Its joint-tail proof chooses flags for the fixed determinant size; its constants and decay exponent depend on the fixed word. The complete word-kernel and diagonal-clustering proofs were read. Their local holomorphy and separated-group factorization do not provide a connected cumulant expansion with explicit order bounds for nested source strings.

2. Section4 constructs a common analytic disc for the row spectral parameter near a swap point. Commuting that row through a fixed word has word-dependent terms and bounds. This spectral-parameter radius is not a charge-parameter radius for a growing exponential height string. The diagonal boost estimate is also stated for fixed words/groups. The diagonal-twist cocycle is obtained by differentiating equal-twist commutation once at zero; it identifies a current and a covariance measure, not a finite-charge logarithmic generating function.

3. The two-twist overlap is a different exact finite determinant, retaining the whole root-set size. Section2 explicitly asserts only a finite-chain local logarithm. Section5 takes its quadratic coefficient before either array limit. The full finite trace and Fourier-symbol proof was read: it controls first and second root jets, weighted matrix Taylor traces, sparse-end deletion, and the bulk quadratic symbol. Its all-order midpoint accuracy is for each fixed derivative order, with order-dependent constants. The conclusion explicitly does not assert a common analytic neighborhood or uniform finite-twist expansion. Thus neither source analyticity assertion can be substituted for the requested fixed-charge bound.

There is a useful formal check showing exactly why the bulk symbol looks promising, but it does not pay the finite-matrix passage. Let a=2pi z and |a|<pi. The two formal relative symbols give

    F(a) = (1/(2pi lambda)) integral_0^infinity
             log[(1+2u cos(a)+u^2)/(1+u)^2] du/u.

This integral converges at both endpoints. For a in a compact subinterval of (-pi,pi), differentiation is dominated and

    F'(a)=-(sin(a)/(pi lambda)) integral_0^infinity
                                  du/(u^2+2u cos(a)+1)
         =-a/(pi lambda).

For 0<a<pi the last integral equals a/sin(a), by completing the square; evenness extends the result to negative a and continuity covers zero. Since F(0)=0,

    F(a)=-a^2/(2pi lambda)=-2pi z^2/lambda.

Adding the formal pair-product contribution 2z^2 and substituting z=t/[2(pi-lambda)] reproduces exactly -t^2/[2lambda(pi-lambda)]. This is an exact identity for the formal continuum symbol. To turn it into a uniform finite-charge overlap asymptotic, one must prove a common nonvanishing charge neighborhood, uniform control of the moving roots and of the full logarithmic determinant (including sparse edges), and the two-limit comparison there. Even that staggered-vacuum fidelity is a distinct object from multiple spatial microscopic height-source tilts; a source-string identification and uniform collision estimates would still be necessary. No such steps are asserted proved.
