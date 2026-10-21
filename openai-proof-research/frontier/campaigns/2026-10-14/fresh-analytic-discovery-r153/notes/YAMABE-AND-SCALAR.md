# Strongest integrated reduction after Ge–Wang

PREFREEZE feasibility notes. These replace the provisional 'Bochner absorption is unpaid' diagnosis in FEASIBILITY.md. They are not a new theorem nominee or a contribution verdict. The actual Ge–Wang author PDF was read completely before this calculation. Its Lemma 1, with the standard Yamabe normalization, says

  96 S(g) <= Y([g])^2,   S(g)=integral sigma2(A_g),
  96 S(g)=integral R_g^2 - 12 integral |E_g|^2.

This inequality is valid with either sign of Y. The identity S(g)=S(g_Y) uses conformal invariance in dimension four. Yamabe existence is a classical input, not re-proved; Ge–Wang's actual proof uses the constant-scalar minimizer and the algebraic sigma2 inequality. The normalization Y=6Y1 matters.

## Even the scalar sign can be paid

Consider a sequence of smooth closed connected four-manifolds with nonzero Euler characteristic, and

  eta_j=||E_j||_2 -> 0,   sigma_j=||F_j||_2 -> 0,
  F=max(0,-minimum sectional curvature).

No pointwise curvature sign is assumed in this calculation. Orthogonal-frame summation gives R_-<=12 F and |Rm|<=A(|R|+F). Chern–Gauss–Bonnet gives 1<=|chi|<=C integral |Rm|²; orientation double covers give the same statement if necessary.

For all test functions the Yamabe quotient is >=-||R_-||_2, by Holder. If Y<=0, then |Y|<=12sigma. Ge–Wang Lemma 1 gives

  integral R² = 96S + 12eta² <= Y²+12eta² <=144sigma²+12eta².

This and the curvature inequality contradict 1<=C(eta²+sigma²) for small errors. Therefore Y>0, even without R>=0. Testing the Yamabe quotient on 1 gives Y<=Ravg sqrt(V), hence Ravg>0 and we may normalize Ravg=12.

Now 96S<=Y²<=144V implies

  ||R-12||_2²<=12eta²,    ||Ric-3g||_2²<=4eta².

This is the sharp four-dimensional almost-Schur estimate at positive Yamabe sign, directly from the actual Ge–Wang proof. The earlier Bianchi route's difficulty is paid, not an obstruction.

The Euler bound and |Rm|<=A(|R|+F) give a uniform V>=v0. Also the standard local Euclidean Yamabe test gives Y<=Y(S4)=8sqrt(6)pi, while S>=1.5V-eta²/8. Thus

  V <= 8pi²/3 + eta²/12.

For small errors, S>=c>0 and Y>=sqrt(96S)>=y0>0. Its variational definition gives

  Y||f||_4² <= 6||grad f||_2² + 12||f||_2²
                 + ||R-12||_2 ||f||_4².

Absorbing the last term gives a uniform ordinary Sobolev constant. Source EG's cutoff iteration then supplies Vol B(x,r)>=v*r^4 for 0<r<=1. Disjoint-ball packing and the upper volume bound bound the initial diameter. No segment inequality, initial Ricci lower bound, or new cover theorem is needed.

## The negative scalar part does not break the common lifespan

Let g(t) be each individual unnormalized Ricci flow, initially with its own lifespan. Put u=R_- and q=||u(0)||_2<=12sigma. In dimension four,

  (partial_t-Delta)u <= -u²/2,
  d/dt integral u² <= -2 integral |grad u|².

Indeed on {R<0}, scalar evolution gives -(2|Ric|²)<=-R²/2, while volume variation contributes +u³ to the u² integral, cancelling the -u³ from its reaction. Smooth positive-part approximation justifies the integrated inequality. Consequently

  dV/dt <= q sqrt(V),   sqrt(V(t))<=sqrt(V(0))+qt/2.

This gives a uniform upper volume bound on existing times t<=1. It does not presume a common lifespan.

The initial Sobolev inequality and q small imply, for ||f||_2=1,

  integral (4|grad f|²+R f²) >= (4-q S0)||grad f||_2²-q S0.

Jensen and the initial Sobolev inequality therefore give the source uniform initial lower Perelman mu bound for entropy parameters 0<tau<=2. Monotonicity transfers this to every existing time t<=1 with tau<=1.

In the resulting log-Sobolev inequality REPLACE R BY R_+ ON THE RIGHT. This only increases that right side. Choose tau=(1+integral(4|grad f|²+R_+ f²))^-1 and use the source support/truncation lemma with nonnegative potential R_++1. Thus

  ||f||_4² <= S1 integral (4|grad f|²+(R_++1) f²).

Using R directly in that truncation lemma would be unjustified because its potential is assumed nonnegative. The positive-part replacement explicitly pays that compatibility issue.

Set K0=12A and K'=Cq K², as in EG, with A chosen for |Rm|<=A(|R|+F). The elementary inequality |R|<=12+|R-12| gives

  ||(|Rm|-K0)_+||_2 <= A(sqrt(12)eta+sigma).

The curvature tail w=(|Rm|-K)_+ gives R_+<=C(K+w), so small ||w||_2 absorbs the weighted Sobolev term exactly as in EG. The now possibly adverse volume term in d integral w² is

  integral R_- w² <= C integral (K+w)w².

This only changes the coefficients of the already absorbed cubic term and bounded-background quadratic term. The first-crossing proof, gradient estimate, noncollapse and continuation give EG's common T and |Rm(t)|<=A1/t. The parameter hierarchy is chosen before the sequence index; q and the initial tail tend to zero. No independent restarts or time-zero pointwise bounds are used.

## Identification of the same compact limit

For L=Ric-lambda(t)g, lambda=3/(1-6t), EG's homogeneous equation still holds. The adverse volume term is again bounded by C(K+w)|L|², so the original Sobolev absorption propagates ||L(t)||_2<=C eta. Total curvature energy remains uniformly bounded by the bounded K, controlled w and the volume bound.

For the convex sectional deficit F, the source mollified chain rule gives (partial_t-Delta)F<=C|Rm|². Its volume term is now bounded by

  R_- F <= C |Rm|².

Therefore integral F(t)<=V(0)^(1/2)sigma+Ct. Compactness of positive-time slices follows from EG's unchanged ball packing, injectivity estimate and compact-embedding argument, directly on the base. The limit satisfies Ric_h=3h and h(t)=(1-6t)h. Passing j->infinity for each t>0 gives (1-6t)integral F(h)<=Ct; then t->0 gives sec_h>=0.

Thus the entire sign-removal/quotient route is accounted for by the actual EG operations, Ge–Wang's Yamabe argument, elementary critical scalar-energy cancellation, and positive-part/Holder modifications. The source classification applies on the base's compact Einstein limit. It yields a manifold diffeomorphic to a finite free isometric quotient of S4, CP2, or the equal sphere product; it does not identify the original metric. This is a paid strongest-composition reduction, not a claimed nonroutine discovery.

## Exact limit of what this calculation says

The explored threshold is existential and dimension-only for eta²+sigma², with chi!=0 and no curvature sign. A contradiction sequence supplies a threshold once the credited inputs are accepted. No numerical epsilon, time-zero metric rate, dynamical attraction, all chi=0 classification, or new-to-literature claim is supplied. Original I30 scope and dispositions are untouched. No theorem has been frozen, since no operation beyond source/classical composition has been identified as a substantial research contribution. Primary transitive proof coverage remains incomplete; see READING-LIMITS.
