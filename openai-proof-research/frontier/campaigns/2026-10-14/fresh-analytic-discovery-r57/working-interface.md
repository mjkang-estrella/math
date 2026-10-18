# The q=4 occupation endpoint: pre-freeze working interface

Author: Myeongjin Kang. Author-side research, not an independent review.
The pinned source theorems are stipulated. No theorem is nominated, and no
full target or logarithmic normalization has been frozen. This note records
what was actually obtained before deciding whether a full proof is credible.

## Intended question and normalization status

The concrete starting model is exactly the square Dobrushin model in the
natural-occupation source: q=4, p=2/3, D=(0,1)^2, a=(0,0), b=(1,1), top and
left arcs wired, bottom and right arcs free, omitted wired boundary edges
declared open when drawing the strand. Count every full medial-edge
traversal once at its projected midpoint; do not count terminal half-edges
or artificial connectors. The sought object is the entire interface jointly
with its occupation measure, including total mass, and the SLE4 Minkowski
content of that same limiting curve. A mere interior restriction, a
subsequence, an unspecified arm-probability normalization, or convergence
of the unparametrized curve is not a substitute. Domain extension beyond
the source's square has not been selected or justified: the source's
occupation theorem itself is a square theorem, unlike some of its curve
companions. In particular no arbitrary-domain finite-total-content claim
has silently been adopted.

Aharony–Asikainen, cond-mat/0206367v2, Table 1 and equation (6), predict
hull mass R^(3/2)(log R)^(1/4). Their c_H/a=-1/4 is opposite to the
external-perimeter coefficient c_EP/a=1/4. Thus the *predicted* candidate
counting factor is n^(-3/2)(log n)^(-1/4), up to a positive constant. Their
paper gives RG/Coulomb-gas predictions, not a rigorous arm-amplitude
contract. Matching their hull convention to the actual Dobrushin medial
traversals is also an obligation. Neither exponent nor constant is proved
here. Salas–Sokal hep-lat/9607030v1 §§1–2.1 describes the marginal RG flow
and its log-log corrections; it does not supply that missing microscopic
probability theorem. The downloaded filename cardy-salas-sokal is historical;
the actual authors are Jesús Salas and Alan D. Sokal.

## What the operative source pays

The occupation manuscript works at fixed 1<=q<4 and explicitly does not
claim uniformity as q increases to 4. With sqrt(q)=2 cos(lambda), its
angular construction assumes lambda>0. Its exchange R-matrix, exponential
rapidity decay, width tail, off-axis Laplacian gain, electric-charge
amplitude, exact-two-arc outward coupling, and microscopic calibration form
a chain of operations. The power remainder in the electric formula is
expressly used for a convergent amplitude, not only a scaling exponent.

The embedded c=2 GFF proof uses DKLM Theorem 2.8 at this endpoint; it does
not construct the lambda=0 angular representation by continuity. DKLM's
actual Definitions 2.6–2.7 and Theorem 2.8 concern finite-energy tests,
negative regularity and off-diagonal products of distinct increments.
Point insertions with repeated coincident endpoints have infinite energy
and are not covered by those tests. Theorem 9.1 identifies a rescaled
spectral limit but gives no signed logarithmic correction or microscopic
vertex-operator renormalization. Its proof obtains the measure by GFF
convergence and Laplace-transform uniqueness. The actual proof overview
explicitly distinguishes this from a rigorous RG analysis.

The q=4 loop companion has a bulk four-arm limsup estimate at fixed
continuum radii and derives regular-domain fields. Its spin-two argument
has a special positive coefficient for two passages at each box. This is
not a microscopic two-arm amplitude theorem. The q<4 occupation paper's
jagged-corridor regeneration uses arbitrary-boundary crossing inputs in
its stated q<4 range. No endpoint extension of that operation has been
proved in this round.

## Exact signed endpoint row calculation

This is finite matrix algebra, not an assertion about an endpoint
thermodynamic representation. Write

    R_lambda(lambda t) = [sin(lambda(1-t))/sin(lambda), 0, 0, 0;
                          0, sin(lambda t)/sin(lambda), 1, 0;
                          0, 1, sin(lambda t)/sin(lambda), 0;
                          0, 0, 0, sin(lambda(1-t))/sin(lambda)].

For each fixed t, its limit is R_0(t), with outer entries 1-t and middle
block [[t,1],[1,t]]. Let D=diag(-1,1,1,-1), let P swap the two tensor
factors, and let Q=DP. Then

    R_0(t)=tD+P=D(tI+Q),   Q^2=D^2=P^2=I,   DP=PD.

Consequently, for t^2!=1 and every matrix M,

    (I+Q/t) M (I+Q/t)^(-1) - M
       = [t[Q,M] + M-QMQ]/(t^2-1).                     (1)

Multiply both sides by t^2-1 to check (1); it follows immediately from
(tI+Q)^(-1)=(tI-Q)/(t^2-1). For a diagonal M, the exterior D factors in
conjugation by R_0 do not change M, and they preserve the zero-total-charge
subspace used below. Thus this is the relevant leading transport term.

Take H=diag(1,-1), M=I tensor H, and
v=(|01>+i|10>)/sqrt(2). The vector v has total H-charge zero. In that
subspace, Q=[[0,1],[1,0]], M=diag(-1,1), and

    <v,[Q,M]v>=2i,   <v,(M-QMQ)v>=0.

At t=iy, y real and nonzero, (1) therefore gives the exact real correction

    <v, ((I+Q/(iy)) M (I+Q/(iy))^(-1)-M) v>
        = 2y/(1+y^2).                                (2)

The leading coefficient is nonzero. This state is also obtained, up to
a scalar phase, by applying I tensor exp(-i pi H/4) to the SU(2)-invariant
singlet (|01>-|10>)/sqrt(2). More generally, a diagonal mark of angle theta
on that singlet gives the correction -2y sin(2 theta)/(1+y^2), so the
first-order term need not vanish even for arbitrarily small fixed marks.
This verifies compatibility with the finite singlet/diagonal-mark algebra;
it still does not identify the actual plane exterior state. In contrast,
a diagonal density matrix kills the commutator trace; special states can
have cancellation.
The conclusion is precisely that ice/charge conservation alone does not
prove such cancellation. We do not assert v is a physical exterior state
of the endpoint lattice model, nor that (2) is the lattice arm drift.

For the source's exchange, t=(z'-z)/pi at lambda=0. Its angular variable
is z=-i Log w, so y grows proportionally to logarithmic spectral dilation.
This is a rapidity variable. It has not been identified with the Euclidean
dyadic scale of a microscopic arm probability. No equality of these two
scales, and no Euclidean logarithm exponent, follows from (1)–(2).

## Exact renormalized telescoping obligation

For an explicitly specified lattice two-arm probability a_k across scales
1 and 2^k, put b_k=2^(k/2) a_k. The proposed hull prediction would ask for
b_k/k^(1/4) tending to a positive constant (the log(2) factor can be
absorbed into that constant). An exact sufficient signed identity is

    log(b_{k+1}/b_k) = (1/4) log((k+1)/k) + e_k,
    sum_{k>=k0} e_k converges.                         (3)

Indeed the logarithm of b_K/K^(1/4) equals its initial value plus the
partial sum of e_k. Absolute summability is sufficient, not necessary.
An estimate e_k=O(log(k)/k^2), for example, would suffice. This is an
ordinary telescoping observation, not a new theorem about FK.

Even identifying a first-order coefficient 1/(4k)+o(1/k) would not finish
the amplitude. Taking e_k=1/(k log k) for k>=2 produces a divergent extra
factor of logarithmic order, while keeping precisely that first-order
coefficient. Conversely a nonsummable absolute bound does not imply the
actual signed series diverges. Equation (3), or an equally effective
renormalized identity, is the missing useful operation. It must be tied to
the correct microscopic arm event and then to full strand occupation,
not inferred from the formal rational-row limit.

## Current status

The source contracts and the actual primary comparisons do not yet give
(3), an equivalent critical vertex-operator estimate, or the endpoint
outward coupling needed to finish calibration. The full endpoint
occupation question is unresolved here. The finite signed calculation
above pinpoints a possible cancellation that would have to be proved in
the physical state; it does not refute the question and does not count as
a substitute result. No source theorem has been contradicted or audited.
