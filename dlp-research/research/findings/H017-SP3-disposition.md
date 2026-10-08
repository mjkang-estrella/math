# H017 SP3: valid tensor encoding, exact S3 parametrization, missing detector

2026-10-08. Claude Opus initial proposal is preserved verbatim in
H017-coordinate-opus-raw.md, including unaccepted claims. Native Astra
/root/h007_additive_relations completed independent mathematical review;
root derived the explicit parametrization below and both native Astra and
native Sol independently checked the expansion. No numerical test, timing,
new Lean claim or verified improvement.

## Exact bridge

Take E: y²=f(x)=x³+a*x+b over Fp, p>3, nonsingular, with odd prime group order q.
Odd order excludes rational2-torsion; the cubic has no Fp root, hence is
irreducible. Let K=Fp[theta]/f. For affine P=(x,y),

    Norm(x−theta)=f(x)=y² !=0.

The quadratic characters of z in K and Norm(z) in Fp agree, so x−theta is
a square. Choose sigma(P)²=x−theta, without requiring a descent oracle.
The coefficient of theta² in sigma(P1)*sigma(P2)*sigma(P3) vanishes exactly
when some signed choice of the three affine points sums to O.

Forward: a signed collinear triple on y=lambda*x+mu satisfies
f(X)−(lambda*X+mu)²=product_i(X−x_i). Evaluate at theta. Conversely, a zero
tensor coefficient gives sigma1*sigma2*sigma3=A+B*theta, so

    f(X)−product_i(X−x_i)=(A+B*X)².

The two sides agree modulo the irreducible cubic and have degree at most2,
so the equality is exact. Ordinates A+B*x_i give the required signs. Repeated
roots use intersection multiplicity (tangencies/flexes); they are not arbitrary
independent ordinate choices. Infinity is outside this affine definition and
needs an explicitly declared branch. This proves a signed group relation,
not yet a nonzero-coefficient relation recovering the target scalar.

## Root's explicit parametrization, independently checked

For H=(u,v) and P=2H, let lambda=(3u²+a)/(2v) and
l(X)=lambda*(X−u)+v. The tangent identity is

    f(X)−l(X)²=(X−u)²*(X−x(P)).

Hence sigma(P)=l(theta)/(theta−u) is one square root. Using
(theta−u)*(theta²+u*theta+u²+a)=−v² gives

    2v*sigma(P)=w(u)=u²−a−2u*theta−2theta².

The projective vector [u²−a : −2u : −2] lies on the nonsingular conic
z1²+2*z0*z2−a*z2²=0. Reduction modulo theta³=−a*theta−b yields

    [theta²] w(u1)*w(u2)*w(u3) = −2*S3(u1,u2,u3).

Explicitly this is

    −2*sum_(i<j) ui²*uj² + 4*u1*u2*u3*(u1+u2+u3)
    +4a*sum_(i<j) ui*uj +8b*sum_i ui −2a².

Here S3 is the standard summation polynomial; root checked its formula in
[Semaev §2](https://arxiv.org/pdf/1504.01175). Thus generate labelled H first
and compute w(x(H)) directly. The homogeneous test needs neither an extension
square root nor division by v nor an explicit doubled point. Doubling is
bijective on the odd-order group, so the signed dependencies are unchanged.
The parameter u must remain an abscissa of a rational elliptic point; arbitrary
conic points are not automatically admissible inputs.

This eliminates the proposal's mandatory extension-square-root setup estimate.
Its claimed ~2000 field multiplications versus ~6 per rho step was not a local
measurement and is not accepted as a calibrated comparison.

## Complete-work decision

Three independently generated labelled lists of length n require their full
point generation, coordinate arithmetic, storage and unsuccessful attempts.
At n on the scale q^(1/3), a complete useful-zero detector with cost
O(n^(3/2−epsilon)*polylog(q)), bounded success loss, and charged setup could
change the exponent relative to the square-root baseline. No such detector
is supplied. A count of expected relations alone does not establish the needed
success probability. Sol's completed independent review supplies a bound for
the precise iid sampling rule below; it does not supply the detector.

For a fixed pair, possible third abscissae are those of H1+H2 and H1−H2,
with exceptional cases handled. Enumerating all pairs costs Theta(n²), already
q^(2/3) at the proposed scale. This screens THAT implementation; it is not a
lower bound on every implicit detector. Rank at most3 of the expanded
n²-by-n pair/point matrix does not by itself find a zero without materializing
its rows. A new representation may still help design an algorithm, but this
one has not supplied the missing operation.

No automatic novelty or conditional-hardness claim is accepted. An integer
3SUM analogy is not a reduction preserving this field, conic admissibility,
random-list distribution and exponent. The raw report's suggestion to reject
the card merely upon finding a general3SUM result is too broad. Prior-art and
complete-cost review continues before deciding whether a particular detector
deserves an experiment. The completed review found no applicable detector or
hardness reduction in the sources below. Tiny correctness enumeration is unnecessary to decide
these already independently checked polynomial identities.

## Iid hit probability and complete cost

Sol supplied, and root checked, the following refinement. Sample three lists
of n independent uniform full-group points. Count the4n³ signed equations
A_i+epsilon*B_j+eta*C_k=O, epsilon,eta in{−1,1}. Distinct equations have
nonproportional coefficient vectors over Fq (q odd), so their indicators are
pairwise independent. If Z counts witnesses and mu=4n³/q, then
E Z=mu, Var Z<=mu and Cauchy-Schwarz gives

    Pr(Z>0) >= mu/(1+mu).

Rejecting infinity and conditioning all3n points affine lowers this bound by
at most3n/q (use the union bound before conditioning). At n on the scale
q^(1/3), this proves constant witness probability for this sampling rule.
For a single affine triple, the four sign events are mutually exclusive;
each has probability(q−2)/(q−1)², so the exact combined probability is
4(q−2)/(q−1)². Repeated coordinate values do not require independent events;
the full-group second-moment argument is over indexed sample variables.
It does NOT apply automatically to dependent walk-generated lists.

Generate each labelled H as alpha*G+beta*Q with independent uniform
alpha,beta in Fq. Conditional on every generated point, the beta coefficients
remain independent uniform. A witness and signs chosen using coordinates only
therefore have a nonzero aggregate beta with probability1−1/q. Reject and pay
for zero-coefficient witnesses; verify the recovered scalar. Label-dependent
selection or other generation rules require their own proof.

Thus if s is the useful success probability including DETECTOR completeness,
the full expected work for independent batches includes

    C_setup + [3n*(C_labelled_point+C_feature)
               + C_detector + C_recovery_and_verification]/s,

plus all affine rejections and actual memory/workspace. The witness existence
bound cannot be substituted for an unproved fast detector's success rate.
No finite-size setup is declared negligible and no GPU throughput is inferred.

## Primary incidence literature checked

Native Sol actually read the following sources. Root additionally checked
Williams–Yu Theorems1.6–1.7 and Vinh Theorem3 in their primary PDFs.

- [Williams–Yu, Finding orthogonal vectors in discrete structures](https://people.csail.mit.edu/virgi/6.s078/papers/OV-finite.pdf), §3/Lemma3.1,
  §4/Theorems1.6–1.7, §6: the stated finite-field algorithm's characteristic
  dependence is unfavorable at dimension3 and growing p. The explicit
  pair-side input would itself have n² rows. The high-dimensional unrestricted
  hardness result is not a reduction to SP3. The output-sensitive matrix
  algorithm enumerates nonzero entries, not these rare zeros.
- [Chan–Zheng](https://arxiv.org/pdf/2111.03744), §§3.1–3.2: real ordered
  arrangements/cuttings do not establish a finite-field implicit-pair method.
- [Erickson](https://jeffe.cs.illinois.edu/pubs/pdf/hopcroft.pdf), §§1,4:
  real partitioning-model lower bounds do not reject this structured problem.
- [Vinh](https://arxiv.org/pdf/0711.4427), §2/Theorem3: a spectral bound on
  the number of incidences, not an algorithm locating a witness in these lists.

This is a bounded literature check, not proof of novelty or nonexistence. The
next useful step is an explicit executable implicit detector with a cost bound;
none of these sources supplies it. No SP3 experiment or engine is justified yet.

## Other raw dismissals remain unaccepted unless separately justified

The raw table is not a set of proved universal obstructions. In particular,
the fixed-anchor cancellation equation is necessary, not sufficient for every
specified incidence configuration; a trivial fixed-isogeny torsor class does
not make every coordinate feature constant; and a full Fp-subspace requirement
is a restriction of a chosen trace-base construction. Sibling-walk operation
counts and image-bias heuristics are not measured complete-walk costs. Global
EDS equivalences and Prym claims require their precise hypotheses and primary
source checks before use. None changes the baseline in this checkpoint.

Validation: root and independent reviewers checked the displayed mathematics
on paper. `./scripts/check.sh > /tmp/ecdlp-h017-sp3-check.log 2>&1` from
dlp-research exited0, with363 existing dependency audits passing. Those audits
do not formalize these new paper derivations; no Lean/Audit.lean claim changed.
No experiment or throughput measurement was performed.
