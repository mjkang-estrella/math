# Gamma-moment existence versus log-ID: already publicly refuted

28 October 2026. **Credit 0; no Lean investment or discovery nomination.**
This is distinct from the still-unresolved convexity question MathDB343458.
That convexity statement is not refuted here.

## A fully explicit independently found witness

For normalized Pochhammer Gamma quotients choose positive parameter arrays

    A=(1,4,4,10,10),   C=(2,3,3,11,11).

Their quotient simplifies by the Gamma recurrence to

    M(s)=100(s+3)²/[9(s+1)(s+10)²], s>-1.

It is the Laplace transform of the strictly positive probability density

    ρ(t)=100/729 ·[4e^(-t)+(77−441t)e^(-10t)], t>0.

To see positivity put u=9t. The bracket times e^(10t) is
4e^u+77−49u, whose global minimum is126−49log(49/4)>0.
The last strict inequality follows from log(49/4)<18/7: the degree7 rational
Taylor sum for exp(18/7) already exceeds49/4. Direct integration gives total
mass1 and Laplace transform M. Thus X=exp(-T) is a genuine variable in(0,1)
with the displayed Gamma-type Mellin transform on the entire strip s>-1.

Nevertheless −(log M)'=1/(s+1)+2/(s+10)−2/(s+3) is not completely monotone.
At s=157, its signed34th derivative divided by34! is

    1/158^35+2/167^35−2/160^35 <0,

verified by exact integer arithmetic. Equivalently the35th logarithmic
complete-monotonicity inequality fails. The corresponding rational spectral
sum e^(-t)+2e^(-10t)−2e^(-3t) equals−90348/9765625 when e^(-t)=4/5.
The standard Gamma log-ID criterion therefore also fails. The parameter
arrays have equal cardinality and sumA29<sumC30, so this is not a point-mass,
complex-parameter or boundary loophole. Everything is exact in check_exact.py.

## Why this cannot receive discovery credit

Kadankova–Simon–Wang1908.03428v2 section1.2, equations(5)–(6), asks whether
existence of a positive Gamma-type moment variable forces its logarithm to be
infinitely divisible. I read that actual primary body. But a subsequent
primary source by a co-author already answers negatively: Min Wang,
2410.19330v1, section2.2, equation(2.9), cites Dufresne's example.

The actual published Dufresne2010 paper, *G distributions and the beta-gamma
algebra*, Electronic Journal of Probability15,2163–2199, was obtained from
the official EMIS/TCD mirror. Its **Comments and examples, item2, p2195**
constructs a legitimate G(3,3) law with parameters a=(1,2,3) and positive
real b≈(1.0120,1.8659,3.8871), and explicitly proves log G is not infinitely
divisible. Those positive b are the negatives of the roots of

    200p³+1353p²+2615p+1468.

Exact Sturm counts put its three roots respectively in(-4,-3),(-2,-3/2),
and(-11/10,-1); hence all original b parameters are positive and real.
This is precisely inside the purported open question's positive-parameter,
equal-cardinality scope. It is not merely a counterexample in the paper's
larger complex-parameter class. Dufresne's item2 uses paired convolutions of
signed auxiliary measures; one must not mistake their auxiliary rational
factor for the final Gamma Mellin transform.

The independently found integer-parameter witness above is a simpler
instance of an already public negative proposition. The campaign excludes
such refinements/rediscoveries. No full formalization, new manuscript, packet
or credit is warranted, and no public problem record is changed. The broader
convexity conjecture343458 stays open and separate.

## Evidence and limits

The source and follow-up actual HTML bodies were read. Dufresne's published
p2195 was read in the PDF text and rendered for visual checking. Sources,
hashes, exact algebra/sign checks and the real-root isolation are retained.
This is a positive prior-art exclusion, not an inference from failed searches.
No exhaustive literature/priority claim is made. Accepted count stays
2/30 additional and32/60 total; no external communication or posting.
