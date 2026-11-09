# Sustained solving: the PLC characterization question

Status: unresolved in full scope; zero nominations. No PROOF.md is supplied. The auxiliary calculations below are elementary classical bridges and receive no discovery credit.

Wang–Yeh, arXiv:math/0504164v7 (27 November 2006), Section 4 asks for a necessary and sufficient condition for a nonnegative triangle a(n,k) to preserve log-concavity under z_n=sum_(k=0)^n a(n,k)x_k, for EVERY nonnegative input sequence with no internal zeros. Output must also have no internal zeros. Their actual Theorem 2.3 proves LC-positivity sufficient, via weight grouping and Abel summation in Lemma 2.1; Remark 1.1 gives necessary truncated-geometric pointwise tests. These two conditions differ. Their source does not assert equivalence. Definitions, Remark 1.1, Lemmas 2.1–2.2 and Theorem 2.3 proof, Theorem 3.10 proof and Section 4 were read. The journal reference is JCTA114(2007)195–210; that separate typeset body was not authenticated.

## Route A: exact ratio elimination, beyond geometric inputs

For each n put U=sum a(n-1,k)x_k, V=sum a(n,k)x_k, W=sum a(n+1,k)x_k. The required inequality is Q=V²-UW>=0. For positive x_0,...,x_n, its coefficient in x_(n+1) is -a(n+1,n+1)U<=0. Consequently its minimum over the last LC constraint is at x_(n+1)=x_n²/x_(n-1) (n>=1). This elimination is universal; it is not a sample-prime/order calculation. Multiplication by the positive denominator x_(n-1) yields an explicit cubic condition in the remaining coordinates. Zero support boundaries must be treated separately; dividing through zero is prohibited.

At n=1 write rows a; (b,c); (d,e,f), all nonnegative. Then Q at the saturated endpoint is

    A*x0²+B*x0*x1+C*x1²,
    A=b²-ad, B=2bc-ae, C=c²-af.

For x0,x1>0 this is nonnegative exactly when A>=0, C>=0 and B+2sqrt(AC)>=0. Necessity follows by taking x1/x0 to zero/infinity and, when B<0, minimizing A/t+B+Ct; sufficiency is AM–GM. Limits cover support endpoints. This is a complete local row criterion, not the full arbitrary-n PLC characterization or a new nomination.

For n=2, denote rows U=a*x0+b*x1, V=c*x0+d*x1+e*x2, W=f*x0+g*x1+h*x2+i*x3. Normalize x0=1, x1=t, x2=t²u, 0<u<=1, t>0. Saturation gives x3=t³u². Thus the universal local problem is exactly nonnegativity of

    (c+dt+e*t²*u)²-(a+bt)(f+gt+h*t²*u+i*t³*u²).

Its coefficient of u² is t³[(e²-bi)t-ai], so no universal monotonicity in the next curvature variable follows from nonnegative array entries. An interior minimizing curvature can occur; blindly saturating all LC constraints is unjustified. For all n, positive inputs have the exact parametrization

    x_j=x0*t^j*product_(h=1)^(j-1) u_h^(j-h), t>0, 0<u_h<=1.

This produces polynomial positivity on a box times a ray, for every support interval. It is a precise algebraic reduction, not a finite explicit structural characterization. A quantifier-elimination restatement would be routine and would not earn credit. The decisive outstanding calculation is a structural description of the negative minima compatible with the special rank-one-difference form V²-UW, including all support intervals and output support.

## Route B: certificates from elementary LC inequalities

Each inequality x_i*x_j>=x_(i-1)*x_(j+1), j>=i, holds for every nonnegative no-internal-zero LC sequence. One can seek Q as a nonnegative sum of these differences and nonnegative monomials, possibly adding ordinary squares. The source Theorem 2.3 implements the first part separately within each weight i+j using nonnegative tail sums. That is a complete sufficient bridge, but it cannot be necessary as a coefficientwise criterion.

Here is an ALL-input, ALL-parameter obstruction to necessity, with its complete bridge. Take rows (1), (1,1), (0,g,0), then all-zero rows. For g>=0, the output is (x0,x0+x1,g*x1,0,...). Its only potentially nontrivial log-concavity inequality is

    (x0+x1)²-g*x0*x1=(x0-x1)²+(4-g)*x0*x1.

This is nonnegative for every input exactly when g<=4; g>4 fails on the valid LC input x0=x1=1 and all later coordinates zero. The output has no internal zeros, by direct inspection of whether x0,x1,g vanish. Thus the ENTIRE triangle is PLC iff 0<=g<=4. In contrast its r=0 LC-positive polynomial at n=1 is 1+(2-g)q+q²; all other tail and row inequalities are immediate. Hence it is LC-positive iff 0<=g<=2. For 2<g<=4 cancellation between different weights is essential. This explicitly exhibits the classical applicable bridge; it does not exclude the source's full characterization from shortness. The source's own pointwise/coefficient distinction anticipates the issue, so this family is not offered as new mathematics.

The next certificate route must allow cross-weight squares. Merely making within-weight tail tests exact, or finding a larger finite collection of successful triangles, will not solve the source problem. For arbitrary n it remains unproved that LC-difference multipliers plus suitable squares give a complete finite certificate at degree two. Standard multi-constraint S-lemma assertions cannot be assumed: the LC input region is not a convex cone in the original coordinates. This is a different obstruction and route from ratio elimination.

## Closed Hankel reconnaissance

Before the PLC investment, the ERR2009 binomial-Hankel family was reduced in two ways. With x=t+2+t^-1 and CT the Laurent constant term,

    binom(2j+r,j)=CT[x^j*((1+t)^r+(1+t^-1)^r)/2].

The monic basis p0=1, p_j=t^j+t^-j for j>0 gives an exactly equal determinant of the integer band matrix B: B00=1; B0j=Bj0=binom(r,j); and Bij=binom(r,|i-j|)+delta_ij+binom(r,i+j) for i,j>0. This follows by expanding products and using unitriangular change of basis, and is checked independently against rational elimination. Alternatively the weight is P_r(x)=x^(r/2)T_r(sqrt(x)/2), leading to a confluent Christoffel determinant with zero multiplicity ceil(r/2) and other roots 4cos²((2j-1)pi/(2r)). We did not finish this second evaluation.

The legitimate targeted search then found Cigler–Tyson1807.08330v2, actual October2018 body. Its equations (9)–(12) prove these endpoints; Sections 6–8 express the matrix through finite tridiagonal polynomial matrices, then handle invertible and corank-one cases using a determinant/adjugate rank-one update. The n-versus-N bridge is N=n+1: ERR's F(n,r)=d_r(n+1). This is the SAME object for every r and n, not a formal resemblance. It completely closes the two endpoint families and the corrected midpoint formulas. ERR's unsigned odd-midpoint formula already fails at r=3,m=0: determinant -4 versus printed +4; the known2018 sign is (-1)^(k(k+1)/2) for r=2k+1. This is a published correction, not a new counterexample. No further investment in that closed target is recommended.

## Limits

Exact finite checks support algebra and code only. No arbitrary-n PLC theorem, surviving source resolution, or novelty certification results. Current arXiv primary searches were made, but complete current public-proof registries were unavailable under inherited access denials. No denied route was retried. Full citing and worldwide history clearance is absent. No manuscript or Lean work was undertaken.
