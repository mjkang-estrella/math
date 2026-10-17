# Exact comparison with the Hughston–Salamon non-SIC examples

This is an independent prior-codebook comparison, not a replacement proof of B8C. The primary is Hughston–Salamon, *Surveying points in the complex projective plane*, arXiv:1410.5862v2, especially §6 and Example 10.2. The authenticated r1 copies remain private inputs; no third-party text is republished here.

Write alpha(C)=min_[u] max_[s] |<s,u>|² for unit representatives. A single unit u whose nine scores are at most 1/2 disproves the sufficient covering property for that particular C. This says nothing about alternative partitions of CP².

## Example 6.4: the three-basis WH orbit

The paper constructs a nine-point WH orbit of an eigenvector of M in (6.13). Twenty-seven pairs have squared overlap 1/3, and nine pairs are orthogonal. The resulting points are three orthonormal bases, pairwise mutually unbiased. These are not twenty-seven SIC-overlap pairs: the nonzero overlap here is 1/3, whereas Example 10.2 uses 1/4.

Here is an exact exclusion that does not assume an arbitrary MUB triple extends to a fourth basis. Let C be a qutrit WH orbit and suppose two distinct orbit rays are orthogonal. Conjugating their displacement gives <f,Df>=0 for a nonidentity WH displacement D. Its eigenvalues, after a common phase change, are 1,omega,omega², all simple. If p_j are the squared moduli of f in this eigenbasis, then sum p_j=1 and sum p_j omega^j=0 imply p_0=p_1=p_2=1/3. For every WH displacement g, g*Dg is a scalar multiple of D, so <gf,Dgf>=0 and the same conclusion holds for gf. Every D-eigenvector therefore has score 1/3 against every ray in C. Thus alpha(C)≤1/3. In fact WH tightness gives equality, but that extra observation is unnecessary. This excludes every Example 6.4 orbit with the stated orthogonal pairs.

## Example 10.2: an explicit quartic configuration

Use (6.3), with real x=tan(phi) and c=1/sqrt(1+x²):

    z(sigma,x) = c (sqrt(2/3)e^{i sigma}, -1/sqrt(6)-x/sqrt(2),
                                               -1/sqrt(6)+x/sqrt(2)).

The two fixed rays are z1=(0,1,-omega)/sqrt(2) and z2=(0,1,-omega²)/sqrt(2). The four ordered roots t=x3<x4<x5<x6 satisfy

    P(x)=27x⁴-66x²+8 sqrt(26-2 sqrt(97)) x+3=0.

The remaining seven rays are z(0,t) and z(±sigma_j,x_j), j=4,5,6. By the prescribed squared overlap 1/4 with z(0,t),

    cos(sigma_j) = [9(1+t²)(1+x_j²)-16-4(1+3t x_j)²]
                                          / [16(1+3t x_j)].

Take u=(1,0,1)/sqrt(2). Its scores against the fixed two rays are 1/4. For any other ray the score is

    F(x,c_sigma) = [4+(sqrt(3)x-1)²+4(sqrt(3)x-1)c_sigma]
                                                    / [12(1+x²)],

with c_sigma=1 for x=t. It is independent of the sign of sigma.

The following rational intervals each contain exactly one root:

    t  in [-1.687100,-1.687097],
    x4 in [-.109890,-.109887],
    x5 in [ .442461, .442464],
    x6 in [1.354524,1.354527].

Their endpoints are rational numbers, not floating-point certificates. Squaring verifies

    9.8488578 < sqrt(97) < 9.8488579,
    2.5104350 < sqrt(26-2 sqrt(97)) < 2.5104352,
    1.7320508 < sqrt(3) < 1.7320509.

Interval substitution makes P have opposite signs at the endpoints of each interval. Four disjoint sign-changing intervals exhaust a degree-four polynomial's roots. Rational interval substitution into the displayed F and cosine formulas, whose denominator intervals avoid zero, gives every score strictly less than 7/20. The original standard-library script example_10_2_bounds.py implements exactly these operations with Fraction; example_10_2_bounds.json records the exact rational bounds. There is no numerical minimization in this certificate. Therefore the explicitly instantiated Example 10.2 satisfies alpha(C)<7/20<1/2.

The printed (7.1) adds omega² to the last coordinate of the (6.3) parametrization. Under that literal convention rotate the last coordinate of u by omega² as well. The seven scores stay identical, and the scores against the two fixed rays remain 1/4 because u's middle coordinate is zero. The exclusion therefore holds under either printed coordinate convention; no correction to the source is assumed.

A preliminary NumPy/SciPy probe located a much stronger witness and then suggested this simple ray. Its retained exploratory script is not proof evidence; it is clearly distinguished from the exact Fraction calculation. The exact proof needs no estimate of the global minimum and no claim that this u is optimal.

## Scope of the exclusion

The paper's general case-(iv) polynomial family was not globally optimized over all its parameters. The paper uses it to eliminate spurious SIC solutions, and the inspected statements do not assert a uniform covering radius. No theorem instantiates alpha>1/2 there. The explicit examples raised for this review are now ruled out, and the whole Example 6.4 class is ruled out by its orthogonal pairs. I do not promote a remaining unoptimized parameter space into evidence either for or against priority.

Nor is the B8C orbit a disguised point in the displayed twenty-seven-SIC-pair family. For positive epsilon its nine within-group pair scores are 1-3pq>1/4 and its twenty-seven cross-group scores are pq<1/4, where pq=1/4-epsilon²/[2(1+epsilon²)²]. It has no pair with squared overlap exactly 1/4. Unitary conjugacy preserves this multiset. A specific previously established cover in another configuration could still supply the Borsuk upper half, but no such result is supplied by these primary bodies.
