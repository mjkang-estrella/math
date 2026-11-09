# W032: compile all integral polynomial annihilators

Parent symbolic derivation, 2026-10-08. **Unreviewed. No experiment.**
Verified complete factoring improvement: **NONE**.

The fixed binomial filter could be the wrong linear functional. A concrete
alternative is to acquire T consecutive lower remainders r_0,...,r_(T-1)
once and compile the entire lattice of integer filters annihilating
polynomials of degree at most 2R. This is a different computation from
randomly trying coefficients or assuming an optimal filter oracle.

Let m=2R+1, T>m, M=N^(2R), with all original arithmetic-progression
points units and the accepted full denominator guard. For integer weights
lambda_j require sum_j lambda_j*j^d=0 for d=0,...,m-1. For an actual
arithmetic progression this suffices to annihilate its scalar polynomial;
therefore gcd(sum lambda_j*d_R(a_j),N) equals gcd(c_lambda,N), where

    c_lambda = sum_j lambda_j*r_j/M in Z.

Use the generating polynomial Lambda(X)=sum_j lambda_j X^j. Vanishing
power moments through degree m-1 is equivalent over Q to a root of
multiplicity at least m at X=1: ordinary powers and falling factorials
span the same rational polynomial space. Therefore

    Lambda(X)=(X-1)^m Q(X),   Q in Z[X], deg Q<T-m.

The integer claim follows from exact division by the monic polynomial
(X-1)^m; it needs no modular factorial inverse or Smith-normal-form oracle.
Conversely every such Q supplies valid weights. Thus the shifted binomial
differences form an integral basis of this particular kernel.

Write c_j=Delta^m r_j/M for j=0,...,T-m-1. The accepted signed integer
convolution computes all these quotients from the one acquired list.
Writing Q(X)=sum_j q_j X^j now gives the exact identity

    c_lambda = sum_j q_j*c_j.

Consequently all obtainable quotient integers form the ideal g*Z with
g=gcd(c_0,...,c_(T-m-1))>=0. The gcd and Bezout coefficients are computed
by ordinary extended Euclid; their construction, widths and storage are
paid. A conservative sequential implementation has polynomial cost in
T,R,logN, even allowing Bezout coefficients O(T*R) bits. This removes
enumeration of all weight vectors for the COMMON-divisibility question.

The resulting concrete consumer first tests gcd(g,N). A proper result is
a valid factor. If N divides g, every filter in this exact kernel has full
gcd, including g=0. If gcd(g,N)=1, no common prime divides all filters;
that does NOT mean individual filters cannot yield a factor.

There is a useful exact distinction in the unit case. Extended Euclid
gives beta_j with sum beta_j*c_j=g. For any public target z modN choose
u=[z*g^-1]_N and set Q=u*sum beta_j X^j. Then c_lambda=u*g=z modN.
Unrestricted integer weights can therefore program every ordinary gcd
argument. Surjectivity alone is not a factoring advantage: choosing an
unknown-factor multiple z remains the original selection problem. A
factor might still come from a restricted short filter or from useful
information in the acquired data. This calculation does not lower-bound
such selectors, nonlinear consumers, or all factoring algorithms.

The decisive next question is now precise: does the cheaply acquired
sequence have a nontrivial common gcd, or a provably useful SHORT-weight
selector beyond this unrestricted programming identity? A gcd of a
translated-difference list tests the first question without an exponential
search. No such test is run here; adding a numerical screen would require
its own frozen protocol. This derivation also prevents promoting the mere
existence of a factor-producing linear combination into a discovery claim.
