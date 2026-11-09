# A full counterexample to the maximality clause of Nikolov–Savov Conjecture3.7

Primary sources: https://arxiv.org/pdf/2307.00545v1 (2 July2023) pp2–4,6–7 and https://arxiv.org/pdf/2307.00545v2 (1 May2024) pp2–5,6–7. Both actual bodies, including Proposition3.8's closest k=3 proof, were inspected. This is an ordinary-mathematics refutation, held pending independent review and bounded prior-art/eligibility investigation. No novelty or discovery credit is asserted.

## Exact object and endpoint

For k>=3 the source uses probabilities p1,...,pk>=0 summing to1, iid positive integer increments, u0=1 and u_n=sum(j=1..min(n,k))p_j*u_(n-j). It defines m_k=min(n>=1)u_n, Q_k=product(j=1..k-1)(p1+...+pj), and A_k={real polynomials in p1,...,p_(k-1), total degree<=k-1, bounded above by m_k on the whole simplex}. Conjecture3.7 asserts Q_k is maximal in A_k for every k>=3, and a largest-element assertion in a smaller subclass. Maximality means P in A_k and P>=Q_k everywhere imply P=Q_k. A single polynomial dominating Q4 strictly somewhere, but bounded by every renewal mass for every probability vector, disproves this universal statement. It is not enough to improve at one probability vector.

Put x=p1,y=p2,z=p3,w=p4=1-x-y-z, t=x+y+z. Thus x,y,z,w>=0 and t<=1. Define

    Q=x(x+y)t,
    P=x²t+xy=Q+xyw.

P is a real polynomial in x,y,z of total degree3. P>=Q on the entire simplex. At x=y=z=w=1/4, Q=3/32=6/64 whereas P=7/64. Thus P is not Q.

## Route I: direct inequalities and an independent all-time argument

The recurrence gives u1=x, u2=x²+y, u3=x³+2xy+z. The exact differences are

    u1-P=x(1-y-xt),
    u2-P=x²w+y(1-x),
    u3-P=xy(1-x)+z(1-x²).

For the first, xt<=x, so 1-y-xt>=1-y-x>=0. The other two differences are visibly nonnegative since0<=x<=1. Hence0<=P<=u1,u2,u3 and P<=1. The fourth mass is

    u4=w*u0+x*u3+y*u2+z*u1 >= w+(1-w)P >= P.

For n>=5 all four indices n-j are positive and smaller than n, so induction gives u_n>=sum(j=1..4)p_j P=P. This proves P<=u_n for EVERY n>=1 and EVERY point of the simplex, including all boundary points and periodic/degenerate increment laws. In particular it is a valid polynomial minorant even if one defines m by infimum instead of a possibly unachieved minimum. No reliance on the source's printed maximum/minimum typo in(3.1), strictness claims, Blackwell limit, or finite-support reduction is needed.

Consequently P belongs to A4, P>=Q4 throughout the simplex, and P!=Q4. Q4 is not maximal. The universal maximality clause, and therefore literal Conjecture3.7 as a conjunction, is false.

## Route II: barycentric positive-coefficient certificate

Set s=x+y+z+w and work homogeneously at s=1. Homogenize P to degree3 as Ph=x²(x+y+z)+xy*s. Homogenize u1,u2,u3 as x*s², x²*s+y*s², x³+2xy*s+z*s². Their differences from Ph expand to:

    w²x+2wx²+wxy+2wxz+x²z+xyz+xz²;
    w²y+wx²+wxy+2wy²+2wyz+xy²+xyz+y³+2y²z+yz²;
    w²z+wxy+2wxz+2wyz+2wz²+xy²+3xyz+2xz²+y²z+2yz²+z³.

Every coefficient is nonnegative. This separately certifies all initial minorant inequalities on the nonnegative orthant at s=1, without the direct inequalities in Route I. Iterating the positive recurrence then certifies every later mass. Equivalently, the augmented state vector (u_n,u_(n-1),u_(n-2),u_(n-3)) stays in the order interval[P,1]^4 once n=4; its update is a stochastic companion matrix, preserving this interval. The initialization is explicitly certified above.

diagnostics.py checks all symbolic identities over exact rational polynomials, their nonnegative coefficients and1,771 rational simplex points of denominator20. Only the universal symbolic certificates and recurrence induction constitute proof. The grid is a debugging diagnostic.

## Smaller subclass and source fidelity

In cumulative coordinates X=x, Y=x+y, Z=x+y+z, this P becomes

    Phat(X,Y,Z)=XY+X²(Z-1).

Literal v2(2.9) imposes degrees after setting trailing cumulative variables to1: Phat(X,1,1)=X has degree1; Phat(X,Y,1)=XY has degree2; full Phat has degree3. Thus P also refutes the largest-element clause under that displayed v2 definition. However, v1 adds a prose monomial-prefix-degree description after(2.9); read as separate termwise restrictions, it excludes X²Z despite cancellation at Z=1. The v2 removes that prose. Its printed substitution also has an index mismatch. We do NOT rely on this ambiguity for the primary claim. The maximality refutation in A4 is unaffected by every one of these subclass issues and is not a wording/domain correction. No conclusion about largestness under a stronger intended termwise subclass is claimed.

## Scope and credit objections

This answers the literal universal maximality question negatively; it does not classify optimal minorants, prove largestness/nonlargestness in every k, or assert novelty of the polynomial construction. There are no unresolved mathematical quantifiers in the A4 counterexample. Independent review, current full registry coverage, journal-version comparison, citation-network coverage and the substantive-versus-routine credit decision remain unresolved. These are real gates, not an acceptance recommendation disguised as a proof.
