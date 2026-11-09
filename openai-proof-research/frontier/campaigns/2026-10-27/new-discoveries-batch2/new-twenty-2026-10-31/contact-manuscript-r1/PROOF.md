# Ordinary proof - MathDB 365301

DRAFT; AI-assisted; zero accepted credit.

## 1. Source conventions and the statement

Let G be a finite simple undirected graph with adjacency matrix A. Colour each vertex z or w, let Y be the diagonal indicator of the z vertices, and choose a root i. The source representation is

    M(z,w) = A - zY - w(I-Y),      f(z,w) = (M(z,w)^(-1))_(i,i).

It is the diagonal entry of the inverse, not its reciprocal. On the bi-upper half-plane, M is invertible: if Mv=0 with v nonzero, the imaginary part of v*Mv is strictly negative. With D=diag(Im z or Im w), the inverse identity is

    Im(M^(-1)) = (M^(-1))* D M^(-1).

Thus Im f is positive. Real coefficients give real values on the real boundary wherever the quotient is defined. The Cayley map beta(v)=(1+iv)/(1-iv), with inverse i(1-v)/(1+v), gives a rational inner function

    phi(Z,W) = beta(f(beta^(-1)(Z), beta^(-1)(W))).

The boundary point (infinity,0) becomes (-1,1). All contact orders below are local there. The source's Section 4, Theorem 4.6 proves contact order 2d when there is exactly one w vertex and its minimum path distance from the root is d. Conjecture 6.1 extends this assertion to multiple w vertices. The adjacent paragraph additionally predicts equal contact orders on all branches. Our example has two w vertices; it violates both expectations without contradicting Theorem 4.6.

For a reduced expression phi=q/p with p stable and q a unimodular multiple of its reflection, contact K means that the infimum of 1-|W| over nearby zeros q(Z,W)=0 in the face |Z|=1, |W|<1 is comparable to |Z+1|^K. Existence of a nearby zero is part of this comparison. Section 3.1 and Remark 3.2 of [2] retain the maximum branch convention in the ELA 2026 journal version: generic matched level curves yield the maximum of their vanishing orders. It is neither the minimum nor their sum.

## 2. The graph and the reduced resolvent

Use vertices 0,1,2,3,4, root 0, and the following data:

    E = {01,02,03,13,24,34},    z vertices = {0,3,4},    w vertices = {1,2}.

The root has w neighbours 1 and 2. A path of length zero cannot reach a w vertex since the root is z. Consequently its nearest-w distance is exactly 1. The graph is connected: 1,2,3 are adjacent to 0, and 4 is adjacent to 2 (also to 3). In the indicated order its matrix is

    M = [ -z   1   1   1   0 ]
        [  1  -w   0   1   0 ]
        [  1   0  -w   0   1 ]
        [  1   1   0  -z   1 ]
        [  0   0   1   1  -z ].

Expanding the determinant and the (0,0) cofactor gives f=N/Q, with

    N = (wz-w-1)(wz+w-1),
    Q = -w^2 z^3 + 2w^2 z + 4wz^2 + 2wz - w - 3z.

This is an identity of rational functions; the pointwise matrix-inverse identity is used where Q is nonzero. In the bi-upper half-plane that condition follows from the strict imaginary-part argument. The determinant and cofactor are independently recoverable from the displayed matrix, so this quotient is tied to the actual graph.

We verify reduction over C[z,w], not merely over the rational numbers. Each factor w(z-1)-1 and w(z+1)-1 is primitive as a polynomial in w over C[z]. It is linear and irreducible over C(z), hence irreducible by Gauss's lemma. They are nonassociate: their coefficients of w differ while their constant coefficients agree. Neither divides Q, since substitution yields

    Q(z,1/(z-1)) = (2z-1)^2/(z-1)^2,
    Q(z,1/(z+1)) = -1/(z+1)^2.

Both are nonzero rational functions. There are no z-only factors of N because its factors are primitive. Every common divisor of N and Q is therefore a unit. The formal proof obtains irreducibility using a polynomial equivalence and checks nondivisibility already at (z,w)=(0,-1) and (0,1). It concludes a common-divisor statement in the original bivariate complex polynomial ring.

The two distinct w factors matter: this is genuinely a degree-two representation in w after reduction. Removing a cancelled factor cannot turn it into the one-w case. Likewise, the distance calculation refers to the original graph, rather than an auxiliary quotient graph or an effective coupling parameter.

## 3. Analytic level curves and exact differences

For a finite nonzero real level L set t=1/z and w=tu. The cleared equation f=L is

    F(t,u,L) = a_L(t)u^2 + b_L(t)u + c_L(t) = 0,
    a_L = L(1-2t^2)+t-t^3,
    b_L = -4L-2Lt+Lt^2-2t,       c_L = 3L+t.

Indeed F=t(N-LQ) after substitution. At t=0 it equals L(u-1)(u-3), with simple roots 1 and 3. The discriminant has value 4L^2, so a local analytic square root with initial value 2L exists. The quadratic formula gives two convergent analytic branches, uniquely labelled by their slopes. The leading coefficient is nonzero near zero, so these are all roots; in particular all w roots are O(t).

The identity N-LQ=0 away from t=0 is equivalent to f=L on these branches. If Q vanished there then N would vanish as well. The displayed substitutions in Section 2 show that common zeros cannot accumulate at z=infinity. Thus no level branch here is a spurious common-zero component.

The branches have expansions

    w_(L,1)(t) = t-t^2+t^3-t^4/2-t^5
                 +(17/4-1/(2L))t^6+O(t^7),
    w_(L,3)(t) = 3t+(3-2/L)t^2+O(t^3).

These are convergent analytic expansions. For an explicit coefficient check for the longer jet, put

    p_L(t) = 1-t+t^2-t^3/2-t^4+(17/4-1/(2L))t^5.

Substitution into F gives O(t^6). The identity F(t,u)-F(t,p)=(u-p)[a_L(t)(u+p)+b_L(t)] has bracket -2L at (t,u,p)=(0,1,1). Division by this analytic nonvanishing bracket shows u-p=O(t^6), proving the first expansion. For the slope-three branch, put p=3+(3-2/L)t; its residual is O(t^2) and the bracket has value 2L. This proves the second expansion without treating formal jets as analytic existence.

For distinct finite nonzero real L,H, subtraction gives

    w_(L,1)-w_(H,1) = (1/(2H)-1/(2L))t^6+O(t^7),
    w_(L,3)-w_(H,3) = (2/H-2/L)t^2+O(t^3).

The coefficients are nonzero; the orders are exactly 6 and 2. Cross-matching slopes gives order 1 and is not the local branch matching. The calculation works for every nonzero real level, not only positive levels. Consequently it is compatible with the generic-level convention of [2, Remark 3.2] and [3, Theorem 3.1]. The maximum order is 6. We next prove this conclusion directly from the zero-set definition, independently of the generic-level theorem.

## 4. A direct zero-set proof of contact six

For domain assertions use x=-1/z, which preserves the upper half-plane; t=1/z alone reverses it. Clearing the denominator of beta(f(-1/x,w)) gives

    R(x,w) = x^3[Q(-1/x,w)-iN(-1/x,w)]
      = (1-ix-2x^2+ix^3)w^2
        +(4x-(2+2i)x^2-x^3)w+3x^2-ix^3.

Write A(x)=1-ix-2x^2+ix^3, B(x)=4-(2+2i)x-x^2 and C(x)=3-ix. For w=xu the equation is x^2[A(x)u^2+B(x)u+C(x)]=0. At zero the desingularized quadratic has roots -1,-3. Its normalized discriminant (B^2-4AC)/4 has value 1. The analytic inverse function theorem for s -> s^2 at 1 supplies a local analytic square root. The quadratic formula yields exhaustive analytic branches u_1,u_3. No global choice of square-root branch is required.

Here is an analytic remainder proof of their imaginary orders. Put

    P(x) = -1-x-x^2-x^3/2+x^4.

Direct polynomial multiplication gives A P^2+B P+C=x^5 H(x), where H is polynomial with H(0)=-17/2+i. Subtract the branch equation; the divided difference A(u_1+P)+B has value 2. Therefore, on a neighbourhood,

    u_1=P+x^5 g,       g=-H/[A(u_1+P)+B],
    g analytic,        g(0)=17/4-i/2.

Similarly A(-3)^2+B(-3)+C=x H_3(x), with H_3(0)=6-4i. The divided difference A(u_3-3)+B has value -2. Thus u_3=-3+xh with h analytic and h(0)=3-2i. For real x the two pole roots w_j=xu_j satisfy

    Im w_1(x) = x^6 Im g(x) = -x^6/2+O(x^7),
    Im w_3(x) = x^2 Im h(x) = -2x^2+O(x^3).

The nonzero analytic factors give exact real analytic orders 6 and 2. After shrinking the interval, both roots have negative imaginary part. They tend uniformly to zero, and every root is one of them for nonzero sufficiently small x. Continuity gives |Im w_1| between |x|^6/4 and |x|^6, while |Im w_3| is at least |x|^2. Restricting |x|<1, every root has imaginary distance at least |x|^6/4, and the first root witnesses an upper bound |x|^6 in any prescribed small neighbourhood. This proves HasHalfPlaneContact R 6 with a uniform lower bound and an attained upper bound.

There is no common component of R and its coefficientwise conjugate: one would divide the cleared N and Q, while x cannot divide R because R(0,w)=w^2. Thus the local boundary zero is not an artefact of common-factor cancellation.

## 5. Reduction on the bidisk and the Cayley comparison

For clarity the global certificate uses polynomial clearing rather than a merely local quotient. In C[Z,W], set a=i(1-Z), b=1+Z, c=i(1-W), e=1+W and define

    N_c = b(ca-cb-be)(ca+cb-be),
    Q_c = -c^2 a^3+2c^2 ab^2+4ca^2 be
          +2cab^2 e-cb^3 e-3ab^2 e^2,
    q_b = Q_c+iN_c,       p_b = Q_c-iN_c.

Clearing gives N_c=b^3 e^2 N(a/b,c/e) and the analogous identity for Q_c. Hence phi=q_b/p_b in the bidisk. The proof of coprimality factors N_c into b and its two bilinear factors. Each is irreducible; exact evaluations at (1,-i), (1,i) and (-1,0) exclude their divisibility into Q_c. Invertible scalar linear combinations then give reduction of q_b,p_b. Thus reduction is checked after clearing, including its exceptional divisors; it is not inferred solely from rational coordinate substitution.

The support of p_b is bounded by (3,2). With reflection in that bidegree, direct polynomial coefficient computation gives q_b=reflect(p_b), with phase 1. The denominator is stable: beta^(-1) takes the bidisk into the upper half-plane, Q is nonzero there by invertibility of the graph matrix, and Q-iN cannot vanish because Im(N/Q)>0. Indeed Q-iN=0 would imply f=-i. The clearing factors are nonzero in the open bidisk. This gives a reduced rational-inner certificate for the actual graph function. Both q_b and p_b vanish at (-1,1).

For real nonzero x near zero let Z=-beta(x)=beta(-1/x). Coefficientwise conjugation of R converts lower-half-plane pole roots u to upper-half-plane roots conjugate(u), and W=beta(conjugate(u)) gives precisely the nearby numerator zeros. The clearing and quotient identities establish both directions; possible exceptional denominators are ruled out by localization. Every such image eventually lies inside the disk and arbitrarily close to 1.

The transfer uses explicit estimates, not an assertion that contact is conformally invariant. If Im y>0 and |y|<1/2, then

    1-|beta(y)|^2 = 4 Im y / |1-iy|^2,
    Im y/2 <= 1-|beta(y)| <= 16 Im y.

For |Z|=1 near -1 the circle chart x=i(1+Z)/(1-Z) is real and

    |Z+1|/2 <= |x| <= |Z+1|.

Combining the half-plane lower constant 1/4, height lower factor 1/2, and parameter lower factor 1/2 in power six yields 1/512. The upper constant is 16. Localization first places all witnesses in any proposed numerator neighbourhood. Thus HasZeroSetContact q_b (-1) 1 6 holds, with rho=1/2, lower constant 1/512 and upper constant 16 (and some positive delta).

Finally contact 2 is impossible. Its positive quadratic lower bound, applied to the localized sixth-order witness, would imply c|Z+1|^2 <= 16|Z+1|^6 for arbitrarily small positive |Z+1|. Dividing and tending to zero contradicts c>0. The boundary point is therefore a genuine contact-six singularity, and 6 is unequal to twice the nearest-w distance 1.

