# Candidate strengthened scalar and taxicab inequality

Status: complete scalar proof formalized in `formal/StrengthenedScalar.lean`; all 12 local declarations freshly replayed warning-free with Lean 4.34.1 and only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. Parent has independently checked the central algebra. Geometric integration, further independent review, and novelty acceptance are separate gates; no novelty/tally acceptance is claimed.

For nonnegative A,B,C,u,v,w and nonnegative barycentric weights a,b,c summing to1, assume all opposite-side caps u≤min(B,C), v≤min(A,C), w≤min(A,B), and (1−a)u≤aA, (1−b)v≤bB, (1−c)w≤cC. Then the proposed conclusion is

    2(A+B+C) ≥ 3(u+v+w+min(u,v,w)).

The existing geometry bridge establishes exactly these hypotheses for arbitrary normed-plane supporting-line distances, and in particular for the source's explicit L1 distances. Nothing in the proof imposes an orientation condition.

## Positive lengths and the cubic criterion

First let A,B,C>0 and suppose F=u/(A+u)+v/(B+v)+w/(C+w)≤1. Define

    H(A,B,C;u,v,w)=ABC−Avw−Buw−Cuv−2uvw.

Clearing the three positive denominators gives H≥0.

We prove the following threshold lemma: if all the caps hold and

    2(A+B+C)=3(u+v+w+min(u,v,w)),

then H≤0.

Relabel the paired variables so that0≤u≤v≤w. Put y=w−v, a=A−w, b=B−w, c=C−v. These four variables are nonnegative, and the threshold equation is

    2(a+b+c)+y=6u.                                      (1)

View

    h(t)=H(t+y+a,t+y+b,t+c;u,t,t+y)

as a polynomial in t. Its quadratic coefficient is q=b+c−4u≤0. Its derivative at t=u is

    D=u(b+c−8u−4y)+b(y+a)+c(2y+a+b).

The following exact identity, using(1), proves D≤0:

    12D = −31u² −[3(b+c)−8u]² −(3y−u)²
          −12yb −3(b−c)² −18ya.

Consequently, for t≥u,

    h(t)−h(u)=(t−u)[D+q(t−u)]≤0.

Thus it is enough to prove H≤0 after replacing v by u and w by u+y, and reducing each of A,B,C by v−u. The resulting lengths remain capped and obey the corresponding threshold equation.

For equal first two side distances u,u, replace the first two lengths by their mean s. This increases H by C(A−B)²/4≥0. We now have

    w≥u≥0, s≥w, C≥u, 4s+2C=9u+3w,
    H(s,s,C;u,u,w)=(s+u)[C(s−u)−2uw].

It remains to show C(s−u)≤2uw. If3w≤8u, the identity

    32[2uw−C(s−u)] = (4C−5u−3w)² +(w−u)(25u−9w)

has nonnegative right side. If3w≥8u, then5w≥13u; putting d=s−w≥0 gives

    2[2uw−C(s−u)] = (w−3u)²+d(5w−13u)+4d²≥0.

This proves the threshold lemma, including u=0.

## Strict contradiction below the threshold

Suppose S=A+B+C is strictly below T=(3/2)(u+v+w+min(u,v,w)). Increase each of A,B,C by δ=(T−S)/3>0, reaching the threshold without violating any cap. The cubic changes by

    H(A+δ,B+δ,C+δ)−H(A,B,C)
      =δ[(AB−uv)+(AC−uw)+(BC−vw)]+δ²(A+B+C)+δ³.

Each bracketed pair difference is nonnegative by the caps. Thus the new H is strictly positive, contradicting the threshold lemma. This proves the strengthened positive-length scalar inequality.

## Zero lengths and barycentric hypotheses

For any epsilon>0, the weighted inequalities imply u/(A+epsilon+u)≤a and its two cyclic counterparts. Apply the proved positive-length theorem with A+epsilon,B+epsilon,C+epsilon. The result differs from the desired conclusion only by6epsilon on the right. If the desired inequality failed, taking epsilon equal to one twelfth of its positive gap would contradict that conclusion. This proves the full weighted assertion, with zero lengths allowed.

## Exact interior sharpness configuration

In the L1 plane take

    P=(0,0), A=(3,0), B=(0,3), C=(−3/2,−3/2).

The positive barycentric weights are(1/4,1/4,1/2), so P is strictly interior. The three vertex distances are all3 and the opposite supporting-line distances are(1,1,3). Therefore the strengthened inequality is equality:

    2·9 =3·(1+1+3+1).

This is one strengthening, not an additional count for an example. Sharpness of the old three-halves coefficient alone remains prior art.

## Formal endpoints and replay

`StrengthenedTaxicab.scalar_strength` is the fraction-form theorem with positive A,B,C and all six caps. Its proof explicitly handles all six relative orders of u,v,w by simultaneous permutations of paired variables.

`StrengthenedTaxicab.scalar_strength_weighted` is the full theorem stated at the beginning of this note: every scalar and weight is nonnegative, zero lengths are allowed, and there are no ordering assumptions. The finite positive-gap perturbation proves the boundary extension without a numerical limit or computational extrapolation.

Run `python3 audit.py` from this directory for a fresh isolated all-declaration replay. The dated build receipt is retained under `build/fresh-audit-gn1dke6s/receipt.json`; `build/latest-audit.json` records its path. This standalone scalar module imports only Mathlib. The exact source geometry is integrated separately by the parent, so this local scalar module alone is not represented as a complete source-question certificate.
