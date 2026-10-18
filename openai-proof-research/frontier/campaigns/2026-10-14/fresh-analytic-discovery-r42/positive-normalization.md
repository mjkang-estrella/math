# Positive measures admit an explicit 3-Lipschitz probability normalization

Myeongjin Kang, no affiliation. Original prose CC BY 4.0. Author-side technical lemma within the unchanged T332 continuation, not a separate target, nomination, or priority claim.

## Statement and conventions

Let (V,d,o) be any finite pointed metric space. Identify a positive measure mu on V without o with the root-balanced signed measure mu-mu(V) delta_o. Its ambient norm is

    ||sigma||_KR = sup { |sum_x f(x) sigma(x)| : f(o)=0, Lip(f)<=1 }.

Equivalently one may integrate just against the off-root coefficients. This is a genuine norm on their finite-dimensional vector space. In particular, for mu>=0 its norm is sum_x h(x)mu(x), where h(x)=d(o,x). Measures of off-root mass<=1 correspond isometrically to probabilities after filling the deficit at o. The metric between such probabilities is W1 by finite transport duality.

There is a 3-Lipschitz retraction from the positive off-root measure cone onto the off-root subprobabilities. Consequently, on a finite rooted tree, the root mass budget can be imposed at a universal cost once nonnegative vertex masses have been obtained. The lemma does NOT produce positivity from an arbitrary signed measure or arbitrary edge vector.

## Construction

Put m_c(x)=min(1,c h(x)) for 0<c<infinity, and m_infinity(x)=1 for x!=o. If mu(V)<=1, set c_mu=infinity. Otherwise choose c_mu>0 such that

    sum_x m_(c_mu)(x) mu(x)=1.

Existence and uniqueness follow from continuity, strict increase until all positive atoms saturate, value0 at c=0, and limiting value mu(V)>1. Set R(mu)=m_(c_mu) mu, interpreted as a probability by adding the missing root mass. This fixes all off-root subprobabilities. The degenerate space V={o} is immediate.

## Fixed-parameter bound

For finite c, the multiplier L_c:mu -> m_c mu has KR operator norm at most2. To see this, fix f(o)=0 with Lip(f)<=1 and define g(x)=m_c(x)f(x), g(o)=0. If h(x)>=h(y), then

    |g(x)-g(y)|
      <= m_c(x)|f(x)-f(y)| + [m_c(x)-m_c(y)]|f(y)|
      <= d(x,y) + c|h(x)-h(y)|h(y)
      <= 2d(x,y)

whenever m_c(x)>m_c(y), since then c h(y)<1. If the two multipliers agree the second term is zero. Thus Lip(g)<=2, and duality proves ||L_c(mu-nu)||_KR<=2||mu-nu||_KR. L_infinity is the identity, with norm1. Also m_c itself is c-Lipschitz and vanishes at the root.

## Changing the parameter

By symmetry assume c_mu<=c_nu. If both are infinite, R is the identity on this pair. Otherwise c:=c_mu is finite, and L_c(mu) has mass1. The positive measure

    Delta=R(nu)-L_c(nu)

is supported on h<1/c: at heights>=1/c both multipliers already equal1. Therefore

    ||Delta||_KR = sum_x h(x) Delta(x)
       <= Delta(V)/c
       <= [1-L_c(nu)(V)]/c
       = [sum_x m_c(x)(mu-nu)(x)]/c
       <= ||mu-nu||_KR.

The second inequality uses only R(nu)(V)<=1, so it includes c_nu=infinity and nu(V)<1. The quantity before the last equality is nonnegative because L_c(nu)<=R(nu). The final bound uses the anchored c-Lipschitz test m_c. Hence

    ||R(mu)-R(nu)||_KR
      <= ||L_c(mu)-L_c(nu)||_KR + ||Delta||_KR
      <= 3||mu-nu||_KR.

This proves the claim with no tree, dimension, aspect-ratio, or cardinality assumption.

## Exact use and unpaid part for T332

For a finite rooted tree the positive off-root cone consists of edge flows q satisfying q_v>=sum_(u child of v)q_u and q_v>=0 at leaves, with NO root budget. Thus a universal Lipschitz retraction from the full weighted edge ell1 space onto this cone, if proved, would compose with R and the pinned source's ell1 cotype witnesses to prove uniform finite cotype. Likewise a uniform cotype estimate directly in the cone would pass through R to probabilities.

No such positivity retraction or cone cotype bound is proved here. The cone is not the coordinatewise nonnegative orthant: nonnegative edge values can have negative divergence at a branching vertex. Coordinatewise positive part in edge coordinates does not fix that, while positive part in vertex-mass coordinates is not KR-Lipschitz. For example, delta_x-delta_y has KR norm d(x,y), but its positive part has root-balanced norm h(x); points x,y can be arbitrarily close far from the root. This example excludes only that elementary operation.

The normalization proof was derived in this round. A focused web search returned ordinary free-space/retraction literature but no operative theorem used in the argument. No new-to-literature assertion is made. The original T332 theorem remains unresolved.
