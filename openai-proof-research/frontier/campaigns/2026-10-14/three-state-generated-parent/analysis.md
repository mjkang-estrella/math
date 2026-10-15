# Positive-tree obstruction to the unit quadratic saving

Status: technical research evidence, not an accepted frontier result. The
three-state capacity necessity theorem remains unresolved. This note does not
refute a saving with some smaller universal positive coefficient.

Use I319's normalization m(mu)=E|zeta|^2. Let C_t be the posterior experiment
of a single symmetric three-state channel with parameter t, and let star
denote observations independent conditional on the common uniform spin.
Every physical channel used below has parameter strictly between zero and one.

## A closed-form positive-tree counterexample

For a,b in (-1/2,1), direct conditioning on whether the two observed labels
agree gives

    M(a,b) = m(C_a star C_b)
           = (a+b+ab)^2 / [3(1+2ab)]
             + 2(a^2+b^2+a^2 b^2-ab-a^2 b-ab^2) / [3(1-ab)].

Indeed the independent marginal labels agree with probability 1/3 and disagree
with probability 2/3, and the Bayes marginal tilts are respectively 1+2ab and
1-ab. In the agreement case the posterior complex amplitude is
(a+b+ab)/(1+2ab). In a disagreement case it is a rotation of
(a+b omega+ab omega^2)/(1-ab), whose squared numerator is the polynomial above.
This derives the formula without a simulation or numerical fit.

Take mu=C_(1/4) and nu=C_(4/5) star C_(4/5). The two strong labels agree with
actual probability 19/25. Their posterior amplitude then is s=56/57. They
disagree with probability 6/25, giving amplitude w=-4/9. Thus the marginal
posterior law nu is the mixture (19/25) C_s + (6/25) C_w. This is a decomposition
of a genuine positive-channel tree law; the negative w is an emergent posterior
shape, not a negative physical channel. Applying the product formula to this
mixture yields exactly

    m(mu) = 1/16,
    m(nu) = 10016/12825,
    m(mu star nu) = (19/25) M(1/4,56/57) + (6/25) M(1/4,-4/9)
                  = 1627919/2046800.

Consequently

    m(mu star nu) - [m(mu)+m(nu)-m(mu)m(nu)] = 119807/175001400 > 0.

The combined experiment is simply the three-leaf star with edge parameters
1/4,4/5,4/5. It belongs to the smallest class containing revealing experiments
and closed under positive channel operations and finite conditional products.
Hence that class does not satisfy I319's desired inequality with c=1.
Subadditivity itself is not contradicted by this example.

## Necessary upper bound on any universal coefficient

For any fixed symmetric posterior law nu, write b=E|v|^2, h=E Re(v^3),
k4=E|v|^4. The exact I319 mixed identity, applied to C_a and nu, gives

    lim_(a -> 0+) [a^2+b-m(C_a star nu)]/(a^2 b)
        = 1 + 2(h-k4)/b,                         (b>0).

To justify the remainder limit directly, use u=a omega^j in I319's formula.
Its denominator 1+u conjugate(v)+conjugate(u) v is uniformly bounded below
by 1-2a, while |v|<=1. Divide the nonnegative remainder by a^2 and apply
bounded convergence. Averaging the squared linear term over the three roots
of unity gives 2|v|^2; the remaining numerator tends to |v|^2. Thus the limit
of the remainder divided by a^2 is 2 k4. The term h(C_a)=a^3 disappears at
that scale, proving the display.

For the positive two-leaf law nu above,

    h = (19/25)(56/57)^3 + (6/25)(-4/9)^3,
    k4 = (19/25)(56/57)^4 + (6/25)(4/9)^4,
    1 + 2(h-k4)/b = 8735449/9152433 < 1.

Therefore any universal coefficient c for the whole positive-tree-generated
class must satisfy c <= 8735449/9152433. This is only an upper bound on an
unknown permissible coefficient; it supplies no positive lower bound.

## Validation, provenance and limits

check.py enumerates 18 explicitly specified positive finite-tree laws and
171 pairs in exact rational arithmetic. Every generated law is checked for
normalization, nonnegative mass, balance and permutation symmetry. The
marginal-tilt information evaluator is independent of output-atom grouping.
A negative-channel exclusion control correctly violates subadditivity, and
equal-channel products match I319's closed form. Six pairings violate c=1;
none of the selected pairs refutes every positive c. Finite agreement cannot
prove a universal inequality. The selected 1/4 versus two 4/5 channels above
was additionally checked using the separate closed form, matching the direct
enumeration exactly. checks.json retains all finite outcomes, not only successes.

Read I319 analysis and reading/failures, I326's two moment obstructions, and
actual pinned three-state foundations through the exact posterior product
formula fnd:product. The immutable upstream revision is
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The present counterexample uses only
Bayes' rule and finite rational calculations. No literature priority claim,
independent proof gate, capacity necessity result or publication is proposed.
The next full attempt still needs a product-preserved class and some c>0,
or a different potential that proves the original arbitrary-tree criterion.
