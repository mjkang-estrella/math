# Exact constrained cotype optimization and its remaining estimate

Myeongjin Kang, no affiliation. Original prose CC BY 4.0. Author-side working derivation for the unchanged full T332 target. This is an exact finite-dimensional reformulation and technical reduction, not a proof of the desired uniform estimate.

## Primal problem

Fix a finite rooted tree with positive edge lengths w_e. Let P be its probability-flow polytope, namely the convex hull of the root-path incidence vectors chi_v, including chi_o=0. Put N(x)=sum_e w_e|x_e| and N*(u)=max_e |u_e|/w_e. Rooted cut flows identify P isometrically with vertex probabilities in W1.

Let A be a finite reversible stochastic matrix, pi its stationary law, t a positive integer, and p_i in P the inputs. States with pi_i=0 can be removed: reversibility prevents transitions from positive-pi states to them. Hence assume pi_i>0. Write c_ij=pi_i a_ij=c_ji. The exact constrained objective is

    J(q)=sum_i pi_i N(q_i-p_i)^2
          +2t sum_(i<j) c_ij N(q_i-q_j)^2,       q_i in P.       (1)

Diagonal terms vanish. The desired finite assertion is a uniform C such that

    min J <= C^2 E_t(p),
    E_t(p)=sum_ij pi_i [(1/t)sum_(s=1)^t A^s]_ij N(p_i-p_j)^2. (2)

All trees, edge lengths, n, A, pi, t and input probabilities are quantified. No aspect-ratio or support restriction is introduced.

The parent vertex-rounding lemma, read in full in this round, proves that (1) has exactly the same infimum as the optimization over arbitrary probability witnesses on the geometric tree or a larger complete tree. Affine endpoint interpolation fixes input vertex laws and contracts W1. Thus requiring vertex witnesses here does not artificially strengthen the fixed-input problem.

## KKT support condition

Compactness gives a minimizer q. Put D_i=N(q_i-p_i), D_ij=N(q_i-q_j). Standard finite-dimensional convex subdifferential calculus gives signs

    s_i,e in sign(q_i,e-p_i,e),
    r_ij,e in sign(q_i,e-q_j,e),   r_ji,e=-r_ij,e,

where sign(0)=[-1,1], such that the first-order optimality functional for state i, after division by 2pi_i, is

    U_i(e)=w_e[D_i s_i,e +2t sum_j a_ij D_ij r_ij,e].          (3)

This follows directly from partial N(x)^2=2N(x) partial N(x); at x=0 the derivative is zero. The finite sum rule applies because all norm-square terms are continuous everywhere, and the polytope is closed convex. The condition is

    <U_i,v-q_i> >=0 for every v in P.                        (4)

Define the rooted potential V_i(v)=sum_(e in [o,v]) U_i(e), with V_i(o)=0. Since P is the convex hull of the chi_v, (4) is equivalent to: the output probability mu_(q_i) is supported entirely on vertices minimizing V_i. More explicitly, if m_i=min_v V_i(v), then

    V_i(v)>=m_i for every v,
    mu_(q_i)(v)>0 implies V_i(v)=m_i.                        (5)

There is no claim that the minimizer set is connected or a single subtree; a rooted potential can have separated minima. Assuming such a property would discard admissible dual data.

## Exact dual formula

Use dual vectors u_i and b_ij=-b_ji (one b per unordered positive-weight query edge). For each i let

    W_i(v)=sum_(e in [o,v]) [u_i(e)+2t sum_j a_ij b_ij(e)].

Then the exact minimum in (1) equals the supremum of

    2 sum_i pi_i [min_v W_i(v)-<u_i,p_i>]
       -sum_i pi_i N*(u_i)^2
       -2t sum_(i<j) c_ij N*(b_ij)^2.                       (6)

For weak duality use, term by term,

    N(x)^2 >=2<u,x>-N*(u)^2,

sum, and minimize the resulting linear expression over P. For equality choose at a primal minimizer u_i(e)=w_e D_i s_i,e and b_ij(e)=w_e D_ij r_ij,e from (3). Every norm-square inequality is then equality, and (5) makes the polytope minimization equality. This also proves dual attainment without importing a separate strong-duality theorem.

Thus an actual proof by this route must bound (6) by C^2 E_t(p) uniformly. The extra minimum-potential term is precisely the constraint contribution. Replacing the polytope minimum by the minimum over the entire edge space would impose u_i+2t sum_j a_ij b_ij=0. That restricts the dual feasible set and gives only the ambient optimum, a lower bound on the constrained optimum. It cannot establish the required upper bound. Simply dropping the nonpositive minimum term is a different relaxation and has not yielded a useful bound.

## The elementary test is insufficient

The feasible trial q_i=p_i gives only

    min J <= t sum_ij pi_i a_ij N(p_i-p_j)^2.                (7)

This does not imply (2): even for two states deterministically alternating, distinct input distance d gives the bound t d^2, while E_t is asymptotic to d^2/2. The example shows only that estimate (7) loses a factor of order t; its true constrained minimum is uniformly bounded, for instance by taking both outputs equal to one input. It is not an obstruction to cotype.

Testing (4) against p_i, or using generic convexity/resolvent averages, has so far recovered only such paid one-step estimates. No argument has converted the joint support conditions (5) into a uniform Cesaro bound. An argument that worked for every convex subset of ell1 from convexity alone would contradict the distinction explicitly recorded in the pinned source between ambient ell1 witnesses and constrained subspaces.

## Homogeneous positive-cone reduction

Let K be the positive vertex-measure cone in edge coordinates:

    K=cone{chi_v:v!=o}.

Equivalently, every nonroot vertex has q_v>=sum_(u child of v)q_u; leaves have q_v>=0. There is no root mass budget. The separate positive-normalization.md proves a 3-Lipschitz retraction R:K->P, fixing P.

It follows that uniform metric Markov cotype on K implies uniform cotype on P with at most a factor3 in the constant: apply cone witnesses to probability inputs and then R. Conversely, uniform cotype on P implies the same constant on K. For finitely many cone inputs, divide them by M=max_i(total off-root mass of the i-th measure). If M=0 all inputs vanish. Otherwise these normalized inputs lie in P; scale the resulting probability witnesses by M to obtain cone witnesses. Both sides of cotype scale quadratically. This is an equivalence of finite uniform problems up to the explicit factor3, not an additional assumption or a new narrowed target.

For cone inputs replace P by K in (1). A minimizer still exists because all pi_i>0 and the fidelity terms make the objective coercive in every q_i. The dual (6) becomes the particularly simple expression

    -2 sum_i pi_i <u_i,p_i>
       -sum_i pi_i N*(u_i)^2
       -2t sum_(i<j) c_ij N*(b_ij)^2,                      (8)

subject to W_i(v)>=0 for every i,v. Indeed a linear functional is bounded below on K exactly under that condition, and its infimum is then0. At the minimizer the positive vertex measure is supported where W_i(v)=0. The KKT argument above again supplies equality and dual attainment. This removes the root-budget multipliers but leaves a genuine nonnegative-potential obstacle.

A sufficient remaining estimate is therefore: for every such dual family satisfying W_i>=0, expression (8) is <=C^2 E_t(p), uniformly for positive cone inputs. It is not proved here. Replacing the inequality W_i>=0 by equality would remove the cone constraint and recover a different, ambient problem. Similarly, the coordinatewise positive part of edge flows need not lie in K, and positive part of vertex charges is not KR-Lipschitz; the normalization lemma does not supply either missing operation.

## Current status and provenance

The parent proposed direct constrained minimization after the simultaneous-coupling route stalled. Equations (3)–(8), the cone reduction and normalization proof are author-side derivations in this round. The source expected-median/quartic-potential mechanism was reread in its operative lines195–390. The finite minimum-sampling counterexample in the companion note rules out that specified family of witnesses, including common adaptive convex minimum mixtures; it does not lower-bound (1).

No uniform estimate for (6) or (8), no universal positive-cone retraction, and no other full-scope cotype witnesses have been established. The original full T332 target remains unresolved. These exact reformulations retain its quantifiers and are intended to prevent future work from silently replacing the missing positivity estimate by ambient cotype.
