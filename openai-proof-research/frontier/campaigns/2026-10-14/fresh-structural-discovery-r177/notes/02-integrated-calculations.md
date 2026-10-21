# Integrated cyclic-filtration calculations (prefreeze, no nominee)

These are durable feasibility derivations, not a frozen author-proof submission or an independent mathematical grade. All chromatic conclusions use Source314 at the stipulated pin. The quantitative group calculations below are checked directly. The third note states the remaining operation without asserting its solution.

## 1. The exact complement interface

Let p be any prime, B a finite abelian p-group, alpha an automorphism of p-power order, H a finite cyclic p-group acting on B through alpha, and G=B semidirect H. We identify H with the specified complement; the action need not be faithful. Put delta=alpha-1 in End(B).

Every subgroup K containing H has K=M semidirect H with M=K intersect B. Indeed, multiplying (x,h) in K by (0,h^-1) leaves (x,1) in K. Conjugation by H makes M alpha-stable. Conversely every alpha-stable M gives such a K.

For M<=N, M semidirect H is normal in N semidirect H exactly when delta(N)<=M. Necessity follows by conjugating H by (x,1), x in N. Sufficiency follows because B is abelian and all the remaining conjugations are already controlled by alpha-stability. Under this condition the map N -> (N semidirect H)/(M semidirect H) is surjective with kernel M. Its quotient is cyclic exactly when N/M is cyclic.

Consequently ell(G,H) is precisely the minimum number of strict terms in
  0=M_0 < M_1 < ... < M_s=B,
  delta(M_i)<=M_(i-1),  M_i/M_(i-1) cyclic.
This handles ALL intermediate subgroups, including mixed subgroups of a direct sum. It does not assume that the intermediate subgroups split along coordinates. If the delta condition holds, alpha-stability of every term follows as well.

Source314 thm:main then identifies this minimum with r_n(G,H) for every n>=0. Every integer loss smaller than this minimum has the finite genuine p-local spectrum witness from the source, with compact retracts included. No separate finite-witness or cell-complex construction is claimed here.

## 2. A cyclic-filtration lemma for finite abelian groups

Let A be nonzero, abelian, of order p^N and generator rank d. For b>=1, the minimum length of a cyclic-factor filtration in which each factor has exponent at most p^b is
  s=max(d,ceil(N/b)).
The lower bounds follow from lifting one generator per factor and multiplying factor orders.

Here is an explicit existence induction, avoiding a claim inferred from a partition diagram. More generally, for any integer d<=s<=N with N<=s*b, one can use exactly s nontrivial factors. Write the invariant exponents as lambda_1>=...>=lambda_d>=1.

If s>d, choose c=max(1,N-(s-1)b). Then c<=b, c<=lambda_1 and c<=N-s+1. The middle inequality follows from c<=ceil(N/s)<=lambda_1 (or directly from N<=s*b). A cyclic subgroup C of order p^c exists in the first summand. The quotient has rank at most d<=s-1 and order p^(N-c), where s-1<=N-c<=(s-1)b. Apply induction to A/C and pull the chain back.

If s=d, choose c=max(lambda_d,N-(d-1)b). Both quantities are at most b, because lambda_d<=N/d<=b. Also c<=lambda_1 and c<=N-d+1. There is a primitive element x of exact order p^c: if d=1 use the generator (then c=N); if d>=2 take
  x=p^(lambda_1-c)e_1+e_d,
where e_i is a generator of the i-th summand. Its order is p^c, and its image in A/pA is nonzero because of the e_d coefficient. Thus A/<x> has generator rank d-1, exactly: its quotient modulo p has dimension d-1. Its order again meets the induction bounds. Pulling back the resulting chain proves the assertion. The case A=0 has length0.

This is elementary invariant-factor bookkeeping. It supplies the entire constant-scalar delta operation, since delta=p^b id makes delta(M_i)<=M_(i-1) equivalent to the exponent bound on M_i/M_(i-1).

## 3. One active cyclic factor and arbitrary trivial abelian factors

Fix 1<=b<a, k>=0, and integers r_1,...,r_k>=1. On
  B=C_(p^a) direct-sum A,  A=direct-sum_i C_(p^r_i),
let delta act by p^b on the first coordinate and by0 on A. Then the exact filtration length is
  L=max(k+1, ceil((a+sum_i min(r_i,b))/b)).                 (1)
To realize the associated group take alpha=1+delta and any cyclic H of p-power order divisible by the order of alpha. Such an order exists for every prime, including2; no odd-prime order formula is used.

Lower bound: project the entire filtration to B/(0 direct-sum p^b A). On this quotient delta=p^b id. The quotient has order p^(a+sum min(r_i,b)), so each surviving cyclic factor has order at most p^b. Also the original B needs k+1 generators. These prove both terms in (1), with no splitting assumption on the original filtration.

Upper bound: remove separately the q summands with r_i>=b, each in one step with delta=0. On the remaining group delta=p^b id, because all residual trivial factors have exponent at most p^b. Section2 gives length
  max(k-q+1, ceil((a+sum_(r_i<b) r_i)/b)).
Prepending the q steps gives exactly (1), because adding q outside the maximum gives k+1 and ceil((a+q*b+sum short r_i)/b). All subgroups in this construction are compatible with the original delta.

For equal r this becomes max(k+1,ceil((a+k*min(r,b))/b)), the initially exploratory formula in note01. Thus that particular exploratory formula is now accounted for by the elementary reduction, not left as an empirical guess.

The parameter p=2,a=3,b=2,k=1,r_1=1 gives length2, agreeing with the actual mixed chain in Kuhn--Lloyd Example5.15. Setting k=0 gives ceil(a/b). If every r_i>=b, (1) is ceil(a/b)+k; small exponents can be absorbed into a mixed chain. For example a=4,b=2 and two trivial C_p factors give length3 rather than4. This is why the source's product upper bound cannot be treated as an equality.

The source's product-series lemma is compatible with (1): for sufficiently large equal r, the full additive loss returns. Formula (1) gives a finite threshold for THIS metacyclic-complement family; it does not assert such a threshold for an arbitrary group pair.

## 4. Two genuinely different scalar actions

There is a stronger closed feasibility calculation than concatenating two copies of Section3. Let
  1<=b<c, a>b, e>c,
  B=C_(p^a) direct-sum C_(p^e),
  delta(x,y)=(p^b x,p^c y).
Then the exact length is
  L=max(ceil(a/b)+1, ceil((e+b)/c)).                       (2)
Again alpha=1+delta has p-power order, so this has the full complement/chromatic interpretation of Section1 at every prime and height.

Lower bound: form Q_b=B/(delta-p^b)B and Q_c=B/(delta-p^c)B. Since p^(c-b)-1 is a p-adic unit, these are respectively
  Q_b=C_(p^a) direct-sum C_(p^b),
  Q_c=C_(p^b) direct-sum C_(p^e).
The induced delta is p^b id on Q_b and p^c id on Q_c. Project any admissible chain and use order accounting: its length is at least ceil((a+b)/b) and ceil((e+b)/c). These are precisely (2).

Upper bound: set s to the right side of (2), t=s-1, and take
  g=(1,p^(c-b)), y=(0,1).
The inequalities defining s give bt>=a and ct+c-b=cs-b>=e. Therefore delta^t g=0. Let
  M_j=<delta^(t-j)g,...,delta^(t-1)g>,  1<=j<=t,
with M_0=0. Each factor is cyclic and delta(M_j)<=M_(j-1). Terms may initially be allowed to repeat; deleting repetitions only improves the upper bound.

Let U=M_t. Since a>b, t>=2, and U contains g and delta g. Their difference satisfies
  delta g-p^b g=(0,p^c(p^(c-b)-1)).
Multiplication by the displayed unit is invertible on the second cyclic factor, hence p^c y belongs to U. Also g has first coordinate1, so B/U is generated by y. It follows that U<B is one further admissible cyclic step: delta y=p^c y is in U. The resulting chain has at most s steps, and the lower bound gives equality.

This calculation tunes the p-adic weight of g so that its delta orbit terminates at the necessary height while the remaining quotient is cyclic with trivial action. It proves, for example, length4 when (a,e;b,c)=(3,4;1,2), rather than the length5 obtained by separate coordinate filtrations. The retained finite enumeration produces factors p,p^2,p^3,p in that example. Formula (2) is not the old r66 commutator-rank theorem: B here is abelian and the group pair uses a specified complement. Nevertheless this is a short elementary module construction, and no substantial-contribution claim is being made for it.

## 5. A three-action construction beyond pairwise concatenation

On B=C_(p^3) direct-sum C_(p^3) direct-sum C_(p^4), take delta=(p,p^2,p^3). Successively adjoin
  v_1=(p^2,0,0), v_2=(p,0,0), v_3=(1,p,0),
  v_4=(0,1,p), v_5=(0,0,1).
These generate all of B. The delta identities are
  delta v_1=0, delta v_2=v_1, delta v_3=v_2,
  delta v_4=p*v_3-v_2,
  delta v_5=p^2*v_4-(p*v_3-v_2).
Thus they give an admissible chain of at most5 cyclic factors at EVERY prime. The scalar quotient B/(delta-p)B has order p^5 and delta=p, so at least5 steps are necessary. The length is exactly5. At p=2 the retained BFS has the same chain and factors2,2,4,8,8, with429 discovered states.

Separate-coordinate chains cost3+2+2=7. The strongest pairwise application of (2) plus the remaining coordinate costs6. This five-step construction therefore checks a genuine interaction left out by pairwise optimization. It is a small explicit example, not a full general multi-action result and not a proposed substantial nominee.

## 6. Diagonal pairs: retained but not developed into a nominee

For any finite p-group P, overgroups of Delta P in P x P are K_N={(x,y):xy^-1 in N}, N normal in P. To see this, use multiplication by (y^-1,y^-1) to identify N through the first-coordinate kernel; conjugation by Delta P gives ambient normality. Every K_N is generated by N x1 and Delta P.

For N<=M, K_N is normal in K_M iff [P,M]<=N: normality under M x1 of the diagonal is exactly this commutator requirement. Then K_M/K_N is M/N. Thus ell(P x P,Delta P) is the minimum length of a central series of P with cyclic factors. The correspondence is elementary, does not bypass the cyclic-chain optimization, and is not a protected Quillen top-image target or a new nomination.
