# Every ell1 nearest-point selection fails uniformly, already on a path

Myeongjin Kang, no affiliation. Original prose CC BY4.0. Author-side route exclusion only. No nomination, independent review or priority claim. This is not an obstruction to all retractions or to the unchanged T332 extension theorem.

Let n=2m+1, m>=1. On the rooted path of n unit edges, the positive vertex-measure cone is

    K={q in R^n:q_1>=q_2>=...>=q_n>=0}.

For 0<t<1 take the nonnegative ambient flow

    x(t)=(0,...,0,t,1,...,1),

with m zeros and m ones. The UNIQUE minimizer of ||q-x(t)||_1 over K is q(t)=t(1,...,1).

Indeed, pair coordinate i with n+1-i, for 1<=i<=m. Write a=q_i, b=q_(n+1-i); feasibility gives a>=q_(m+1)>=b>=0. The paired contribution is a+|b-1|. If b<=1 this is1+a-b>=1. Equality forces a=b. If b>1 it equals a+b-1>1. Thus every pair contributes at least1, with equality only when a=b in[0,1]. The central contribution is |q_(m+1)-t|>=0. The objective is therefore at least m. The constant vector t attains m. Equality requires the central coordinate t and all paired coordinates equal, hence by their bracketing of the central coordinate every coordinate equals t. This proves uniqueness directly, without restricting beforehand to symmetric competitors.

For s,t in(0,1),

    ||x(t)-x(s)||_1=|t-s|,
    ||q(t)-q(s)||_1=(2m+1)|t-s|.

Consequently every selection of ell1 nearest points onto K has Lipschitz constant at least2m+1. There is no dimension-independent bound. Since q(t) has all coordinates in[0,1], the same unique minimizer occurs for path probability flows (the additional condition q_1<=1). Both inputs x(t),x(s) are ambient signed flows, as permitted in the sufficient retraction problem, not feasible probabilities.

The known1-Lipschitz path rearrangement does not contradict this. It sends x(t) to (1,...,1,t,0,...,0), whose distance from x(t) is2m, whereas the nearest feasible distance is m. Its output is deliberately not nearest. This example therefore exposes a genuine constraint on the operation, not a lower bound on the optimal retraction constant.

## Minimum-cost signed-mass cancellation is included

At path vertices labelled by distance from the root, x(t) corresponds to positive mass1 at vertex n, negative mass t at vertex m, and negative mass1-t at vertex m+1; the root balances the total. Consider the rule that supplies negative charges from the positive atom or an unlimited root reservoir, minimizes total tree-transport cost, then keeps unused positive mass.

For the negative atom at m, root supply costs m per unit and leaf supply costs m+1. For the negative atom at m+1, leaf supply costs m per unit and root supply costs m+1. Leaf mass1 suffices for the latter's demand1-t. Therefore the unique minimum-cost allocation uses the root for the first demand and the leaf for the second; it leaves mass t at vertex n. This is exactly q(t). Thus that natural minimum-cost cancellation rule has the same unbounded sensitivity. This says nothing about suitably non-optimal or randomized cancellation rules.

## Attribution and boundary

The construction was derived here after reading r42's path/branching/normalization notes. The parent checked its paired-coordinate proof author-side. The parent's separate t332-parent-positive-projection-r1/projection-obstruction.md proves an unbounded obstruction for each fixed coordinate ell-p projection with p>1 on binary trees. That entire proof was read and checked here; it is not duplicated as this agent's result. Together these exclude the ordinary fixed-p nearest-point approaches, not arbitrary retractions, tree-dependent optimization metrics, or direct cotype estimates.
