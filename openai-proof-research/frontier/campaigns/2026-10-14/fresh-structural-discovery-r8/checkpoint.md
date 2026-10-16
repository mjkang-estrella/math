# Mathematical checkpoint

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; code MIT.

Full U remains unresolved. The pinned triangular chart uses the forward-gap
root cone, not the vertex cone. For D=3 its five-root skew matrix is

    0 -2  0  1  0
    2  0 -1 -1  1
    0  1  0 -1 -1
   -1  1  1  0 -1
    0 -1  1  1  0

This same principal block occurs for every D>=3, irrespective of the allowed
phases: theta_(2,2)<theta_(1,1)<theta_(1,2) determines its adjacencies.
The three roots 0,1,3 form a directed cycle. This rules out direct application
of the acyclic hypothesis in Davison–Mandel Theorem 2.18; it does not prove
mutation-cyclicity and does not disprove U. Bounded mutation search found no
acyclic seed through depth 10 with entries bounded by 10 (21,092 labelled
states), but every proper four-root principal subquiver does have an acyclic
mutation. These are diagnostics, not a global classification.

For S_3, set V_0=V_2=M^(3) and V_1=M^(2,1). Since M^(2,1)=1+Std,
there is an equivariant hard Lefschetz operator: a three-degree trivial
string plus Std in the middle. Every degree is a Young permutation module.
Nevertheless the coefficient of h_3 is (1,0,1), so Young multiplicities
need not be unimodal. This is an abstract representation countermodel,
not Hessenberg cohomology or a graph counterexample.

Bar invariance, fixed parity and the weaker pre-Lefschetz property do not
close the gap either. In the notation P_r(v)=v^(r-2)+v^r for odd r,

    P_-3+2P_-1+2P_3+P_5
      = v^-5+3v^-3+2v^-1+2v+3v^3+v^5

is positive, bar invariant, parity pure, has no gaps, and is not unimodal.

Paid conditional propagation: if every jump coefficient in the pinned
incoming-coordinate recursion is a finite sum of centered sl_2 strings,
then induction on its finite cone intervals gives the same property for
the sections. The target coefficient v^-M c_lambda(v^2) would then be
Lefschetz. The required jump property for the cyclic gap charts, or a
target-specific alternative, remains unpaid. No identification with
standard broken-line theta functions has been assumed.

The complete exact coloring/elementary-basis calculation through n=6 covers
196 Hessenberg sequences, 1,836 elementary polynomials and 5,543 lower-half
inequalities. It finds no counterexample and proves no all-n assertion.
