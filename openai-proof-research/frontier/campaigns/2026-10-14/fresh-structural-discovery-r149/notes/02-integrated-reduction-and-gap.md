# Strongest integrated reduction and precise remaining obligation

PREFREEZE. No theorem statement is frozen or nominated. This is a feasibility derivation, not an author-proof submission, a correctness grade, or a contribution grade.

## Exploration retained at full scope

The exploratory question is the positivity part of Ellzey1709.00454v2 Conjecture 1.4: for every finite circular indifference digraph Γ (including permitted antiparallel arcs), every partition λ of |VΓ| and every j≥0, the coefficient [e_λ q^j] X_Γ(x;q) is nonnegative. Ellzey additionally conjectures unimodality; this round does not rename or weaken the old project frozen natural-unit-interval unimodality scope U. No result on a subclass, q=1, positive real q, fixed width, or fixed number of colors is offered in place of this exploration.

## Operations already paid

1. Pinned Source169 proves coefficientwise elementary positivity for all linear natural unit interval graphs, using commuting independent-set sums, a quantum-torus coefficient kernel, triangular positive walls, and a partition-valued witness. Its operative sections 01–07 were read, including all local reordering and finite-coefficient controls. The source is stipulated true.
2. Ellzey's actual two-color involution proves symmetry for circular indifference digraphs; consistently directed even cycles are allowed in the two-color components. Directed cycles have an explicit positive elementary generating function. Neither symmetry nor the one-port directed-cycle case is an unpaid operation.
3. Vailaya2609.33124v1 supplies a common q=1 multiport basis and trace construction for all proper circular arc graphs. Its entire proof was read, including finite-color specialization and the Vandermonde argument. Cyclic closure at q=1 is paid.
4. Hikita2410.12758v2 supplies rational-q local transition probabilities for every linear natural unit interval graph. Sections 3–4 actually prove the operator-level modular laws using antisymmetric tableau differences and residue identities. Tom–Vailaya2503.19344v1 Proposition 4.7 and Theorem 4.9 give one-port graded gluing and equality with polynomial forest-triple matrices; these proofs, not just their statements, were read. The latter matrices need not be coefficientwise positive merely because the tableau formula is positive for positive real q.

## Graded multiport trace compatibility is stronger than the initially failed fixed basis

Use finite N, field K=Q(q,x_1,...,x_N), and states ordered k-tuples of distinct entries in [N]. The color append operator is

 Mhat_k(q)b_i = sum_(c notin i) x_c q^(#{a in i:a<c}) b_(i,c),

and Dhat deletes the first entry. Let a tableau state be σ. Color all integers ≤0 and all σ entries red; the other positive integers are white. Let W be red-to-white transition positions and R white-to-red positions. Define

 A_q(y|σ) = [y]_q prod_(b in R)[y-b]_q / prod_(a in W, a≠y)[y-a]_q  (y in W),

and zero otherwise. The proposed tableau append has coefficient A_q, while deletion has coefficient e_(σ1)/e_(σ1−1). Omit append positions >N. The q=1 specialization is exactly Vailaya's local formula. For q>0 each allowed A_q is positive, by interlacing of W and R (negative q-integers cancel in pairs); this is not coefficientwise polynomial positivity.

There is a compatible finite-state argument, avoiding the failed unchanged q=1 basis. It shows why claiming that every graded multiport intertwiner is unpaid would be too strong:

* Every nonnegative-height M/D word starting and ending at level 0 describes a FIFO interval construction: vertices arrive at M and leave at D. It gives a linear natural unit interval graph. The color vacuum evaluation is its ascent CSF. For the tableau evaluation, appending at column y supplies [y]_q φ_y; deletion later supplies e_y/e_(y−1). Over a completed history the elementary ratios telescope to e_shape and the q-integers multiply to the product of row q-factorials. Thus Hikita's scalar identity equates the two vacuum evaluations. Truncating at column N is legitimate: any history reaching a larger column ends with an elementary factor e_r, r>N, and vanishes in N variables. This is a rational-function calculation; no positivity is inferred from inversion.
* At q=1, color reachability from the vacuum follows inductively. Put Rhat_k=Mhat_(k−1)Dhat_k−Dhat_(k+1)Mhat_k. It rotates (a,w) to (w,a) with weight x_a, and Rhat_k^k multiplies a tuple by the product of its colors. Given an input tuple i at level k−1, the vectors (Rhat_k^k)^u Mhat_(k−1)b_i, 0≤u≤N−k, separate all choices of the appended color by a Vandermonde matrix. Rhat is a linear combination of legal M/D words.
* Observability has a dual elementary argument. Assuming all suffix coordinate rows at level k−1 are reachable by output words, apply such a row after Dhat_k(Rhat_k^k)^u. For a fixed suffix w this gives weights (x_a prod w)^u on all admissible first colors a. Another Vandermonde matrix separates them. Hence output words span the dual at every level. Both arguments remain true at k=N with Mhat_N=0.
* Vailaya's q=1 invertible common basis transfers both properties to the tableau system. Choose finite lists of input/output words furnishing bases at q=1. Their determinants are rational in q and are nonzero at 1; hence they remain nonzero over K. The finite Hankel matrix of scalar evaluations agrees by Hikita. The map sending each tableau input-word vector to its color counterpart is therefore well-defined: any relation is annihilated by all output words on one side, hence on the other, and observability kills the difference. It is invertible and intertwines M and D by the same argument. Thus traces of finite closed words agree generically in q, and identities extend rationally. The bounded diagnostics (126 constant-width and 240 varying-width tests) support this calculation but do not prove it.

This argument uses only compatible known scalar identities, the q=1 full basis, and elementary finite-dimensional realization. It is treated as a reduction, not substantial-contribution evidence and not a supporting nominee. A separate full directed circular presentation still has to assign each arc exactly once when cutting at a clique boundary, especially antiparallel arcs; no claim that this bookkeeping was verified at every endpoint convention is made. Even granting the full trace identification, the main coefficientwise obligation below remains.

## What is actually unpaid

The finite tableau trace is a sum of Laurent elementary monomials with rational functions of q that are positive for q>0. Equality with a symmetric polynomial can remove negative elementary exponents. It does NOT remove negative q coefficients. Even a quotient of polynomials with nonnegative coefficients can be a polynomial with a negative coefficient: (1+q^3)/(1+q)=1−q+q^2. Hikita's probabilities are rational, not a coefficientwise-positive polynomial certificate.

To finish the retained exploration, one needs a uniform all-boundary/all-partition cancellation or positive expansion showing that every elementary coefficient of the full graded circular trace lies in N[q], with finite-N stability and each directed arc counted once. Source169 pays the unmarked linear scalar case, not an arbitrary boundary contraction. Its witness preserves total exponent and energy, but packet switches can redistribute increments; the read proof does not establish preservation of the equality constraints identifying all marked boundary colors. The minimal-realization change of basis above uses inverse Hankel matrices and supplies no positive contraction. A successful compatible positive boundary refinement, trace-level cancellation, or another source/classical composition has not been obtained.

For an attempted torus quotient, simply identifying the ends of the linear anchor chain makes the cyclic bridge sum zero and violates the free pointed-cone chart used in the actual wall theorem. It does not establish impossibility of an affine enlargement, a different cone, or trace-level cancellations. Incoming quiver cycles already occur in linear project history; 'there is a cycle' is not itself an obstruction.

No impossibility theorem, exclusion of other compatible classical compositions, exhaustive search certificate, priority claim, or full-scope mathematical result is asserted. The precise remaining problem is coefficientwise positivity of the full boundary trace, not merely q=1, scalar open positivity, existence of graded rational matrices, or unchanged-basis failure.

## Direct quantum-torus composition also pays commutation, not positivity

There is another compatible reduction within the same family. For a circular indifference digraph put Ω(a,b)=1_(a→b)−1_(b→a), with this sign chosen to count ASCENTS in a product ordered by increasing color. Let E_k be sums of X_I over independent sets of the underlying graph. In the two-colored induced digraph, the relevant circular-indifference property makes components consistently directed paths, consistently directed even cycles, or isolated antiparallel pairs, with isolated doubled vertices handled separately. This is the structural input actually used in Ellzey's symmetry proof.

In a term E_j E_k, exchange the two memberships on components with an odd number of vertices and leave even components fixed. The odd path components have equal numbers of the two alternating skew edge signs, hence zero skew weight; even cycles and antiparallel pairs have zero total imbalance. Even components have equal color-class sizes. Thus this operation swaps the global sizes j,k and preserves exponent and skew weight. It proves commutation in exactly the source's manner. The elementary dual Cauchy identity then gives

 [e_λ]X_Γ(x;v²) = v^|EΓ| [X_(sum vertices)] m_λ(Y).

An antiparallel pair contributes one ascent in every proper coloring, zero Ω, and two arcs to |EΓ|, so the normalization accounts for it correctly. This reduction requires no false embedding of a circular graph in a linear interval graph. It does not imply positivity of m_λ(Y): already m_(2)=E_1²−2E_2 has subtraction. The missing step is a positive wall/section identification or another positive evaluation of this exact circular graph alphabet. The pinned triangular embedding supplies that step only under its actual linear interval hypotheses. This is a further paid compatible operation, not a full nominee or a global impossibility statement.
