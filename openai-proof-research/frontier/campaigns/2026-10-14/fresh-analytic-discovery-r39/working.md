# T332: probability-valued extension on real trees

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Author-side work, not an independent gate.

The full target in original-scope.txt remains unproved and unrefuted. All statements below concern proposed constructions; none is a counterexample to that target. In particular, failure of an ambient retraction does not logically imply failure of Hilbert-domain extension.

## 1. The exact finite interface

For a finite rooted metric tree with positive edge lengths w_e, encode a probability measure by q_e=mu(T_e). Write q_root=1 and q_v for the coordinate on the edge entering a nonroot vertex v. The feasible set is

    C_T = {q: q_v >= sum_{u child of v} q_u >= 0 at every vertex,
                 1 >= sum_{u child of root} q_u}.

Equivalently q_e>=0 and each vertex has nonnegative residual mass. The residual at v is q_v minus its children's sum; the root residual is one minus its children's sum. Telescoping gives total mass one. Conversely every feasible vector gives precisely that probability measure. The transport formula is

    W1(mu,nu) = sum_e w_e |q_e(mu)-q_e(nu)|.

This is the primary Evans--Matsen formula, read through Mathey-Prevot--Valette Theorem1.4, Proposition3.1 and Theorem3.3. Their constructive proof first moves surplus mass up and then moves deficits down **between two already specified probability measures**. It does not choose a positive measure from an arbitrary signed input, and it does not prove stability of such a choice.

The pinned source proves its metric Markov-cotype bound by weighted cut encoding, the cubic phi(h)=3h^2-2h^3, a quartic Hilbert martingale potential, and an affine contractive reconstruction. Its modified points are expected coordinatewise medians of three independent geometric-walk endpoint data. The stationary construction and bound3024 are fully paid. Source cor:extension then gives Hilbert-to-ell1 extension via the generalized Ball theorem and ell1's dual structure.

A universal L-Lipschitz retraction R_T from weighted ell1(E) to C_T would therefore settle the finite-tree target immediately, with constant LK. This is only a sufficient route. Restricting the source median to C_T without a correction is invalid.

## 2. A source-construction obstruction, including an actual resolvent

On a three-leaf unit star let

    x1=(0,1/2,1/2), x2=(1/2,0,1/2), x3=(1/2,1/2,0).

Each vector represents a probability measure supported on the leaves. Their coordinatewise median is (1/2,1/2,1/2), not feasible. Independent uniform choices give expected median coordinates (1/2)phi(2/3)=10/27, total10/9.

The same failure occurs for an actual source resolvent, not merely an arbitrary endpoint law. Take the three-state transition matrix A with every entry1/3 and stationary law uniform. It is reversible. At source time t=2, p=1/3,q=2/3 and G=pI+qA. Its first row is (5/9,2/9,2/9). At coordinate1, the probability of a value1/2 is4/9, and at coordinates2,3 it is7/9. Thus the source output has total

    (phi(4/9)+2phi(7/9))/2 = 263/243 > 1.

It corresponds to negative root mass -20/243. This shows that the source's quantitative bound cannot simply be read as a bound inside P1(T). It does not invalidate any source assertion, whose target is the full ell1 space.

## 3. Ordinary normalization loses the edge-length ratio

On a root with two leaves of lengths epsilon and1, feasible flow x=(0,1) and signed flow y=(delta,1) have ambient distance epsilon*delta. Positive-part normalization N(y)=y/max(1,sum y_i) gives

    ||N(y)-N(x)||_(1,w)=delta(1+epsilon)/(1+delta).

The ratio is (1+epsilon)/(epsilon(1+delta)), unbounded as epsilon decreases. The unchanged long-edge mass is scaled in response to cheap excess on the short edge. This is not a reason to impose an aspect-ratio restriction on T332.

## 4. Exact nearest-KR projection cannot be the correction

Work on the compact interval T=[-1,1], already a complete real tree. For |s|<1 let the signed mass-one measure be

    sigma_s=delta_{-1}+delta_1-delta_s.

For s>0 its unique closest probability measure in the Kantorovich--Rubinstein norm is delta_{-1}; for s<0 it is delta_1. Here is a direct proof. The signed cumulative function is1 on(-1,s) and0 on(s,1). A probability cumulative function F is nondecreasing and lies in[0,1]. Put a=1+s,b=1-s and let c be the average of F on(-1,s), d its average on(s,1). Monotonicity implies c<=d. The norm distance is

    a(1-c)+bd >= a+(b-a)c.

When s>0, b-a<0 and c<=1, so this is at least b. Equality requires c=d=1, hence F=1 almost everywhere on(-1,1), and the probability is delta_{-1}. Conversely that probability achieves b. The case s<0 follows symmetrically. The cumulative-norm identity follows either from one-dimensional transport or integration by parts in the KR dual formula, and holds for signed total-mass-zero differences.

But ||sigma_s-sigma_{-s}||_KR=2s while W1(delta_{-1},delta_1)=2. Consequently every exact nearest-point selection is discontinuous at sigma_0. The target still permits non-nearest Lipschitz corrections; this argument excludes only exact nearest projection/cancellation.

## 5. Weighted stars admit a simple correction

This technical positive calculation prevents overinterpreting section3. Order the leaf lengths w1<=...<=wn. First replace each input coordinate by its positive part. Retain up to total mass1, visiting leaves in decreasing length order:

    R_i(x)=min(x_i^+, (1-sum_{j>i} x_j^+)_+).

The unassigned mass is placed at the root. This is a retraction onto C_T and is2-Lipschitz for the weighted ell1 metric. To prove the bound, vary just coordinate k after positive-part clipping. On every interval where the active cutoff index is fixed, either that coordinate is entirely discarded, the retained vector is constant, or its increase is balanced by removing the same amount from a coordinate j<=k. The weighted output speed is at most w_k+w_j<=2w_k; when total mass is below1, it is w_k. The formula is continuous and piecewise affine, so integration proves the same bound across cutoff changes. Change input coordinates one at a time and sum. Positive-part clipping is1-Lipschitz, completing the proof.

Thus the full finite weighted-star extension follows technically from the source. It is not a replacement target, not a nomination, and not asserted new to the literature.

## 6. A fixed priority does not combine branches and long paths

A natural extension of section5 is lexicographic flow correction: order all edges once, and, in that order, choose the feasible coordinate closest to its prescribed value while preserving earlier choices. This is well defined on the compact polytope C_T, but its Lipschitz constant is not uniformly bounded.

On an m-edge unit path, feasible flows satisfy 1>=q1>=...>=qm>=0. Let k be the highest-priority edge. Starting from the all-zero vector, change only coordinate k to delta in(0,1). The lexicographic rule keeps qk=delta. Every upstream coordinate is forced to at least delta and is then set to delta; downstream coordinates remain0. The output distance from zero is k*delta, for input distance delta. Alternatively start from the all-one vector and reduce coordinate k by delta. Every downstream coordinate is forced to1-delta, while upstream coordinates stay1; the ratio is m-k+1. Hence one of these two inputs gives amplification at least(m+1)/2, regardless of the fixed priority order. No branching or length degeneracy is needed.

This does not exclude averaging along paths, isotonic methods, or a joint adaptive construction. It shows that weighted-star clipping cannot simply be iterated edge by edge.

## 7. Direct chain-energy rounding: what was tried and what is missing

A retraction is stronger than necessary. For a reversible finite chain (A,pi), time t, and feasible input flows x_i, one could instead seek feasible y_i with

    sum_i pi_i ||x_i-y_i||_(1,w)^2
    + t sum_ij pi_i A_ij ||y_i-y_j||_(1,w)^2
    <= C^2 sum_ij pi_i (t^-1 sum_{s=1}^t A^s)_ij ||x_i-x_j||_(1,w)^2,

uniform in the tree and all chain parameters. The source supplies this in the ambient flow space. A pointwise bound for the distance of each corrected output from C_T is insufficient: independently correcting by the input x_i gives an uncontrolled factor t in the pairwise term.

Two attempted constructions explain why the remaining debt is not just initial notation.

* Lift the chain using optimal couplings of neighboring probability measures, and apply tree-valued smoothing. This naturally controls expectations of squared point distances, whereas the required costs are squares of W1 distances. There is no uniform comparison: mu=delta_o, nu=(1-h)delta_o+h delta_v with d(o,v)=1 have W1^2=h^2 but every optimal coupling has expected squared distance h. The ratio1/h diverges. Independent sampling of three tree points also fails the identity condition when all input measures agree: its median law need not equal that common measure.
* Use coordinated transport rounding on a tree. Archer--Fakcharoenphol--Harrelson--Krauthgamer--Talwar--Tardos Proposition3.1 and Corollary3.1 preserve prescribed marginals and the **first** distance cost along a tree **of query vertices**. Here the target label space is a tree, while A may have arbitrary cycles. Their reduction of a general query metric to trees loses O(log n), and their probability vectors are already feasible. Their exact operation therefore supplies neither signed-flow correction nor the displayed squared uniform estimate. Replacing the Markov chain by a tree or tolerating a logarithmic number-of-states loss would change the target.

The desired joint branching/path correction or constrained energy estimate has not been proved. No theorem is inferred from these tests.

## 8. Global scope is an additional genuine obligation

Mendel--Naor Theorem1.11 is a finite-extension theorem. Their following discussion explicitly sends a general extension into a target ultrapower and requires a Lipschitz retraction back; Corollary1.13 treats suitable Banach targets. P1(T) is neither the full L1 ambient space nor generally proper. Compactness of bounded first-moment sets cannot be assumed: on the complete countable unit star, the measures delta_{v_n} all have first moment1 and mutual W1 distance2, and are not uniformly tight. The family ((1-1/n)delta_o+(1/n)delta_n) on a ray also has bounded first moments but no uniform first-moment tail integrability.

It may be possible to exploit a special tree ultrapower projection, or L1 decompositions of the flow cone, but no such construction with all Radon/measurability and mass conditions has been completed here. This is retained rather than quietly restricting the statement to finite or compact trees. The decisive presently missing estimate already occurs before this passage, in the finite-tree constrained construction.

## Disposition

Full T332: unresolved, not refuted. Source theorem and classical transport operations: stipulated/paid. Sections2--6 and the cost example in7: exact route diagnostics and a technical star calculation. No new substantial theorem, no independent review PASS, no count increment, and no broad formalization proposed. An appropriate future formal check would verify finite-flow feasibility, the resolvent counterexample, and the star/priority formulas; that would not prove T332.
