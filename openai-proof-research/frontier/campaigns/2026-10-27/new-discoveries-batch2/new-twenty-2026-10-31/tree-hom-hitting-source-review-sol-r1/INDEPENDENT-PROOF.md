# Independent ordinary proof for MathDB 351988

Personally derived and checked by GPT-6.1 Sol high/default. This is ordinary mathematics, with no mathematical program, enumeration, CAS or formal execution. Author deductions were not treated as upstream truth.

## Exact domain

T and U are arbitrary finite unweighted simple trees with equal vertex count n. Assume hom(T,G) >= hom(U,G) for EVERY finite simple graph G, including disconnected graphs and graphs with isolated vertices. No shape, distinctness, bipartition, transfer or size bound is added. For the source random walk take n>=2; set H(v,v)=0 and alpha(T)=n^(-2) sum over ordered u,v of H(u,v).

The copied source defines a tree as connected and acyclic but supplies no singleton transition rule: its degree-proportional walk and its volume denominators are meaningful without an extra convention only when n>=2. The singleton has no outgoing edge. With the usual absorbing-singleton extension H(v,v)=0 it has alpha=0 and the conclusion is equality. This extension is a convention, not a new outcome. Empty graphs are outside the nonempty connected tree/random-destination domain; the arithmetic mean at n=0 is undefined in the source. If a formal tree predicate permits empty graphs, it must explicitly exclude them or state a separately justified totalization. Merely using Lean's total division at zero does not authenticate a source definition. Neither n=0 nor n=1 is a counterexample or discovery credit. All substantive sizes are covered below.

## 1. Recover a continuum test from finite simple targets

Fix c>0 and let gamma be standard Gaussian probability on R. Put K(x,y)=exp(-c(x-y)^2/2), a symmetric measurable function in (0,1]. For an n-vertex simple graph F let
Z_F = integral product_{ab in E(F)} K(x_a,x_b) d gamma^n(x).
It is a finite, positive integral: boundedness gives integrability and strict positivity almost everywhere gives positivity.

For each integer N>=n use the finite product probability space of N independent gamma variables X_i and independent uniform variables V_{ij} for unordered pairs i<j. Set i~j iff V_{ij}<=K(X_i,X_j), and set no loops. This is a measurable random variable in the FINITE set of simple graphs on [N]; it neither assumes a graphon ordering nor changes the target domain.

For an injective map f:V(F)->[N], distinct edges of the simple source use distinct unordered pairs. Conditioning on X therefore gives homomorphism probability product K(X_f(a),X_f(b)); the distinct X coordinates have product law gamma^n. The unconditional probability is exactly Z_F. There are (N)_n injective maps. Every other map contributes a probability in [0,1], whether its edges collide, repeat, or map to forbidden loops. Thus
E hom(F,G_N)=(N)_n Z_F + R_F,
0<=R_F<=N^n-(N)_n.
For n>=2, maps having a collision belong to the union of the binom(n,2) events f(a)=f(b), each of size N^(n-1). Therefore |E hom(F,G_N)/N^n-Z_F|<=binom(n,2)/N (write it as ((N)_n/N^n-1)Z_F+R_F/N^n, or use that both terms range over the same missing fraction). For n=1 the error is zero. The pointwise assumed hom inequality implies the expected one, since all realizations are allowed simple graphs. Passing to the limit N->infinity gives Z_T>=Z_U. Only finite expectations and this explicit error bound were used; no independence is asserted for noninjective maps.

## 2. Evaluate precisely this integral

Orient the edges of F and let B be its incidence matrix, with entries +1,-1 at the two distinct ends. Its Laplacian L=BB^t has x^t Lx=sum_edges (x_a-x_b)^2>=0. The integral is
(2pi)^(-n/2) integral_R^n exp(-x^t(I+cL)x/2) dx.
The real symmetric spectral theorem gives an orthogonal matrix Q with diagonal entries lambda_i>=0 for Q^t LQ. The linear change x=Qy has absolute Jacobian 1. Tonelli applies to the nonnegative integrand; its one-dimensional factors are integrable, and substitution z=sqrt(1+c lambda_i)y_i gives
Z_F=product_i (1+c lambda_i)^(-1/2)=det(I+cL)^(-1/2).
The standard Gaussian integral is normalized by squaring integral exp(-x^2/2) dx, using the nonnegative planar product integral and polar coordinates, yielding 2pi. These are the upstream finite-dimensional spectral theorem, change-of-variables and Tonelli facts used here, with their hypotheses checked; no graph ordering theorem is cited. Each 1+c lambda_i is strictly positive. Since inverse square root is strictly decreasing on positive numbers, the previously proved inequality implies
D_T(c):=det(I+cL_T)<=det(I+cL_U)=:D_U(c) for all c>0.
This is one necessary family of tests, not a converse characterization of hom order.

## 3. Obtain the highest two coefficients without a hidden minor theorem

Now F is a tree. It has n-1 edges. Sylvester's determinant identity, obtained by eliminating either off-diagonal block in [[I_n,B],[-cB^t,I_(n-1)]], gives D_F=det(I_(n-1)+cB^tB). In the determinant's principal-minor expansion,
D_F(c)=sum_{S subset E(F)} c^|S| det((B^tB)_{S,S}).
Choosing identity entries in the complementary rows of the Leibniz formula proves that expansion including its positive signs. Cauchy-Binet for B_{:,S}^t B_{:,S} gives
D_F(c)=sum_S c^|S| sum_{R subset V(F), |R|=|S|} det(B_{R,S})^2.

For each S, (V,S) is a forest. If its components have orders a_1,...,a_k, it has n-k edges. In one tree component its full incidence block has rank a_i-1: the row sum is zero; deleting any chosen root row leaves a determinant of absolute value 1. For this last assertion induct on a_i: for a_i=1 the empty determinant is 1; otherwise choose a leaf different from the root, expand its sole nonzero row entry, and delete that leaf and edge. A tree with at least two vertices has such a leaf. The remaining matrix is the corresponding rooted minor of the smaller tree. Signs do not affect the square.

After grouping rows and columns by components, columns of a component have support only in its selected rows. If any component has fewer than a_i-1 selected rows, those columns are linearly dependent. If none has fewer, the fixed total n-k forces exactly a_i-1 rows in every component. Hence the determinant is nonzero exactly when R omits one vertex per component; the component minors then have squared determinant 1. This also handles isolated vertices, whose single row must be omitted. There are product_i a_i such choices. We have proved
D_F(c)=sum_{S subset E(F)} c^|S| product_{C component of (V,S)} |C|.

The top coefficient, c^(n-1), is n, since S=E is the only full-edge subset. For n>=2 the next coefficient, c^(n-2), is sum_e a_e(n-a_e), where the two components after deleting e have sizes a_e,n-a_e. A pair of distinct vertices is separated by e iff e belongs to its unique connecting path. Counting pair-edge incidences in these two ways shows that this coefficient is precisely
W(F)=sum_{unordered distinct {u,v}} d_F(u,v).
This W is the unordered index, unlike the ordered W printed in Csikvari-Lin Definition 4.11.

For n>=3, D_U-D_T is a polynomial nonnegative for every positive c, its c^(n-1) coefficient cancels, and its c^(n-2) coefficient is W(U)-W(T). Dividing by c^(n-2) leaves this coefficient plus finitely many negative powers of c, tending to zero. The limit of nonnegative real numbers is nonnegative. Thus W(U)>=W(T). At n=2 both trees are isomorphic to one edge, and W=1; equivalently the constant next coefficient is 1. At n=1 W=0. No coefficientwise domination at every lower degree, strictness, converse or isomorphism conclusion is inferred.

## 4. Independently identify the literal random-walk mean

For a finite tree with n>=2 put Delta=max degree>=1 and D=n-1. From every state there is a simple path to a specified target of length <=D, each transition with probability >=1/Delta. Hence the probability of hitting the target within D steps is at least p=Delta^(-D)>0. Conditional on failure in one D-block the same bound applies from the new state. By induction P(tau>kD)<=(1-p)^k, and E tau<=D/p<infinity. Periodicity is irrelevant: hitting within a block does not require arrival at its end. This proves almost-sure absorption at each specified target and finite expectations, rather than presuming recurrence or optional stopping. The discrete strong Markov identity at a finite hitting time follows by conditioning on its countably many possible times and using the ordinary finite-state Markov property; nonnegative sums justify passage to expectations, now finite.

For adjacent a,b let A be the a-component of F-ab, of size s. Root A at a with b as its external parent. For each v in A, let s_v be its descendant subtree size and h_v the expected time from v to its parent. A leaf has h_v=1. If v has d children, all d+1 neighbors are its children or parent; first step and strong Markov on the necessary return from a child give
h_v=1+(1/(d+1)) sum_children (h_child+h_v).
Multiplying and subtracting d h_v gives h_v=d+1+sum h_child. Induction using s_v=1+sum s_child yields h_v=2s_v-1. In particular H(a,b)=2s-1. Only motion inside A is possible before crossing ab, so no discarded transition is present in this recurrence.

For u=v the hitting time is zero. For u!=v, in a tree any walk to v must hit the successive vertices of the unique u-v path in order; applying the same finite strong Markov decomposition repeatedly gives H(u,v) as the sum of adjacent crossing expectations along that path. In the reverse path the component sizes on each edge sum to n. Thus each edge contributes (2s-1)+(2(n-s)-1)=2(n-1) to H(u,v)+H(v,u), proving
H(u,v)+H(v,u)=2(n-1)d_F(u,v).
Summing over unordered pairs, with diagonal zero, gives
alpha(F)=2(n-1)W(F)/n^2.
Since the prefactor is positive for n>=2 and the sizes agree, W(U)>=W(T) gives alpha(U)>=alpha(T), with exactly the required order. Equality is permitted throughout. At n=2 both means are 1/2. At n=1 the separately stated absorbing extension yields zero. This proves the full substantive source-defined statement for every pair and every finite simple target hypothesis, with no unpaid ordinary bridge found.
