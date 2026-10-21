# r155 integrated calculations and exact remaining boundary

PREFREEZE / no nominee. These are exploratory calculations and a strongest-input comparison, not a frozen theorem or author-proof submission. No correctness, contribution, acceptance, or count is assigned. The one developed family is Source169 chromatic quasisymmetric functions, prescribed-demand multicolorings, and their existing heap-component refinement. Elementary unimodality U is not reopened. All old frozen scopes/dispositions remain unchanged.

## 1. Full prescribed-demand reduction is paid

Use the notation of note01. Zero demands can be retained or their vertices deleted; induced ordered subgraphs remain natural unit interval graphs. N=0 gives the constant1. All other arguments allow arbitrary finite nonnegative r, including repeated letters and disconnected graphs. No unary restriction or special graph class is being offered as a substitute.

Fix a Source169 triangular embedding of G, enlarged so D>=N, and put u_r=sum_i r_i a_i. In the graph quantum torus let E_k be the independent-set sum and Y its commuting symmetric alphabet. At a finite number s of colors expand

    product_(c=1)^s (sum_k x_c^k E_k).

A contribution at X_(u_r) chooses an independent set I_c for each color, with each vertex i in exactly r_i of these sets. No I_c can contain a vertex twice. Thus these contributions are exactly proper set colorings of demand r. For each edge ij there are r_i r_j pairs of colors and all pairs are unequal. In increasing color order the torus exponent is 2 inv - M_r, where M_r=sum_(ij edge) r_i r_j. This proves the generalized coloring-kernel identity, first in s variables and then in the stable limit:

    F_(G,r)(X;v^2) = sum_(lambda |- N) v^(M_r)[X_(u_r)]m_lambda(Y) e_lambda(X).       (1)

The left side initially uses color inversions. Commutation of the E_k makes it symmetric; finite color reversal then identifies ascents and inversions and proves reciprocity about M_r/2. This is compatible with Hwang's exact definition/proposition and clone formula. Symmetry is not being inferred from positivity of a nonsymmetric coloring expression.

The decisive source statements tri:domination and tri:monomial apply to every partition and every vertex exponent, not only squarefree ones. They yield

    m_lambda(Y)=Theta_(sum lambda_i d_i),
    (N!/product lambda_i!) Theta_(sum lambda_i d_i) <= U^N,  U=E_1,             (2)

in the coefficientwise positive torus order. Therefore (1) has nonnegative integral Laurent coefficients before the v-to-q conversion. On the other hand its ordinary elementary coefficients lie in Z[q], with q-degrees between0 and M_r: use the integral elementary basis in at least N variables on the actual coloring polynomial. Hence the Laurent powers have the requisite parity and become nonnegative q coefficients. This pays the ENTIRE prescribed-demand coefficient positivity statement by the operative source proof. It is not a substantial new operation.

Hwang2208.09857v2, Remark multi-chrom, independently supplies

    X_(G^r)(X;q) = (product_i [r_i]_q!) F_(G,r)(X;q),                         (3)

where G^r replaces i by an ordered r_i-clique, with complete joins over old edges. For a fixed set coloring, assigning its r_i distinct colors to labeled clones contributes the usual inversion enumerator [r_i]_q!; cross-edge contributions do not depend on this assignment. G^r remains natural unit interval. Marberg2312.16474v4 explicitly uses (3) for its pair-ascent Kromatic refinement. A failed attempt to infer positivity by division alone would not survive the stronger reduction (1)-(2).

Summing (1) over all positive r gives ordinary degreewise e-positivity for the pair-ascent set-valued series; each total degree has only finitely many demands. This is another compatible composition, not a K-theoretic-basis assertion. The complete-graph and Grothendieck e-type bases are different, and the primary literature warns that their positivity can fail. No K-basis positivity is proposed.

## 2. Repeated input letters do not leave a new witness gap

Let W_r be words with exactly r_i copies of letter i. For w in W_r define

    P_G(w)={j: w_j<w_(j+1), {w_j,w_(j+1)} not an edge},
    inv_G(w)=#{p<q: w_p>w_q and {w_p,w_q} an edge},
    A_(G,r)={w in W_r: P_G(w) is empty}.

Equal letters contribute neither strict ascent nor inversion. In a packet required to have nonedge ascents at its internal positions, all letters are distinct and form an increasing independent set. Conversely every independent-set packet gives those required ascents. Repetition can occur between packets, precisely as in the generalized kernel.

In source section06 replace N=n by N=sum r_i and u by u_r. The interval Nd_1<=y<=u_r remains finite in the same free root cone; R=u_r-Nd_1 has nonnegative root coordinates. The packet switches depend on exponent, energy, packet size and decoration, not on squarefreeness of the total exponent. Positive and negative individual packet directions are both retained, even when the total jump is zero. Their finite-rank bijections remain literal bijections of unlabelled independent-set packets; no quotient of labeled-clone matchings is required.

All common histories still depend on (chamber,y) rather than the chosen packet composition. At pure anchor labels, return-to-anchors works for repeated multiplicities exactly as stated in route:return. The new instance of (1)-(2) supplies the finite degree range -M_r,-M_r+2,...,M_r needed in route:parity. In the required-mask argument, the source domain is now W_r; required masks still encode the same independent packets. Its finiteness is N!/product r_i!, and target energy slices are finite by the source proof.

The source alternating-path cancellation passes from required masks to exact masks unchanged: nested calls strictly enlarge the mask; the outer alternating walk is an endpoint path in a finite union of two matchings. At exact empty mask there is one weakly decreasing anchor word for each terminal partition, even with repeated parts. Consequently the same construction supplies a terminating partition assignment Lambda_(G,r) with

    F_(G,r)(X;q)=sum_(w in A_(G,r)) q^(inv_G(w)) e_(Lambda_(G,r)(w))(X).       (4)

This is a compatibility calculation for the existing source algorithm, not a new algorithmic complexity result. The arbitrary local ranks need not coincide with the original witness run on a labeled-clone permutation. Neither that orbit-equivariance nor a polynomial runtime is required for (4). No source algorithm was implemented or runtime theorem tested in the finite diagnostic.

A direct insertion calculation checks the total witness mass. Put L_a=sum_(b<a, ba edge) r_b. Deleting all copies of the largest letter a from an admissible word leaves an admissible word. If a nonempty a-run had predecessor b, b must be an earlier neighbor. For any new consecutive pair b<c after deletion, interval closure gives bc an edge because b is adjacent to a and c<a. The only insertion slots for a-runs are before the word and after each earlier-neighbor occurrence. Their inversion contributions per inserted copy are L_a,L_a-1,...,0 in their order. Distributing r_a indistinguishable copies among these L_a+1 slots gives the Gaussian polynomial. Thus

    sum_(w in A_(G,r)) q^(inv_G(w)) = product_a Gaussian(L_a+r_a,r_a)_q.      (5)

This is the repeated-letter version of the source insertion digits; it is not evidence of a nonroutine contribution. It includes L_a=0, r_a=0 and N=0. Reversing words exchanges ascent-free and descent-free conventions and complements inv to M_r; (5) is palindromic of degree sum_a L_a r_a=M_r.

## 3. The genuinely finer existing question and its exact algebra

Hwang's original local-flip question is finer than (1)-(4), not a new conjecture identified here. For a natural unit interval order P (i<_P j iff i<j is a nonedge), let

    A_P=Z< u_1,...,u_n >/I_P,

where I_P is generated by u_a u_c-u_c u_a for a<_P c and u_a u_c u_b-u_b u_a u_c for a<b<c with ab,bc edges and ac a nonedge. Including contexts, these binomial relations identify exactly the components C of Hwang's word graph of fixed content. The second displayed local move and its variant bca<->cab are equivalent using the first move. Because this is a monoid-congruence ideal, A_P has the word components as a free Z-basis: reduce a polynomial by summing its coefficients over each component. There is no torsion or division in that statement.

Hwang proves E_k^P commute modulo I_P by actual odd-path local flips; it is stronger than their scalar-torus commutation. Hence m_lambda^P=m_lambda(E_1^P,E_2^P,...) is defined in A_P. His noncommutative Cauchy proof gives

    b_(C,lambda)=[h_lambda]K_C = <m_lambda^P, sum_(w in C) w>.               (6)

The proposed full positivity would require b_(C,lambda)>=0 for EVERY finite P in this class, EVERY finite content r, EVERY word component C, and EVERY partition lambda of N. This was an exploratory compatibility question, never frozen as a candidate. It is Hwang's Conjecture3.10; BEPS2211.03967v2 explicitly identifies its own cj:m pos as the stronger (3+1)-free version. We do not reduce that larger published scope or claim to solve either version.

Strongest compatible positive inputs already include: Hwang's class-preserving commutation and Cauchy formulas; his noncommutative Schur tableau proof; the classwise grouped-by-length sink formula; all hook and two-column monomial-positive lifts; and the full-height recurrence. BEPS supplies a still finer P-plactic Schur lift and hook/two-column tableau constructions. No theorem below is based on pretending these operations are unpaid.

The scalar source map is

    pi(u_w)=v^(2 inv_G(w)-M_r) X_(u_r).                                   (7)

Both generators of I_P map to zero; for the cubic relation the two edge contributions cancel, and its nonedge endpoints commute. Hence pi is an algebra homomorphism from A_P after adjoining v. Under it E_k^P maps to the source independent-set E_k, so (6) aggregates to

    [e_lambda]F_(G,r)(X;q)=sum_C b_(C,lambda) q^(inv(C)).                    (8)

The source proves positivity of every aggregated coefficient in (8). It does not state a positive lift of m_lambda(Y) to A_P. Extending the multiset packet proof does not supply one: its ranks are taken at a torus exponent/energy, and that indexing does not retain C.

## 4. Actual information loss, and a compatible edge-grading test

For h=(3,3,4,4), r=(1,1,1,1), the word components represented by1243 and2134 both have inversion1 but are different. Their h-functions are respectively h_4+h_(3,1) and h_4. This is a small explicit instance of the primary's stated refinement. In A_P their basis elements differ, while (7) identifies them. This does NOT refute positivity for either class, nor does noninjectivity alone rule out a special lifting theorem on m_lambda^P.

Try the stronger idea of giving each edge its own quantum degree, rather than stopping at loss under a single q. Let Omega_t(b,a)=t_ab on each a<b edge, zero on nonedges, with t in a free abelian parameter group. The independent-set E_1,E_2 must still commute if the source alphabet is to exist. On an induced increasing path a-b-c, the coefficient of X_(a+b+c) in their commutator is exactly

    v^(t_ab-t_bc) - v^(t_bc-t_ab).                                       (9)

There is only one independent pair among these three vertices, namely ac. The contributions of a and c to the total exponent are zero; the contribution of b to ac is t_ab-t_bc. Thus independent Laurent edge variables force t_ab=t_bc. This necessary condition already comes from the paid two-color commutation contract, before any wall positivity question.

For the five-vertex graph h=(2,4,4,5,5), the edges are12,23,24,34,45. Induced paths123,124,245,345 force ALL five edge degrees equal. Nevertheless the components represented by12354 and13245 are distinct, each has six words and inversion1. original/edge_grading.py enumerates their complete closed components and checks every allowed neighboring move stays within the claimed component. Both functions happen to be h_5+h_(4,1); their distinctness concerns component identity, not a negative coefficient. Both words therefore map to the same torus monomial even after every independent-edge grading allowed by (9). This defeats that specific recovery attempt at its full interface. It is not a universal obstruction to categorification, matrix coefficients, additional graph gadgets, or a different proof.

Adding separate commuting vertex weights does not help this loss: every word of fixed content gets the same product of vertex weights. Replacing vertices by cliques changes content and admits words with interleaved clones; no argument here isolates a prescribed original component through that operation. We did not mistake the all-content positivity in (1) for such an isolation theorem.

## 5. Stronger classical composition before stopping

The full-height recurrence is a real paid operation in A_P. If d=alpha(G), then m_lambda^P=0 for length(lambda)>d, and

    m_lambda^P=E_d^P m_(lambda-(1^d))^P  if length(lambda)=d.              (10)

It follows by multiplying ordinary symmetric polynomials and eliminating every term of length>d. Iteration strips full columns; for d<=2 this closes the entire component question using the already positive power sums. Hook/two-column/small-height rephrasings are therefore not residual nominees. For d>=3, (10) can leave a shape of length strictly between1 and d, so it does not close arbitrary shapes.

Even the next two-part case can be expressed without any new source gap. Hwang's sink formula gives p_k^P as a positive sum over unique-sink heaps. Since these power sums commute,

    m_(a,b)^P=p_a^P p_b^P-p_(a+b)^P               if a>b>0,
    2 m_(a,a)^P=(p_a^P)^2-p_(2a)^P.                                  (11)

The classwise right side counts ordered pairs of unique-sink heaps concatenating into C, minus unique-sink heaps in C. The divisibility by2 in the second formula is already an integral symmetric-function identity. A class-preserving injection paying the subtraction for all fixed sizes would establish this subcase, but none was obtained. It would not by itself prove all shapes. More generally, the partition-lattice Möbius formula expresses m_lambda as a signed combination of commuting p-products; it only reorganizes the missing cancellation and is not a proof of positivity.

The source domination bound (2) does not transfer merely from the identity

    U^N=sum_(lambda |- N) (N!/product lambda_i!) m_lambda^P.

Retaining one positive summand is legitimate in the scalar torus because source positivity was already established there. In A_P, retaining a summand would assume the unknown classwise positivity. Hwang's already class-preserving Schur expansion supplies additional constraints but is not a positive inverse change from Schur to h. No class-preserving wall factorization, arbitrary-shape cancellation, or positive component extraction was constructed.

## 6. Ending state

The fully paid result of this exploration is the arbitrary-demand kernel, q-factorial normalization, finite multiset witness and Gaussian insertion law, together with the primary's class algebra and its established positive subfamilies. These are credited compatible compositions. The local edge-grading calculation and finite component examples locate an interface failure in one possible lift; they are not nominated as a substantial obstruction theorem.

The exact unpaid obligation for the finer route is a nonnegative lift of m_lambda(Y) to m_lambda^P in EVERY heap-component coordinate, or an equally strong class-preserving cancellation, for arbitrary content and shape. The existing literature formulates this question already. This round supplies no new full proof, no closure of that obligation, and no evidence warranting a substantial nominee. There is no frozen statement to weaken. We do not submit ordinary multicoloring positivity, grouped sinks, hooks, two columns, height2, finite tests, a conditional lift, or elementary unimodality as replacements. No exhaustion, impossibility, novelty-to-literature or worldwide-priority claim is made.
