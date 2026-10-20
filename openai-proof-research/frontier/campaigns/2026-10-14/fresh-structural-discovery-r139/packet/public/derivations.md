# Connected switch fibers: a sharp local estimate and the remaining global step

Research support by Codex / GPT-6 Astra / high / default service tier, explicitly authorized for r139. Original prose CC BY 4.0; original code MIT. This is PREFREEZE support, not a frozen full-target author-proof nominee or an independent mathematical verdict. No upstream theorem or proof operation is audited. All source uses are at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## 1. Scope retained and source interfaces

The investigation is the arbitrary-degree connected realization problem considered, without a freeze, in structural r30. Let n>=4, let d be any labelled simple degree vector having at least one connected realization, and let Omega_c(d) be ALL those connected realizations on [n]. No restriction on leaves, minimum degree, density, or regularity is introduced. The contemplated full operation is a uniform polynomial worst-start mixing bound for the source's half-lazy four-vertex switch proposal, rejecting a proposed switch if it disconnects the graph. No such bound is proved here. Nothing below replaces that problem by a special family.

For each vertex pair a, record all edges outside a, the edge within a, and every outside vertex's number of neighbors in a. Source131 `eq:pair-operators` defines its averaging projection E_a and h_a=I-E_a on the unrestricted graph space. On Omega_c use the same recorded data, but average only the connected states in each fiber: write E_a^c, h_a^c, and H_c=sum_a h_a^c. Let L_c be the unnormalized Laplacian of distinct connected-switch neighbors, counting each neighbor once. All graph inner products below use the uniform law on Omega_c.

The source's full `row:variance`, `tri:gap`, `dis:interaction`, `sl:comparison`, `dis:nonnegative`, and `mix:H-square` operate on unrestricted conditional laws. Those operations are paid in their stated domain. They are not assertions about the changed conditional law. The source's `mix:comparison` counts each switch in exactly two pair fibers; this incidence count does survive connected rejection. The matching companion's `cor:prescribed-degree` and constant-fiber Tutte construction cover arbitrary unweighted hosts but do not impose connectivity or control the present transition kernel.

## 2. Exact local support, with the r30 contribution credited

A pair fiber has N singleton-neighbor labels, of which exactly q attach to the first endpoint. If the endpoint edge is present, or an outside vertex is adjacent to both endpoints, the endpoints are connected regardless of their assignments. Provided the fiber contains a connected state, every outside component has a fixed attachment, so the entire q-subset slice is permitted.

Otherwise the components of the fixed outside graph partition the N labels into nonempty blocks B_1,...,B_t. A q-subset S is permitted precisely when it splits at least one block:

    A = {S subset [N]: |S|=q, some j satisfies 0<|S intersect B_j|<|B_j|}.

A mixed component joins the two endpoints, and every other component attaches to one of them. If no component is mixed, the two sides remain disconnected. This characterization is r30's paid supporting work. Its failure of matroid exchange does not preclude a spectral estimate.

Every block partition in this display is realizable as an actual graph fiber. Make the labels in each B_j into a path in the fixed outside graph; attach each label once to one of two new endpoints, with q labels at the first endpoint. The outside degrees and both endpoint degrees stay fixed. Thus the following calculation concerns the full class of these fibers, including arbitrarily large ones.

## 3. A sharp deletion estimate on every such fiber

For a graph on subset states, its unnormalized Laplacian sums f(S)-f(T) once per adjacent state. Adjacent states differ by removing one label and inserting another. Denote the Johnson Laplacian on the full q-slice by J, and its induced Laplacian on A by J_A. Assume A is nonempty; necessarily N>=2 and 1<=q<=N-1.

Let b(S) be the number of Johnson neighbors of S outside A. Let s be the number of singleton blocks, and let t_* be the number of nonsingleton blocks. For S in A the following is an exact formula, not a union bound.

* If S mixes at least three blocks, b(S)=0: one exchange touches at most two blocks.
* If S mixes exactly one block B, write k=|B| and r=|S intersect B|. A forbidden neighbor is obtained either by removing the unique selected label of B when r=1 and inserting an unselected singleton-block label, or by inserting the unique missing label of B when r=k-1 and removing a selected singleton-block label. Thus b(S)=1_{r=1}s_0+1_{r=k-1}s_1, where s_0,s_1 count unselected and selected singleton blocks. The two cases both apply when k=2; their exchanges are distinct. Exchanging within B cannot make it unmixed, and touching any other nonsingleton block would make that block mixed.
* If S mixes exactly two blocks B,C, a forbidden neighbor must remove the unique selected label from one and insert the unique missing label in the other. Hence

    b(S) = 1_{|S∩B|=1, |S∩C|=|C|-1}
         + 1_{|S∩C|=1, |S∩B|=|B|-1} <= 2.

Consequently b(S)<=D, where D=s if t_*=1 and D=max(s,2) otherwise. Since t_*=1 entails N-s>=2, and t_*>=2 entails N-s>=4 and N>=4, always N-D>=2.

The classical Johnson spectrum is r(N+1-r), 0<=r<=min(q,N-q); in particular its nonzero gap is N and its largest eigenvalue is at most floor((N+1)^2/4). These facts are paid by the actual Filmus slice-basis and transposition calculations, not new contributions here. For completeness, the eigenvalues can also be obtained without importing the full basis construction. On j-subsets let U lift by summing over (j-1)-subsets, and let D=U* lower by summing over containing j-subsets. Direct counting gives, on (j-1)-subsets,

    D_j U_(j-1) - U_(j-2) D_(j-1) = (N-2j+2)I,

and on j-subsets,

    J_j = j(N-j+1)I - U_(j-1)D_j.

For j<=N/2 the first identity makes U_(j-1) injective: its squared norm dominates (N-2j+2) times the squared norm of its input. The space decomposes orthogonally as im(U_(j-1)) plus ker(D_j). The second identity gives eigenvalue j(N-j+1) on the kernel. Equivariance under label transpositions gives J_j U_(j-1)=U_(j-1)J_(j-1), so the preceding eigenvalues lift. Start with j=0 and use complementation for j>N/2. This proves the claimed full spectrum and constants; no new spectral theorem is claimed.

Now take any function f on A with sum_A f=0, and extend it by zero to the deleted states. The extension has zero full-slice sum. In counting-measure normalization,

    sum_{edges inside A}(f(S)-f(T))^2
      = <f_tilde,J f_tilde> - sum_{S in A} b(S) f(S)^2
      >= (N-D) sum_{S in A} f(S)^2.

Dividing by |A| gives the uniform-measure statement. It proves

    J_A >= (N-D)(I-E_A) >= 2(I-E_A).                 (1)

In particular the induced graph is connected: a nonconstant function constant on each component would have zero energy and positive variance. There is no assumption of matroid structure or dependent negative correlation.

The bound 2 is sharp at every N>=2, for every 1<=q<=N-1. Use one two-element block and N-2 singleton blocks. A state selects exactly one of the two special labels, together with q-1 other labels. The induced graph is the Cartesian product K_2 square J(N-2,q-1), with singleton factors interpreted in the usual way. The function which is +1 or -1 according to the selected special label has J_A f=2f. Equation (1) supplies the matching lower bound. This family is realized by the outside-edge construction above; its connected realizations are trees. It is an all-size equality mechanism, not an inference from a finite census.

There is also an upper operator bound. The principal submatrix of J on A is J_A+diag(b). It is bounded above by the full operator norm of J. Since J_A kills constants, subtracting the A-mean yields

    J_A <= floor((N+1)^2/4)(I-E_A).                 (2)

The same lower bound 2 and upper bound hold on a nonconstant full slice; constant fibers have both operators zero.

## 4. Integration into the actual connected switch chain

Let J_a^c be the fiberwise induced Laplacian just analyzed. A connected switch lies in exactly two pair fibers, namely the two parts of its alternating four-cycle. Both endpoints are in the same connected conditional fiber in each representation. Conversely each allowed singleton exchange is precisely such a connected switch. The source's incidence count therefore gives

    sum_a J_a^c = 2 L_c.

Here N<=n-2 for every fiber. Summing (1) and (2) proves the two-sided inequality

    H_c <= L_c <= [floor((n-1)^2/4)/2] H_c.         (3)

This is a fully proved, uniform comparison at the arbitrary-degree scope, not a claim that either operator has a polynomial spectral gap. In particular their kernels agree. Carstens--Kleer's local heat-bath comparison already supplies the general principle; the new supporting calculation is the explicit control of the connected fiber after deletion.

The source's half-lazy proposal, with disconnected results rejected, satisfies exactly

    I-P_c = L_c / [12 binom(n,4)].                 (4)

Thus the remaining full mixing operation can be stated without a local-sampling debt: prove absolute C,K such that for ALL the original n,d and all f,

    Var_(Omega_c)(f) <= C n^K <f,H_c f>.           (5)

Equations (3)--(4) would then give gap(P_c)>=[12 C n^K binom(n,4)]^-1 and the usual worst-start bound using |Omega_c|<=2^binom(n,2). Equation (5) is UNPROVED here. This implication is only an exact description of the debt; it is not a nominated conditional finding.

## 5. What connectivity does to a complete three-row cell

Fix a triple T={0,1,2}, its outside graph, and every outside vertex's number of neighbors in T, exactly as in source `tri:gap`. Let C run over components of the outside graph, and let t_C be the fixed total number of attachments from C to T. If t_C=0 the cell has no connected states. Otherwise form a graph Q on T: include internal edges, and join each pair of terminals which both attach to a common C. Contracting each connected outside component proves that the original graph is connected exactly when Q is connected.

For three terminals, Q is connected exactly when it has no isolated terminal. Let r_i(C) be the attachment count from row i to C, and let s_i be its internal degree. Row i knows s_i from its prescribed degree and external row sum, including the source's extra-column convention. Terminal i is isolated precisely when

    s_i=0 and r_i(C) in {0,t_C} for every C.

Consequently the connected law in this cell is the source's complete fixed-margin three-row law multiplied by three explicit zero-one row factors and normalized. The factorization is exact. It does not establish the source's three-row variance inequality for this tilted law. For a disjoint-pair cell there are four terminals; having no isolated terminal no longer characterizes connectivity, so this particular three-row reduction does not silently handle the disjoint sum.

## 6. An exact all-scale failure of the unchanged triangle constant

This is an obstruction to one transfer, not to global connected mixing. On six vertices, take degree vector (3,2,1,3,2,1), T={0,1,2}, outside edge 34, and outside-to-T counts 2,1,1 at vertices 3,4,5. The source's internal-edge count is one. Enumerating that edge and the three external column choices gives exactly eight states. Exactly seven are connected. Below each row lists its five additional edges besides 34:

    A: 03 04 05 12 13       B: 02 03 05 13 14
    C: 02 03 04 13 15       D: 01 04 05 13 23
    E: 01 03 05 14 23       F: 01 03 04 15 23
    G: 01 03 05 13 24

The deleted state has additional edges 01 03 04 13 25 and components {0,1,3,4} and {2,5}. The connected pair-fiber partitions are exactly

    01: {A,B,C}, {D,E,F}, {G};
    02: {A,D,G}, {B}, {C}, {E}, {F};
    12: {A}, {B,E,G}, {C,F}, {D}.

These partitions specify H_T^c=sum_{a subset T}h_a^c completely. Under the involution A<->D, B<->E, C<->F, G fixed, the antisymmetric space has matrix with diagonal 5/3 and off-diagonal -1/3, hence eigenvalues 1,2,2. The symmetric vector (1,-1,0,1,-1,0,0) has eigenvalue 4/3. On the remaining symmetric space (x,x,y,x,x,y,z) the matrix is

    [ 2/3  -1/3  -1/3 ]
    [-2/3   2/3    0  ]
    [-4/3    0     4/3].

Its characteristic polynomial is t(t^2-(8/3)t+14/9). Therefore the FULL seven-state spectrum is

    0, (4-sqrt(2))/3, 1, 4/3, (4+sqrt(2))/3, 2, 2.

In particular the source's bound (H_T)^2>=H_T does not survive connected conditioning. A direct rational witness is f=(1,1,-3,1,1,-3,2), which has mean zero and satisfies

    <f,[(H_T^c)^2-H_T^c]f>_uniform = -8/21.

No floating-point eigenvalue is needed.

For every integer r>=0, append r new leaves to vertex 3, and freeze those edges in the outside graph of this triple cell. Give each new vertex degree one and change d_3 to 3+r. All new outside-to-T counts are zero. The complete cell still has precisely the eight old assignments, with precisely the same seven connected states and the same three averaging projections. Thus the eigenvalue and negative witness persist for every n=6+r. This proves an all-scale failure of the unmodified local triangle constant, not an asymptotically slow sequence of complete chains.

The automatic algebraic identity still reads

    H_c^2 = sum_T (H_T^c)^2 - (n-3)H_c + D_c,

where D_c is the ordered disjoint-pair sum. Replacing the source's sharp local constant by any fixed c<1 alone gives coefficient c(n-2)-(n-3), which becomes negative. The disjoint interactions might compensate, or a different global construction might work. Neither is ruled out or paid here. This is why (1)--(4), despite their full uniformity, do not close (5).

## 7. Strongest integrated comparison and disposition

Filmus supplies the full Johnson spectrum, not merely a weak subset-chain bound. Carstens--Kleer supplies the local-to-global comparison mechanism. Source131 supplies unrestricted uniform mixing and its entire overlapping/disjoint operator calculation. Feder--Guetz--Mihail--Saberi, Section 3.1, Lemma 1 and Theorem 2, supply a cycle-edge joining/retraction comparison when minimum degree is at least two. Their actual proof removes a cycle edge in each component, joins the components cyclically, and controls adjacent images by rotations and reorderings. That operation is compatible with the pinned unrestricted input in its stated regime; it is not dismissed because a different naive conditioning argument fails. It does not handle tree components with leaves by the same selection rule. The r30 all-state exponential-rarity calculation already explains why its polynomial-fiber contract cannot simply extend to every degree sequence. That calculation is credited, not repeated as new support.

The original r30 arbitrary-degree connected question remains unchanged. The weighted full target W of I77 and the forbidden-matching-host augmented target D3 are distinct and remain unchanged; neither is inferred from the present unweighted connectivity calculation. Family169 was abandoned as a new direction on reading the actual prior full-U scope. The thin-tree problem is untouched.

The new deductions are the sharp all-size fiber deletion estimate, its exact two-sided connected-chain comparison, the row-factor form of the true conditioned triple law, and the all-scale exact triangle calculation. They are supporting author mathematics. No proof-feasible full new substantial operation emerged after the strongest compatible reductions. Therefore this packet remains PREFREEZE/no nominee. No correctness, contribution, acceptance, count, formalization, manuscript, or release gate is assigned. There is no claim of worldwide novelty, current open status, impossibility, or exhaustion.
