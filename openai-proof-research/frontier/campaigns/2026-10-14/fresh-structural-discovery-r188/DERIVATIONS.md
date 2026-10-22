# Structural r188: sustained prefreeze construction

These are feasibility derivations, not a frozen theorem or an author-proof nominee. The complete canonical source text and the operative primary and original-history spans listed in INTERFACES.md were read before this extended writeup. The proposed construction concerns only the fixed Ara--Henry coherator category A=Mod(C). All source operations are stipulated true. No mathematical grade is claimed.

## 1. The operation being tested

The working direction is a full-theory reflexive cylinder construction, natural in every model, with exact compatibility of its collapse with EVERY freely adjoined operation. A compatible natural constant-path map would allow the source's expansion argument to start at arbitrary models, without choosing a section by cofibrancy. The point is not to rename the proved homotopy hypothesis or simply to assert a full model structure. We construct the strongest available representing objects and identify a precise further lifting problem. No full-scope conclusion is nominated unless this further problem closes.

Write I={partial D_j->D_j}, J={D_j->D_(j+1)}, W for the exact-boundary weak equivalences. The source proves I-inj=W intersect J-inj, all objects fibrant, and the canonical left semi-model structure. Cofibrant means a retract of a cellular object; it is not synonymous with arbitrary model.

## 2. An unrestricted cellular splitting tool after the source theorem

After the source theorem has been proved in all dimensions, its upper-cell argument can be used with ALL dimensions. If i:U->V is an I-cofibration, U cofibrant and i in W, factor it by the ordinary J-small-object argument as U --a--> Z --p--> V. The map a is a J-cell map with cofibrant source, hence in W by the source. Thus p is in W intersect J-inj=I-inj. The lift against i gives s:V->Z, si=a, ps=id. Every J-attachment has a unit retraction. Transfinite recursion gives t:Z->U, ta=id, so ts retracts i.

Moreover, pushing this retract diagram out along U->U' with U' cofibrant makes i' a retract of a J-cell map with cofibrant source U'. Thus i' lies in W. This is available for arbitrary attaching maps, not only generators. It does NOT say that a pushout into a noncofibrant U' is in W; that would be the very extra assertion under investigation. All receiving objects used below are cellular.

## 3. Removing the cutoff and strengthening the joint endpoint: a paid construction

There is no need to force compatibility among the source's different q-cutoffs merely to obtain a path functor on full models. Once the all-dimensional source theorem is paid, its representing-object construction can be performed directly in A.

Take n=0. Put P_0=D_1 with its two vertices, and define, successively,

  A_j^01=P(partial d_j) amalgam_(partial D_j + partial D_j)(D_j+D_j),
  A_j^epsilon=P(partial d_j) amalgam_(partial D_j) D_j.

For j>0, factor A_j^01->1 by the small-object argument using I_k, k>0, obtaining A_j^01->P_j->1. All P_j and boundary objects are cellular. The source's skeletal formula is valid without a cutoff, since it is a colimit universal property. The initial whisker object H_0(S) is contractible: its dimension-one spine is a finite tree; the original tree argument is now justified by the already-paid J_1 expansions, and the remaining shape is built by higher J attachments. The same induction as the source gives A_j^epsilon and P_j contractible, and A_j^epsilon->P_j a cellular W-map. The splitting tool gives its retraction. For every finite pasting shape S, the exact skeletal filtration consequently makes P(S) cellular and contractible.

For each theory generator theta:D_j->F(S), use the already-interpreted faces and the two endpoints to define A_j^01->P(S). Since P(S) is contractible, extend across A_j^01->P_j. For n=0 every generating output j>0 is in this range. Follow the original free theory order, including composite face operations, and choose the representing maps once. This defines a functor P:A->A by (PY)_j=Hom(P_j,Y). Both endpoints p_epsilon are model morphisms. Their individual I-lifting problems are solved using the retractions A_j^epsilon<-P_j, also at j=0 by the unit retractions D_0<-D_1. Hence p_0,p_1 are I-injective for EVERY Y.

There is a useful further calculation. For every j>=0 put

  B_j=P_j amalgam_(D_j+D_j)(D_(j+1)+D_(j+1)),

using the two endpoints of P_j and source inclusions of the added disks. The map P_j->B_j is two J_j attachments, so B_j is cellular and contractible. The map B_j->A_(j+1)^01 is the pushout of A_j^01->P_j that attaches the MISSING TARGET cylinder. Indeed partial d_(j+1)=d_j amalgam_(partial d_j)d_j; the source cylinder is already present, the target cylinder's lower faces and its two endpoint j-cells are already prescribed. Their union is exactly A_j^01. For j=0 this is the attachment D_0+D_0->D_1 between the two target vertices. No shared face is duplicated.

Consequently B_j->P_(j+1) is cellular, and both its ends are contractible. The splitting tool gives a retraction P_(j+1)->B_j. A J_j lifting problem for (p_0,p_1):PY->YxY is precisely a map B_j->Y; precomposition with this retraction solves it. Thus the pair lifts ALL J_j, not just J_0.

This is a complete nonreflexive path construction, natural in all Y, with both endpoints trivial fibrations and the joint endpoint a fibration. It is a consequence of the source's actual geometry and the usual lifting/retract operations, consistent with Henry--Lanari Proposition1.16. It is explicitly paid, not a nominee. In particular, neither removal of q nor construction of all operation interpretations remains the unpaid issue.

## 4. Exactly why this does not finish the proposed operation

A globular collapse c_j:P_j->D_j can be chosen compatibly on faces and endpoints. Inductively the prescribed boundary and two endpoint maps assemble to A_j^01->D_j. Contractibility of D_j extends over the cellular map A_j^01->P_j. At j=0 use a unit D_1->D_0. This gives a map of coglobular diagrams c and c_j e_epsilon=id.

However, making s_Y:Y->PY a MODEL morphism is a different requirement. On an arity S define c_S:P(S)->F(S) by the colimit of the c_j. If the representation of theta is tilde(theta):P_j->P(S), the exact additional identity is

  c_S tilde(theta) = theta c_j.                         (R)

On an arbitrary tuple y:F(S)->Y, the two sides express respectively the operation evaluated on constant cylinders and the constant cylinder on the operation. Thus (R), for every generating theta and hence all composites, is precisely the missing algebraic naturality of s. It is not an optional normalisation of the endpoints. The ordinary extension into contractible P(S) in Section3 imposes boundary and endpoint equations but not (R).

The fully specified lifting problem is

  A_j^01 --b_theta--> P(S)
     |                   | c_S
     v                   v
    P_j ----theta c_j--> F(S).                         (L)

Its commutativity follows from (R) for earlier operations and c_S e_epsilon=id. A solution to (L) at every free stage extends the full-theory interpretation while preserving the collapse. At limit stages take the union; the original free order handles composite faces. This is an exact family of relative lifting problems, not an unspecified appeal to 'coherence'.

Lanari's Example6.3 already displays failure of constant-cylinder compatibility for a natural composition choice on his cylinders. It warns against simply declaring (R), but does not prove impossibility for this enlarged construction or for other choices. We claim no counterexample to the desired full operation.

## 5. A stronger relative completion: every disk collapse can be made a trivial fibration

One should not stop at the previous failure. Replace the representing cylinders with a genuinely relative construction. Starting with P(partial d_0)=initial, factor the fold

  A_0^01=D_0+D_0 -> D_0

by I-small-object factorization as A_0^01->T_0 --c_0-->D_0, where the first map is I-cell and c_0 is I-injective. Given T in lower dimensions and its compatible collapse, form A_j^01 using T and factor the prescribed collapse A_j^01->D_j as

  A_j^01 -> T_j --c_j-->D_j,

again with I-cell first map and I-injective second map. This is available algebraically without an all-object model structure. The objects can be infinite. The natural maps of coglobular diagrams e_0,e_1:D_bullet->T_bullet and c:T_bullet->D_bullet obey c e_epsilon=id strictly. Each T_j is contractible because c_j is I-injective and D_j->1 is I-injective. Each T_j is cellular, by induction on the globular boundary construction.

We can prove substantially more than objectwise contractibility. For every finite globular set K and each epsilon,

  e_epsilon(K):F(K)->T(K)

is a cellular weak equivalence. Prove this together with A_j^epsilon->T_j by induction on j. For j=0, A_0^epsilon=D_0, and its map to T_0 is cellular and W by c_0 e=id. Suppose the one-sided maps in lower dimensions are cellular W-maps. The exact skeletal gluing formula expresses e_epsilon(K) for dim(K)<j as iterated pushouts of those one-sided maps, starting at cellular F(K). Section2 applies at every pushout, giving cellularity and W.

Now A_j^epsilon is the pushout of e_epsilon(partial d_j) along partial D_j->D_j. The receiving object D_j is cellular, so D_j->A_j^epsilon is in W. The map A_j^epsilon->T_j is cellular: attach the missing endpoint j-cell, then the relative completion. Its composite with D_j->A_j^epsilon is e_epsilon(d_j), which is W because c_j is W and c_j e_epsilon=id. Two-out-of-three gives A_j^epsilon->T_j in W. The skeletal formula now proves e_epsilon(K) for dim(K)=j. This closes the induction for all finite K, not just contractible shapes.

For a pasting shape S, T(S) is therefore contractible, and c_S:T(S)->F(S) is a split epimorphism and a weak equivalence, since c_S e_epsilon=id and e_epsilon in W. The source's original-order extension once again equips Hom(T_bullet,Y) with ALL model operations preserving endpoints. The joint endpoint lifts all J_j: use B_j=T_j amalgam_(D_j+D_j)(D_(j+1)+D_(j+1)); its source is contractible, it is two source attachments, and B_j->T_(j+1) is the same missing-target-cylinder cellular map. Its retraction gives the lift.

Thus this stronger construction pays, simultaneously:

- cellular representing cylinders and exact shared-face gluing;
- both individual endpoint trivial fibrations and a joint fibration on every model;
- a coglobular collapse whose EVERY disk component is I-injective;
- cellular weak-equivalence endpoints for every finite globular set;
- a weak-equivalence, split collapse on every pasting arity;
- full interpretation of the fixed coherator preserving endpoints.

It still does not establish (R). What is lacking is I-injectivity, or just the specific lifting property (L), of the ARITY collapse c_S after globular-sum gluing. Diskwise I-injectivity is not an asserted preservation theorem for these algebraic colimits. For S a globe, c_S is I-injective and (L) does close. For a general finite pasting arity it is a different map.

## 6. The first exact gluing interface and two unsuccessful repairs

Already for S=d_1 amalgam_(d_0)d_1 the relevant map is

  c_S:T_1 amalgam_(T_0) T_1 -> D_1 amalgam_(D_0) D_1.

It is a weak equivalence with two sections, and both c_1,c_0 are trivial fibrations. To prove c_S I-injective one needs, for every k, a prescribed parallel boundary in the left pushout and a k-cell in the right pushout with that projected boundary, an EXACT lift with the prescribed boundary. The tested boundary can involve arbitrary algebraic composites across both factors. The source's skeletal filtration controls weak equivalence of the endpoint inclusions into the left pushout. It does not prescribe the image under c_S of a filler in that object.

The strongest available approximate correction is explicit. Since c_S is W, prop:weak-test produces an exact-boundary cell z upstairs and a (k+1)-cell H:c_S z->y downstairs. If c_S lifted J_k, lifting H with source z would give a cell whose target is the exact desired lift. This is precisely the source lifting lemma. No such J_k lifting for c_S has been proved here. Contractibility of both objects only supplies H and some upstairs fillers; it does not prescribe their images.

A second repair is to factor each c_S separately by I-small-object factorization, making its replacement I-injective. That solves individual lifting problems but changes the arity object independently. It no longer proves

  T(S)=colim_(d_j->S) T_j,

the identity required to represent compatible tuples in the path model. In the displayed two-edge example, a new cell attached to that pushout is not automatically the colimit of compatible changes to the TWO T_1 factors and their COMMON T_0. Filling all arities independently is therefore not a completed model construction. One would need a simultaneous construction preserving these exact colimit identities, the endpoint latching cofibrations, the collapse and all previously interpreted free-stage operations. A formal small-object factorization in a category of arbitrary diagrams does not by itself preserve designated globular sums.

There is an explicit finite topological diagnostic against treating the missing permanence as a GENERAL model-category fact. Let the base span be [-1,0] <- {0} -> [0,1]. Over each interval take its product with the square [0,1]^2, with fibre coordinates (y,z), and over the middle point take [0,1]. Embed this middle interval in each endpoint square by y |-> (y,0). Each of the three vertical projections is a trivial Serre fibration, and all horizontal inclusions are inclusions of cubical subcomplexes. Choose two endpoint sections with (y,z)=(0,0) and (1,0); they agree with the two endpoints of the middle interval. The union of the two endpoint sections and the two boundary intervals in each cube is the boundary of its bottom square, again a cofibration. Thus even the relevant two-sided latching condition in these dimensions is respected.

The induced map from the pushout E of the TWO cubes glued along their middle interval to [-1,1] has two sections and is a weak equivalence. Explicitly, first shrink z to zero in both cubes; this homotopy fixes the glued interval and therefore descends. Then shrink y to zero; the result is the base section. But the projection has no path lift starting at the point x in the first cube with base coordinate 0 and fibre (0,1), for the base path gamma(t)=t, t in [0,1]. For every t>0 a lift must lie in the second cube. That cube is closed in the finite cubical pushout and its intersection with the first cube is only the gluing interval z=0. A continuous lift cannot start at x outside that closed second cube. Consequently the pushout projection fails even interval path lifting.

This is a concrete counterexample to a general colimit-preservation inference, NOT a counterexample to a globular coherator theorem: these are spaces, not the specific free C-models, and their topological product fibres do not establish failure of any c_S constructed above. It shows why an additional property of those exact algebraic arities must be proved, rather than citing a generic objectwise trivial-fibration or Reedy-cofibration argument. Neither attempted repair proves the sought stability false in A.

## 7. What closure would imply, with the whole argument retained

Suppose (L) can be solved for all the relative cylinders of Section5, coherently in the original free tower. Then c represents a natural model morphism s_Y:Y->PY with p_0s_Y=p_1s_Y=id. For any model X, any n-cell a and its expansion i:X->Y, let r:Y->X be the unit retraction. Use the square

  X --P(i)s_X--> PY
  i |             | (p_0,p_1)
    v             v
    Y --(id,ir)--> YxY.

It commutes because s is a section of both endpoints. Since the right map lifts J_n, it lifts its pushout i. Let f:Y->PY be the resulting lift. Then p_0f=id and p_1f=ir. Both endpoints lie in W, hence f and ir lie in W. In the arrow category i:X->Y is a retract of ir:Y->Y using domain maps i,r and identity codomain maps. Thus i is W. This argument has NO cellularity assumption on X once s exists.

The argument even works with a natural single-endpoint section, or with a section chosen for each X, by retaining u=p_1h and the source's iu/iur retract calculation. Reflexivity is a concrete sufficient structure, not claimed logically necessary.

The all-model expansion assertion would imply the FULL canonical model structure: J-small-object factorization works on every map, all its J-cell left factors are W by transfinite closure, and I-inj=W intersect J-inj. For i in I-cof intersect W, factor i=pj, infer p in I-inj, and exhibit i as a retract of j. This gives the missing unrestricted lifting axiom. Conversely in the full canonical model structure, every J_n is a trivial cofibration (its domain is cellular and the source already proves W), so all its pushouts are W. Thus all-model expansions and this full canonical model upgrade are equivalent under the stipulated source; merely giving either as an alternative formulation is not a new bridge.

If the full model structure were known, functorial J-factorization of each diagonal would furnish genuine functorial path objects. Endpoints are fibrations because product projections are fibrations (every object fibrant), and are weak equivalences by their sections, so are I-injective. This confirms that abstract path-object factorization cannot be invoked here as if the desired upgrade had already been established.

## 8. Cofibrant resolution makes the remaining descent issue equally concrete

Choose an I-trivial fibration p:QX->X with QX cellular. Lift a:D_n->X to a_tilde:D_n->QX using I-injectivity (or cofibrancy of D_n). Form QY=QX amalgam_(D_n)D_(n+1) and Y=X amalgam_(D_n)D_(n+1). The top expansion QX->QY is W by the source, as is p. Therefore two-out-of-three in the commuting square shows

  X->Y is W  if and only if  p^+:QY->Y is W.

This is an exact reduction to descent of the trivial fibration through this particular algebraic pushout. It does not assume p^+ is a fibration. The source proves stability for the horizontal cofibrant-start expansion, not for this vertical pushout. Applying realization to a cofibrant replacement does not identify arbitrary actual algebraic pushouts with derived pushouts. Likewise, finitary presentations do not make arbitrary finitely presentable models cellular: relations in X can force matching equations that do not hold in a free cellular presentation. Replacing those equations by joining cells without proving compatible algebraic descent is not a solution.

## 9. Endpoint and scope

The strongest integrated construction includes full unbounded operation interpretation and joint lifting in every dimension, plus an improved relative completion with trivial-fibration disk collapses and split weak-equivalence arity collapses. The unclosed operation is the exact arity-wise lifting (L), equivalently a sufficient coherent collapse-preserving interpretation across the original free theory. The two-edge pushout and the exact-boundary correction specify where more than weak equivalence is required. The cofibrant-resolution square gives a separate exact descent formulation; its vertical equivalence is not proved.

No viable distinct full-scope theorem with this bridge closed has emerged. No statement is frozen and no conditional/restricted construction is offered as a substitute nominee. All-model expansion/full-model equivalence is recorded as a routine reduction, not as a result being claimed. The source's HH, semi-model structure, cofibrant expansions, contractible shapes, conventional changes and primary cylinder constructions are all credited. No claim of impossibility, exhaustive literature coverage, strictification, other coherator conventions, controlled-theory transfer, or an algorithmic bound follows.
