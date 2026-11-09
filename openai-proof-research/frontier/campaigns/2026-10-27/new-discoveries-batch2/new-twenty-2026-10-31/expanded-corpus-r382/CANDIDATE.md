# Ordinary candidate: MathDB 336969 — zero credit

All s>=1 and integers 0<=a,b<s with gcd(s,a-b)=1. For the literal source-defined core bipartitions C=C_(s|0,a) intersect C_(s|0,b), the arithmetic mean of |lambda|+|mu| is
(s+1)[a(s-a)+b(s-b)+1-s]/12.

Source bindings: arXiv:1709.00079, Conjecture 4.6, Proposition 4.4, Theorem 4.2 and its full proof, beta-set definition 2.4 and Remark in 2.3. Read source text lines 120–168, 190–285, 880–1075, 1190–1239. Current author accepted-manuscript copy, sources/cores-author.pdf, still states Conjecture 4.6 (text1172ff); exact PDF hashes in access inventories. This is an ordinary deduction, not a claim that the manuscript's underlying theorems were independently re-proved or formally checked.

## Parametrization, with normalization paid

First s>1. Put d=b-a, residues in Z/sZ. Let U be uniform among binary vectors of length s with exactly a ones, and V independently uniform among those with b ones. The equations
  y_i=x_(i+a)-a+s U_i=x_(i+b)-b+s V_i                 (1)
uniquely determine x,y up to a common additive constant because d generates Z/sZ. Indeed
  x_(j+d)-x_j=d+s(U_(j-a)-V_(j-a)).                 (2)
The increments around the cycle sum to sd+s(a-b)=0, so consistency holds. Choose the common additive constant to make sum x_i=s(s-1)/2; equation (1) then gives the same sum for y.

The resulting x_i are integers: starting with integral x_0, all x_i are integral and x_i-x_0 congruent i modulo s, hence their sum is congruent s(s-1)/2 modulo s. The normalizing translation is integral. The residues of x_i are i+C for a single integer C; y_i has the same residue i+C by (1). Relabeling index i to i-C makes x and y valid s-sets. Each s-set has distinct residues and normalized sum; by the source s-set/beta-set correspondence it is the s-set of a unique s-core. Proposition 4.4 makes the resulting pair lie in C. Conversely any pair in C gives the two binary vectors through (1), and all the choices producing it are simultaneous cyclic shifts. This is also the explicit bijection proved in Theorem 4.2, rather than an inference from its counting formula alone.

Every cyclic orbit of (U,V) has size s. If a shift of order t>1 fixes both vectors, t divides s,a,b, hence divides d, contrary to gcd(s,d)=1. Consequently uniform independent U,V, followed by forgetting the simultaneous shift, induces the UNIFORM measure on C, not a stabilizer-weighted measure. Sum x_i^2+sum y_i^2 is unchanged by relabeling. This is the required bridge for unweighted average size.

## Partition size from its beta-set

For a normalized s-set with entry z_i congruent i (0<=i<s), write z_i=i+s q_i. Then sum q_i=0. Its beta-set consists on runner i of i+s k for integers k<q_i, versus k<0 for the empty partition. The charge-zero beta-set size formula (sum of added beta numbers minus sum of removed beta numbers) gives
 |lambda|=sum_i [i q_i+s q_i(q_i-1)/2]
          =(sum_i z_i^2-sum_i i^2)/(2s).
For q_i<0 the same formula follows by subtracting the finite progression k=q_i,...,-1, so no positivity restriction was smuggled in. The beta-set formula itself follows by truncating both decreasing beta sequences below a common negative cutoff: lambda_j=beta_j+j and the j terms cancel. Equal charge ensures identical truncation lengths. In particular, with c=(s-1)/2,
 |lambda|=sum_i(z_i-c)^2/(2s)-(s^2-1)/24.          (3)
The same identity applies to y and mu. A normalized residue-complete set produces a beta-set of charge zero (sum q_i=0), bounded above with cofinite negative tail, so it indeed produces a finite partition; closure under subtracting s makes it an s-core. Thus this step does not replace a partition by an arbitrary rational vector.

## Exact second moments for x and y

Set W=a(s-a)+b(s-b). For a uniform weight-a binary vector,
 E U_i=a/s,
 Var U_i=a(s-a)/s^2,
 Cov(U_i,U_j)=-a(s-a)/(s^2(s-1)) for i!=j.
These follow from P(U_i=U_j=1)=a(a-1)/(s(s-1)); they include a=0. The same holds for V with b. Independence yields for Delta_j=d+s(U_(j-a)-V_(j-a)):
 E Delta_j=0, Var Delta_j=W, Cov(Delta_j,Delta_k)=-W/(s-1) for distinct j,k.
A sum along l consecutive edges of the d-cycle has mean zero and square mean
  l W-l(l-1)W/(s-1)=W l(s-l)/(s-1).             (4)
It equals x_(j+l d)-x_j by (2).

For any real vector x of mean c,
 sum_j(x_j-c)^2=(1/(2s))sum_(j,k)(x_j-x_k)^2.
For each l=1,...,s-1 there are exactly s ordered pairs at d-cycle distance l. By (4),
 E sum_j(x_j-c)^2
 = W/[2(s-1)] sum_(l=1)^(s-1) l(s-l)
 = W s(s+1)/12,                               (5)
since sum l(s-l)=s(s^2-1)/6.

It is necessary to compute mu as well; its correlation with lambda cannot simply be ignored. From (1) one derives
 y_(i+d)-y_i=d+s(U_(i+d)-V_i).                  (6)
The U coordinates have merely been cyclically shifted relative to V. Since the vectors are independent uniform fixed-weight subsets, these increments have exactly the same covariance table, so (5) also holds for y. No independence between x and y is asserted or required.

Adding (3) for both partitions and using (5) proves
 E(|lambda|+|mu|)=(s+1)W/12-(s^2-1)/12
                =(s+1)(W+1-s)/12,
the complete required formula.

For s=1, the only allowed a,b are 0,0, and the source explicitly defines C_(1|c)={empty bipartition}, notwithstanding the ordinary content-uniqueness convention at s=1. Its mean size and the formula both equal zero. If the target instead used unmodified uniqueness-of-content at s=1, that would require a separate semantic decision; the present candidate follows the explicit source convention required by MathDB's reference to source-defined C.

## Validation and qualification limits

No mathematical code, finite enumeration, numerical experiment, compiler, checker, API, Pi or delegate was used. The two independent marginal computations (2) and (6), charge normalization, cyclic orbit size, negative beta charges and s=1 are checked algebraically above. This is self-validation, not independent adversarial review. Source theorem dependencies remain explicit.

Source Conjecture 4.6 and its accepted-manuscript copy state the identical unweighted all-(s,a,b) formula. Source Theorem 4.2 counts the objects; it does not compute this average. Source Remark identifies a=0 with twice ordinary (b,s-b)-core size. That special case does not imply the independent two-subset formula for arbitrary nonzero a,b. Standard covariance tools do not alone establish either routine exclusion or significance. A full Johnson/Wang-to-target comparison remains a concrete priority/significance gate, not an assertion of new literature. Current registry direct access returned403 for a different target; registry searches for this target found no matching indexed claim, but no current full-tree/head clearance was obtained. Absence is not novelty evidence. Author manuscript header contains a DOI inconsistent with the journal citation; exact final journal identification/corrections should be checked before qualification.

## DORMANT bounded Pi certificate plan — DO NOT DISPATCH

After independent source/ordinary/prior/significance review only: implement source-exact finite partitions, beta-set core characterization including s=1 convention, normalized s-sets and Prop4.4 bridge. Prove the cyclic quotient bijection, free action and uniform-fiber size; prove the charge-size formula over integers including negative q; then finite subset first/two-point counts and rational finite-sum moments, both x and y recurrences, and final average identity. A fixed numerical instance or coordinate-only theorem is insufficient. Formal feasibility is substantial because the source bridge must be included, not axiomatized. Future literal endpoint quantifies all s,a,b as above and asserts finiteness/nonemptiness and totalSize = card(C)*formula over Q. Audit permitted axioms only propext, Classical.choice, Quot.sound; independent fidelity, clean extracted strict replay and root acceptance still required. No endpoint exists and no credit is requested.

## Post-derivation primary comparison update

Actual Johnson text810–867 and Wang105–151,628–664,770–795,895–930 have now been read. Wang Lemma4.10 contains exactly the quadratic s-set size identity used here. Its Proposition4.7 cyclic averaging and Theorem1.1 proof use a single weak-composition space; Johnson uses Ehrhart polynomiality for one simplex. This establishes concrete prior mechanism overlap, not a complete full-target exclusion. The product-of-two-subsets uniform orbit and both marginal transports are the additional target bridges; independent significance review must decide whether these are a full routine adaptation. No novelty qualification is claimed.

Current formal-conjectures root HTML was acquired at currentOid2055e5adadae0b2e392365938faa82ef6f1464f0; no full tree was read. Search caps reached3targetedbatches for336969; no more searches run. Direct GETs attributable to this route are primary,authorcopy,Johnson,Wang,andsharedregistryroot (5), within12. No registry absence or source's conjecture label is treated as clearance.
