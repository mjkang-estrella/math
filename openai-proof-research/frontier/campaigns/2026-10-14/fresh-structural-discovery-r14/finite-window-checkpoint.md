# Checkpoint 2: what specialization actually supplies

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

These are supporting deductions, not a weakened replacement for FT2.
The substantial target remains the existential assertion with ALL degrees
and one fixed finite-dimensional algebra and module over F_2.

## 1. Arbitrarily long finite windows, with a proof

Accept pinned family 199's symmetric example over
K=F_2(q,H_1,H_2). Write a=dim_K A and m=dim_K M. For EVERY integer r>=1,
there exist a finite field k_r of characteristic two, a symmetric algebra
A_r of dimension a over k_r, and a nonprojective module M_r of dimension m,
such that Ext_{A_r}^i(M_r,M_r)=0 for 1<=i<=r.
The dimensions a,m over k_r are constant. The degree [k_r:F_2] is NOT
bounded here. This is ordinary spreading out plus finite linear algebra.

Choose bases for A,M and a symmetrizing linear functional t on A.
The algebra multiplication, unit, module action and t have finitely many
coefficients in K. Choose a truncated resolution by finite FREE A-modules

 P_{r+1} -> P_r -> ... -> P_0 -> M -> 0

exact through P_r. Such a prefix exists: each kernel is finite-dimensional
and hence finitely generated over A. Choose free generators for each step.
Only finitely many differential coefficients have now been introduced.
Choose a localization R=F_2[q,H_1,H_2,1/f] containing all these coefficients.
The displayed algebra, action, and differential identities over K also
hold over R, since R embeds in K.

We can further localize R to preserve every needed rank. For a matrix
with generic rank b, every (b+1)-minor is identically zero in R; inverting
one nonzero b-minor makes its rank exactly b in every residue field.
For b=0 nothing needs to be inverted. Do this for the augmentation and
all the underlying R-linear differentials. At P_j, j<=r, the generic
identity

             rank d_j + rank d_{j+1}=dim_K P_j

therefore holds in every fiber, with d_0 the augmentation. Together with
d_j d_{j+1}=0 and surjectivity onto M, it proves the needed exactness in
every fiber. The fiber P_j remains free over the fiber algebra. The
prefix can be extended to a full projective resolution in each fiber.

Since P_i is free, Hom_A(P_i,M) is a finite direct sum of copies of M.
Its differentials are matrices over R. Preserve their ranks by the same
minor operation. The generic equality

     rank delta^{i-1}+rank delta^i=dim Hom_A(P_i,M), 1<=i<=r,

then proves vanishing of the fiber self-Ext groups in that entire range.
No infinite resolution is specialized; only this finite prefix is used.

Symmetry persists after inverting det(t(b_j b_l)). The cyclic identities
for t persist because they are polynomial identities in the chosen
structure constants. This yields a symmetric, unital associative algebra
in every fiber of the resulting nonempty open set.

Nonprojectivity must also be retained; it is not implied merely by a
finite list of vanishing groups. Use the canonical free surjection
pi:A^m->M sending its free generators to the chosen basis of M.
A splitting is an A-linear section s satisfying pi s=id_M. These
conditions are a finite inhomogeneous linear system over R for the
entries of s. Over K it has no solution. If its coefficient matrix has
rank b, its augmented matrix has rank b+1. Invert a nonzero b-minor of
the former (if b>0) and a nonzero (b+1)-minor of the latter. All larger
minors vanish identically. The same rank gap then holds in every fiber,
so no splitting exists there. This proves nonprojectivity in every fiber.

All these inversions amount to one nonzero polynomial f in three
variables. A nonzero polynomial over an infinite field has a point where
it is nonzero: induct on the number of variables, then avoid the finitely
many roots of a nonzero polynomial in the last variable. Apply this over
the infinite field F_2bar. Its chosen three coordinates are algebraic
over F_2, hence lie in one finite field k_r. Evaluation off f defines
the required fiber. This completes the finite-window assertion.

## 2. Restriction to the PRIME field, with its precise dimension cost

If k/F_2 is finite and A is symmetric over k with symmetrizing form t,
then A, regarded as an F_2-algebra, is symmetric via

                       t_0=Tr_{k/F_2} composed with t.

Cyclicity is immediate. For a!=0 choose b with t(ab)=c!=0.
The trace pairing of a finite field extension is nondegenerate. Choose
lambda in k with Tr(lambda c)!=0 and replace b by lambda b.
Thus t_0 is nondegenerate. For completeness, the trace map is not zero:
for k=F_{2^e}, its polynomial X+X^2+...+X^{2^{e-1}} has degree less
than 2^e and is nonzero, so it cannot vanish on the entire field.
Multiplication by c!=0 is bijective, which proves the required pairing
claim without an assumption that Tr(1)!=0.

The underlying ring A and its modules are unchanged by forgetting the
named k-structure. An A-linear map is automatically k-linear because k
is a central subfield acting on every module. Projective modules,
resolutions, and the additive Ext groups are therefore the same.
The finite-window example becomes a symmetric F_2-algebra/module pair
with dimensions e_r a and e_r m, where e_r=[k_r:F_2].

Consequently the proved quantifiers are

 for every r, there exist finite A_r,M_r over F_2 with Ext^{1..r}=0,

NOT existence of one finite A,M with Ext^i=0 for every i.

## 3. Exact equivalence with an algebraic-closure witness

FT2 is equivalent to existence of a finite symmetric counterexample over
F_2bar. In one direction extend an F_2 witness. Ext commutes with field
extension because a finite free resolution has finite terms in each
degree, Hom commutes with tensor there, and field tensoring is exact.
Nonprojectivity is preserved: the finite linear splitting system above
has the same coefficient/augmented ranks over an extension field.
Symmetry is also preserved.

Conversely, an algebra, module, and symmetrizing form over F_2bar use
only finitely many coefficients. They are defined over one finite
subfield k. The same base-change isomorphism and faithful tensoring
descend all positive Ext vanishings to k. Nonprojectivity upstairs
implies nonprojectivity downstairs, since projectivity ascends.
The trace construction then gives a witness over F_2.

This is not the algebraic closure mentioned in the pinned paper: that
closure contains the transcendental q,H_1,H_2. There is no embedding of
F_2(q,H_1,H_2) into F_2bar fixing F_2, because q would become algebraic.

## 4. The uniform-dimension obstruction to the tempting compactness step

FT2 is equivalent to the following statement: there exist integers A_0,M_0
such that, for EVERY r, a finite-window pair over F_2 can be chosen with
algebra dimension <=A_0 and module dimension <=M_0.

Forward implication: reuse an FT2 witness. For the reverse implication,
there are only finitely many algebra/module structures on vector spaces
with these bounded dimensions: a multiplication table and action use
finitely many binary entries. Restrict to the finitely many pairs that
are symmetric and nonprojective. If each has a positive self-extension,
take the maximum of the first such degrees over this finite set.
A finite-window witness at that maximum is impossible. Hence one pair
has all positive self-extensions zero, proving FT2.

No such uniform dimension bounds were obtained from Section 1. One
cannot use Noetherianity to turn a descending sequence of nonempty open
conditions into a closed point in their infinite intersection. The
nonempty opens

             q!=0 and q^j!=1 for 1<=j<=r

in the q-line over F_2 have a common generic/transcendental point, but
the intersection contains no F_2bar point. This is exactly the kind of
infinite-order condition already present in the source. Model-theoretic
compactness or an ultraproduct would permit an infinite coefficient field;
it does not give a finite-dimensional F_2-algebra.
