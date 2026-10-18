# T205M: the sharp minimum multiplicity in a staircase square

Myeongjin Kang, no affiliation. Original prose CC BY 4.0; original code MIT.
Author-side complete proof submitted for independent proof and contribution
gates. No gate, acceptance, literature priority or campaign increment is claimed.
The exact all-order scope was frozen in `scope205m.md` on 2026-10-18 at
09:35:45 UTC, before completion of the uniform proof. Earlier exploratory
checkpoints remain historical. The campaign is currently 14/20 for unrelated
accepted work.

## 1. Theorem and proof package

For every integer m≥2, put N_m=m(m+1)/2 and ρ_m=(m,m−1,…,1).
For every partition λ⊢N_m other than (N_m) and (1^N_m),

    g(ρ_m,ρ_m,λ)
      =dim_C Hom_(C[S_Nm])(S^λ,S^ρ_m⊗_C S^ρ_m) ≥m−1.       (1)

The group acts diagonally. Equality holds at λ=(N_m−1,1), so the
constant is sharp. This is the full frozen ordinary complex tensor-square
scope. It does not assert a physical-flip refinement, an integral summand,
a characteristic-p result, or the same minimum inside the specified cyclic
module.

The complete proof consists of this document and the two included proofs
`kostka-low-capacity-proof.md` and `provenance/parent-high-capacity.md`.
The latter is an exact credited copy of a parent author-side construction,
not an independent gate. Their precise roles are given below. The finite
base calculations are specified mathematically in §7 and reproduced by
`verify-finite-proof.py`; the complete exact output is
`finite-proof-certificate.json`. None of the finite diagnostics replaces
the all-order arguments in §§4–6.

## 2. Source contracts, with the cyclic module retained

All pinned source statements are stipulated at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. We use the source
*A Cyclic Polytabloid Proof of Saxl's Conjecture*, not just ordinary
Saxl positivity. Let B_m={(i,j):i,j≥1,i+j≤m+1}, let v_R and v_C be its
specified row and column alternating block tensors, and put

    W_m=C[S_(B_m)](v_R⊗v_C) ⊂ S^ρ_m⊗S^ρ_m.

The following are the exact input contracts.

1. `dominance.tex`, Theorem `thm:cyclic-saxl`: every S^λ occurs in W_m.
2. `band-quotient.tex`, Proposition `prop:band-quotient`: for s=1,2 and
   h=m−s≥1 there is a surjection

       W_m ↠ Ind_(S_Nh×S_(Nm−Nh))^(S_Nm)(W_h⊠U_(m,s)).     (2)

   Its proof identifies the specified smaller generator and the entire
   induced module, using disjoint coordinate sectors. A quotient onto
   an unspecified submodule would not suffice here.
3. For s=1, U_(m,1) is the trivial module of S_m. For s=2,

       U_(m,2) ≅ ⊕_(η⊢2m−1, length(η)≤4) S^η.             (3)

   The generator-specific support is the odd-path proposition of
   `path-band.tex`. Its ambient two-row square is multiplicity-free with
   exactly these constituents, by Bessenrodt–Bowman, published Theorem7.11
   (the ordinary-square formula is credited there to Brown–van
   Willigenburg–Zabrocki). Thus support plus ambient multiplicity one
   identifies U itself. This bridge is already developed in I21; it is
   not a new band formula. For (5), only the source support inclusion of
   one copy of each four-row constituent is logically required; the
   multiplicity-free identification and its primary citation are a stronger
   credited antecedent, not an indispensable additional hypothesis.
4. The dominance construction supplies

       [W_m:S^λ] ≥ K_(λᵗ,ρ_m).                            (4)

   Here are its multiplicity details. The signed row-subgroup average
   produces v_R⊗u∈W_m with u nonzero and row-subgroup fixed. A sign
   intertwiner in the second factor sends this tensor to a nonzero
   multiple of z=v_R⊗v_R. Consequently a copy of Z=C[S_Nm]z lies inside
   W_m⊗sgn. The source pair-letter/content map Q sends z to c_m t_m,
   where c_m≠0 and the distinct translates of t_m form the word basis
   of M^ρ_m. Thus Z surjects onto M^ρ_m. Semisimplicity and Young's
   rule give (4), including multiplicities. I21 §2.1 further observes
   that the reverse coset-to-z map is injective because its composition
   with Q sends distinct cosets to distinct words; hence Z≅M^ρ_m.
   This exact module, sign reassociation and Kostka bridge are paid
   source/I21 operations, retained with their original hypotheses.

No assertion W_m≅W_m⊗sgn is made. Only the ambient square is sign
invariant, since S^ρ_m≅S^ρ_m⊗sgn.

## 3. Safe recursion and the asymmetric invariant

Write c_(ν,η)^λ for the ordinary Littlewood–Richardson coefficients.
Define R_1((1))=1. For m≥2 define R_m(λ) to be the maximum of

    1,
    K_(λᵗ,ρ_m),
    ∑_(ν⊢N_(m−1)) R_(m−1)(ν)c_(ν,(m))^λ,
    ∑_(ν⊢N_(m−2),η⊢2m−1,length(η)≤4)
          R_(m−2)(ν)c_(ν,η)^λ   (the last term only for m≥3).       (5)

Induction from (2)–(4) gives R_m(λ)≤[W_m:S^λ]. Separate quotient
bounds are maximized, never added. LR contributions within one induced
quotient are added, as semisimplicity requires. Ambient sign invariance
therefore gives

    g(ρ_m,ρ_m,λ)≥max(R_m(λ),R_m(λᵗ)).                     (6)

For h≥5 define the four exceptions

    E_h={(N_h),(1^N_h),
         H_h=(h,1^(N_h−h)), J_h=(h,2,1^(N_h−h−2))}.

We prove the stronger asymmetric invariant

    R_h(ν)≥h−1 for every h≥5 and ν⊢N_h outside E_h.         (7)

This invariant is genuinely about the cyclic lower bound. Replacing
R_h by the full smaller tensor-square multiplicity, or by the maximum
of its two orientations, would not be justified in (5).

The exact base calculation in §7 proves (7) at h=5,6 and the induction
step at m=7,8. It remains to prove the step at every m≥9, assuming (7)
at m−1 and m−2. We give the wide, narrow-high-capacity and
narrow-low-capacity cases separately, without changing the exception set.

## 4. Wide diagrams: λ_1>m

Exclude the one-row partition, which belongs to E_m. If λ is not a
rectangle, its horizontal m-strip predecessors are counted by

    [x^m]∏_i(1+x+⋯+x^(λ_i−λ_(i+1))).

At least two gaps are positive, and 0<m<λ_1. The coefficient is at
least two: a product of at least two nonconstant initial geometric sums
has every strictly interior coefficient at least two. Equivalently,
a bounded composition of an interior degree can be modified between
two nontrivial coordinates unless it is the all-zero or all-full one.

At least one predecessor lies outside E_h, h=m−1. If the row (N_h)
is a predecessor, Pieri forces λ to have at most two rows, and no other
exception fits. If the column is a predecessor, λ is a hook, whose two
predecessors have consecutive first-row lengths. They cannot both be
exceptional, since the exceptional hook widths are 1 and h≥6, and J_h
is not a hook. Otherwise the only way that all predecessors could be
exceptional is that H_h and J_h both occur. Their interlacing implies
λ_3≤1 and λ_2≤h. But

    ν'=(h+1,1^(N_h−h−1))

also interlaces λ: its first row is at most λ_1>h+1 and at least λ_2;
its second row lies between λ_2 and λ_3; all later entries agree with
J_h. This is a nonexceptional predecessor. The one-band sum in (5) is
therefore at least (m−2)+1=m−1.

If λ=(a^b), with a≥m+1 and b≥2, take

    η_1=(m+1,m−2), η_2=(m,m−1),
    ν_1=(a^(b−2),a−m+2,a−m−1),
    ν_2=(a^(b−2),a−m+1,a−m),

omitting zero parts. The rectangle-complement LR identity gives
c_(ν_i,η_i)^λ=1. Both ν_i are outside E_(m−2): when b≥3 their
first row is a>m−2 and they have at least two rows; when b=2 they
have at most two rows and are not rows. The only possible one-row
case would require a=m+1 and N_m=2(m+1), which forces m=4,
outside the induction range. Hence the two-band sum is at least
2(m−3)≥m−1.

## 5. Narrow diagrams with high capacity

Suppose λ_1≤m and C=λ_1+λ_2+λ_3+λ_4≥2m+1.
The included parent proof `provenance/parent-high-capacity.md` proves,
for every m≥7, that there are at least two distinct ν⊢N_(m−2)
outside E_(m−2) satisfying

    λ_i≥ν_i≥λ_(i+4) for every i.                         (8)

For clarity, its nonroutine combinatorial step counts rank-k ideals in
the skew shape λ/(λ_5,λ_6,…), where k=C−(2m−1). A unique interior
rank would force all included cells to precede all excluded cells;
the monotone four-cell columns forbid such a cut. When an exceptional
predecessor fits, the bottom four cells of column one separate as a
disjoint chain. Counting its possible prefix lengths and handling k=2
excludes the loss of both useful predecessors. The complete argument,
including the exceptional lengths and rank-two inequality, is in the
included proof and is credited to parent author assistance.

Condition (8) says that every column of λ/ν has at most four cells.
Fill each skew column, from top to bottom, by 1,2,3,4 as needed.
This is a semistandard skew tableau: in a fixed row, the number of
removed cells above it weakly decreases as the column moves right,
so the assigned entry weakly increases. Thus s_(λ/ν)(1,1,1,1)>0.
By the LR expansion and nonnegativity, some η with length≤4 satisfies
c_(ν,η)^λ>0. Equivalently, one may use four successive horizontal
strips and Pieri. Each of the two distinct ν therefore contributes
at least m−3 to the same two-band sum. This proves (7) in this case.

## 6. Narrow diagrams with low capacity

Assume λ_1≤m and C≤2m. The included proof
`kostka-low-capacity-proof.md` establishes the following uniform statement:
for d≥8 and L⊢N_d with L_1≤d−1 and top-four sum≤2d,

    K_(Lᵗ,ρ_d)≥d,

except for the column, hooks of widths 2 and d−1, and
(d−1,d−1,1^(N_d−2d+2)). The maximal configuration gives d−1 on
the three noncolumn exceptions.

The proof uses Kirillov's actual rigged-configuration formula. In the
maximal configuration ν^(k)=(α_(k+1),α_(k+2),…), α=Lᵗ, the first
vacancy equals the dominance deficit D_j precisely for j≤t=α_2.
Moving one cell in the conjugate of ν^(1) increases its prefix count
on an interval contained in [1,t), so the first vacancy decreases by
two there and the second increases by one. At every occupied ν^(2)
length in that interval the old second vacancy is zero. These interval
facts justify the explicit positive binomial factors. The width-two
case instead uses ν^(1)=(t−2,2); all other cases are the complete
case split in the included proof. This credits the published
configuration/perturbation operation, not a new rigged formula.

For λ_1≤m−1 this gives K_(λᵗ,ρ_m)≥m−1 except for the column,
which is already in E_m. If λ_1=m, remove the forced full tableau
column to obtain

    K_(λᵗ,ρ_m)=K_((λ_2,λ_3,…)ᵗ,ρ_(m−1)).                (9)

Indeed, the full column must contain 1,…,m, subtracting one from every
content multiplicity. After deletion the last letter has content zero.
Put L=(λ_2,λ_3,…), h=m−1≥8. Its first three parts sum to at most
m=h+1. Its first row is at most h−1: a first row h would leave a
sum of at most one for its next two parts, impossible at area N_h.
Also its top-four sum is at most 2h. The lemma applies at h.
Its column and width-two hook exceptions correspond to H_m and J_m;
the double-(h−1) exception is impossible since its first three parts
sum to 2h−1>h+1. The remaining width-(h−1) hook yields precisely

    λ=(m,m−2,1^(N_m−2m+2)).                             (10)

This last family is paid by multiplicity within the two-band quotient.
Set h=m−2, n=N_h, and ν=(2,1^(n−2)), which is outside E_h.
Then λ=(m,m−2,1^(n+1)), and λ/ν is the disjoint union of a
bottom column of four cells and D=(m,m−2)/(2,1). Jacobi–Trudi and
Pieri give, for m≥5,

    s_D=h_(m−2)h_(m−3)−h_mh_(m−5)
       =s_(m−1,m−4)+s_(m−2,m−3).

Multiplication by e_4 supplies the two distinct four-row constituents
(m,m−3,1,1) and (m−1,m−2,1,1), each with coefficient at least one.
Consequently ∑_(length(η)≤4)c_(ν,η)^λ≥2, and the two-band sum in
(5) is at least 2(m−3)≥m−1. This completes the uniform induction
step at every m≥9.

## 7. Exact finite starts and what their computation proves

The finite calculations are over integers and rational numbers, not floating
point or residues. `verify-finite-proof.py` recomputes its complete certificate.
Its dependencies are the included `multiplicity-diagnostic.py`,
`quotient-diagnostic.py` and `exception-induction-diagnostic.py`; no private
source code, external package, downloaded data or network is needed.

Partitions are enumerated recursively by choosing the next part between
one and the preceding part. A horizontal strip is enumerated by the exact
interlacing λ_i≥ν_i≥λ_(i+1), with the prescribed size difference.
Successively deleting horizontal strips computes Kostka numbers by the
semistandard-tableau recurrence. The four-strip routine enumerates precisely
λ_i≥ν_i≥λ_(i+4), imposing weak decrease and the total area.

For character calculations, a partition with l parts has beta set
{λ_i+l−i:1≤i≤l}. Replacing a bead x by the unoccupied nonnegative
position x−k enumerates a removable k-border strip; the sign is
(−1) to the number of beads crossed. The Murnaghan–Nakayama recurrence
computes χ^λ(μ), and z_μ=∏j^(a_j)a_j! is the centralizer size.
The small square coefficients are exactly

    g(ρ,ρ,λ)=∑_(μ⊢N) χ^ρ(μ)^2χ^λ(μ)/z_μ.                (11)

For induction from character vectors a,b, the value at μ is

    χ_Ind(μ)=∑_(u⊔v=μ) z_μ/(z_uz_v) χ_a(u)χ_b(v),       (12)

where u,v have the two prescribed sizes. Taking character inner products
with χ^λ gives precisely the LR sum in (5). The finite verifier checks
integrality/nonnegativity and induced dimensions at every use of (12).
The small square computation also checks staircase orthogonality, the
hook-length dimension, the total square dimension and both linear coefficients.

The complete outputs establish:

* m=2,3,4: the minimum in (1) is respectively 1,2,3, by (11).
* Starting from R_1 and (5), the R_h values at h=5,6 meet (7) for
  all 172 and 788 nonexceptional labels, respectively. All intermediate
  R_2,R_3,R_4 values and the four separate terms of (5) are retained.
* At m=7,8, every nonexceptional λ passes at least one of the following
  exact tests: the one-band sum with weight m−2 on nonexceptional
  predecessors and weight1 on exceptions; the exact Kostka bound; the
  four-strip sum with weight m−3 on nonexceptional predecessors and
  weight1 on exceptions; or the symbolic critical-family calculation
  (10). Thus these are finite induction steps, not the invalid feeding
  of smaller ambient-square multiplicities into W_h.

The partition counts are 176 and792 at N_5=15,N_6=21, and3718 and17977
at N_7=28,N_8=36. The certificate lists every checked label and winning
bound; the script verifies every required inequality. The uniform proof
therefore depends on a finite, explicitly reproducible exact calculation
in these stated degrees. No assertion of a fully formalized theorem is made.

## 8. Conclusion, sharpness and boundaries

The bases and §§4–6 prove (7) for every h≥5 by strong induction.
For m≥5 and a nonlinear, nonsign label λ, either λ∉E_m, or λ is
H_m or J_m. In the latter two cases λᵗ is outside E_m: its first
row is N_m−m+1 or N_m−m, greater than m, and it is not a row.
Thus (6) proves (1). The small cases m=2,3,4 are already established.

Finally, S^(N−1,1) is the nontrivial summand of the natural permutation
module. Branching and Frobenius reciprocity give

    g(ρ_m,ρ_m,(N_m−1,1))
       =dim End_(S_(N_m−1))(Res S^ρ_m)−1=m−1,

because the staircase has exactly m distinct removable corners and
branching is multiplicity-free. This is the classical corner formula,
not part of the novelty claim.

The source cyclic support, full induced quotients and exact dominance
module are essential inputs. The proposed residual contribution is the
uniform asymmetric multiplicity induction, combining the exceptional-
predecessor count with the quantitative low-capacity Kostka estimate.
Kirillov supplies its configuration operation; the parent supplies the
high-capacity combinatorial proof. Existing signed-square targets and the
accepted integral cube result are neither resolved nor repackaged here.
The independent reviewers must assess both full correctness and whether
this residual step is substantial. No count is requested before those gates.
