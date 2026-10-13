# I208: contribution review of the all-height elliptic covering nomination

2026-10-12. **TECHNICAL/KNOWN ONLY — “technical” is the operative classification.** I do **not** establish that the precise all-height theorem was published before I203. It solves the unpaid in-project optimization and is a useful exact corollary. On the evidence supplied and the primary literature read, however, I do not recommend counting it as a substantial independent finding. Its remaining construction is a two-dimensional shear normal form applied to the accepted square-covering operation; the nonlinear result substitutes the resulting optimal local cost into the accepted retention operation. No new convex-body consequence or other independently substantial application has been demonstrated.

This is a contribution judgment, not I207's proof gate. I207 and other live-task outputs were not read. Eight accepted findings and the accepted corpus at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are unchanged. The parent makes the final decision.

## Exact result being assessed

For each real 2-by-2 matrix A with trace zero and d=det A>0, and each L>0, define c_L(A) by minimizing |F|/covol(Gamma) over bounded Lebesgue-measurable F and full-rank lattices Gamma for which

    F + (I+sA)Gamma = R², for every real s in [-L,L].

I203 gives c_L(A)=1+L²d, with attainment by a compact nondegenerate parallelogram. Both F and Gamma may depend on A,L. In normalized coordinates A=J, k=L sqrt(d), the value is 1+k². This is an exact continuum statement, not a finite sampling assertion or an almost-everywhere-in-height assertion.

Its finite consequence concerns compact label sets K, fields V that are C¹ on a neighborhood of K, trace DV=0 and det DV>-L^-2 on K. For any epsilon>0 it covers the physical ruled sweep F_h(E(K,V,L)) by finitely many cylinders with compact nondegenerate parallelogram perpendicular bases, at total cost at most

    h integral_K [1+L²(det DV)_+] J_h(V) + epsilon,
    J_h(v)=(1+v_1²+h²v_2²)^(-1/2).

The determinant restriction is pointwise on K; it is not a bound on the norm of DV. The claimed lower bound and optimality belong to the periodic affine class, not to this general finite-cover conclusion.

## 1. What primary literature does and does not already supply

The accompanying [literature record](../sources/i208_all_height_tiles_contribution/literature.md) gives theorem locations and reading limits. The most relevant additional comparison missing from I203's cited set is Burgiel–Oussa's **good pairs** of lattices: pairs admitting a common parallelepiped-shaped fundamental domain. Their [2015 preprint](https://arxiv.org/abs/1507.04671v1), read in full, gives the difference-body criterion (Proposition 3), triangular unipotent constructions (Proposition 4), further explicit constructions (Proposition 5), and nonexistence examples (Proposition 6). Thus common convex domains, separate choices of a domain basis and lattice bases, and the use of shear lattices are established parts of this subject. The existence of a particularly simple common endpoint domain is not by itself a new phenomenon.

That paper does **not** state the varying-volume continuum theorem under review. Its equal-volume pair criterion tests two lattices, and cannot simply be relabeled as a theorem about every intermediate lattice. Moreover, its negative examples concern prescribed lattice pairs; they do not obstruct I203, which chooses Gamma. I found no statement there that subsumes the complete I203 assertion.

The actual [Kolountzakis 1998 paper](https://www.combinatorics.org/ojs/index.php/eljc/article/viewFile/v5i1r14/pdf/), read in full in place, is much closer to the operational content: equations (13)–(20) give the signed rectangle identity underlying the positive-product square cover. The source manuscript itself expressly recognizes this overlap in `b:lattice`. The identity allows individual shear parameters larger than one. Neither I203's use of large parameters nor its closed-square coverage is a new tiling mechanism. The positive-product covering range is already paid.

[Grepstad–Kolountzakis 2025](https://arxiv.org/abs/2507.00604v1), Theorem 1, gives bounded finite-polytopal common domains for any two equal-volume lattices. [Grepstad–Kolountzakis–Spyridakis 2025](https://arxiv.org/abs/2508.07972v1), Theorem 1.2 and its interpretation in §1.5, also gives a bounded domain of the sparser lattice containing a domain of the denser lattice. Hence two arbitrary heights can be covered at the larger covolume. Neither conclusion supplies a fixed domain for a continuum, and arbitrary endpoint domains do not have the interpolation property. I203 correctly does not claim otherwise.

The geometry-of-numbers comparison is not limited to Steinhaus terminology. [Xue 2019](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v26i2p9/pdf/), read in full, studies bodies meeting Z² in every translated and rotated position; Theorem 6 reformulates this through covering radii, and Theorem 9 uses inscribed shear parallelograms after Steiner symmetrization. These are relevant established geometric techniques, but their quantifiers fix Z² and require all rotations of a body. I203 instead selects Gamma and couples the rotation angle to a dilation. The two problems are not equivalent. Xue cites older Niven–Zuckerman and Fáry results; their original articles were not obtained/read here, so I do not treat those citations as independently verified priority evidence.

The soft multi-lattice constructions in [Kolountzakis–Papageorgiou](https://arxiv.org/abs/2106.11701v1) impose tiling identities for functions. The recent [Speegle 2026 paper](https://arxiv.org/abs/2606.15297v1), read in full, Theorem 3.1, rounds exact integer-multiplicity identities for **two** lattices to a possibly nonmeasurable set. It does not round a continuum of covering inequalities to a bounded measurable cover. [Loukaki–Spyridakis 2026](https://arxiv.org/abs/2606.14319v1), Theorem B, treats three equal-volume lattices with discrete sum, not the present varying-covolume path.

**Priority finding:** no exact duplicate or equivalent general theorem was located in the sources actually read. This is a limited negative finding, not worldwide novelty. The all-height assertion must not be advertised as the solution of any of these named problems.

## 2. The unpaid bridge, reduced to its actual size

The construction does fill a genuine logical gap in I201: its chosen endpoint tile also covers the intermediate lattices. It provides compact attainment for every k, whereas I201 had only three sharp resonances. Calling it merely another resonance or deducing it from arbitrary endpoint tilings would be wrong.

The following description makes clear how much of that bridge is supplied by old operations. Set

    U_a = [[1,a],[0,1]],   L_b = [[1,0],[b,1]],
    M_u = (1-u)L_b + u U_a = [[1,ua],[(1-u)b,1]],  0<=u<=1.

For a,b with 0<=ab<4, the accepted square-covering lemma immediately gives

    Q+M_u Z²=R²,
    det M_u=1-ab u(1-u)>0.

Both endpoints are ordinary shear tilings; the interior is precisely the old positive-product family. For I203 choose

    u=(t+k)/(2k),  a=-4k²/(1+k²),  b=-1.

Then M_u is exactly B^-1(I+tJ)G from its proof. Its determinant is (1+t²)/(1+k²). The endpoint relative map U_a L_b^-1 has determinant one and trace 2-ab=2(1-k²)/(1+k²), the trace of the elliptic endpoint map (I+kJ)(I-kJ)^-1. Equivalently, matching this elliptic map to two opposite shear bases gives the displayed B,G. The interior coverage is already contained in the accepted lemma, not a new theorem about interpolation of arbitrary covers.

This analysis is not offered as a new result. It identifies the candidate's residual contribution: selecting a shear-to-shear representative of the elliptic path. The all-height quantifier becomes automatic once that representative is selected. The lower bound is the paid endpoint density inequality; conjugation of trace-zero elliptic 2-by-2 matrices is elementary linear algebra. The parallelogram is then a linear image of Q.

A short proof need not be insignificant. In favor of I203 are exact attainment, the full parameter range, a one-piece convex template and a useful distinction between choosing an endpoint tile and choosing one that covers the whole path. Against treating this as a substantial independent finding are the very narrow normal-form task remaining after the accepted operation, the established shear/common-parallelogram context, and the lack of a demonstrated independent geometric payoff. It is more than an unproved endpoint shortcut, but I classify the complete result as a sharp technical application rather than a new covering mechanism or a solution of an established broader problem.

## 3. Demonstrated gains and limits

The gains are precise, and should be retained even under this classification.

* For the periodic affine problem the value is now 1+k² for every k>0. I201's bounds were min(1+2k²,q_4(k),q_6(k)); their excess above 1+k² is strictly positive except at k=1/sqrt(3),1,sqrt(3). This removes the whole previously unpaid parameter range, not just isolated additional cases.
* The nonlinear upper functional is lower than I201's by exactly

      hL² integral_K (det DV)_+ J_h(V).

  It is a strict improvement when the elliptic part has positive label measure. The spectral range, C¹ assumptions and arbitrary compact-label allowance are the same as I201's corrected theorem. It adds no new regularity or boundary theorem.
* A single optimal elliptic parallelogram replaces the older union-of-rectangles template. This is structural simplicity, not a proved uniform bound on the number of retained cylinders. Conditioning can deteriorate as d approaches zero, and the proof uses a determinant cutoff.

These statements concern a general family of ruled sets, not only the source counterexample. Nevertheless, no specific new convex body, stronger tetrahedral coefficient, improved normalized extremal bound, or optimal arbitrary-axis finite-cylinder cost follows in the supplied work. The source counterexample and its rational, hyperbolic, nilpotent, angular and radial companions are already solved; their headline conclusions are not new applications of this theorem. In particular the angular companion already supplies the quadratic coefficient -1/240 with a cubic buffer. I203 constructs no wall-compatible elliptic field producing an additional verified saving.

The rotation sweep is useful as a consistency check but does not close this significance gap: its sections have radius proportional to sqrt(1+omega²s²), so the sweep is generally nonconvex. Covering it does not cover its convex hull. The known volume/chord lower factor 1+k²/3 in the thin-label limit differs from the periodic factor 1+k²; I203 does not show sharpness for finite cylinder covers.

**Narrower verdicts:** the finite coefficient-one transfer is **TECHNICAL/KNOWN ONLY** as an application of the accepted retention machinery to the affine template. The precise affine formula is a valid new-to-project exact corollary on the evidence considered; its worldwide priority remains **INCONCLUSIVE**, and I do not recommend a substantial-finding nomination solely for that formula. A new verified convex-body consequence or an independently established external problem solved by this normal form could change the contribution assessment; neither is present in this record.

## 4. Proof issues relevant to contribution

I found no specific proof defect that motivates this contribution verdict. In particular, the accepted square lemma has no separate bound on |a| or |b|; imposing one would incorrectly remove large k. Independent left and right coordinate choices are permitted because both F and Gamma are chosen; the proof does not claim an elliptic matrix is similar to a hyperbolic one. Endpoints have relative determinant one, while interior overlap is allowed. “Common fundamental domain at every height” would be false wording: interior covolumes differ. “Common covering set” is correct.

For the nonlinear conclusion the essential technical dependency is uniform template/label-cell control away from det=0, followed by the old small-positive-determinant templates near zero, and finite retention of the actual nonlinear targets. The submitted proof explicitly includes that cutoff. Whether every estimate is correct belongs to I207, not to an assumption of this review. No I207 outcome is presumed.

## Reading and operation limits

Three new primary PDFs were fully read through their extracted text and retained: Burgiel–Oussa (13 pages), Xue (11), Speegle (13). Kolountzakis 1998 was fully read in place; the two 2025 domain papers, the 2021 soft-tiling paper and the 2026 three-subgroup paper were read only in the ranges listed in the literature record. The four source companions were checked at actual theorem statements, not solely through the catalogue. No audit of accepted source truth, complete literature bibliography, entire preprint tree, or other task package is claimed. Search misses have no positive novelty force.

Only the authorized I208 files and retained full-read sources were written. No subordinate agents, research code, numerical tests, snapshots, seals, historical replays, staging, commits, publication, I31 edits or shared/ancestor edits were used. Input/source hashes are recorded in the separate authentication file; final output hashes are returned detached.
