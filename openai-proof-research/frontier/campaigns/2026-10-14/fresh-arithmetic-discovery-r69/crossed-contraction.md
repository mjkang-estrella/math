# Explicit crossed two-versus-two contraction

Author expansion requested by parent. All tensor spaces below have their ordinary Euclidean norms. This is an exact finite-dimensional factorization, not a generic assertion about reshuffling preserving operator norms.

Let A_ijab and F_klab be real four-tensors (the two factors may be differently permuted copies of the same tensor). Define

  Q_ijkl=sum_ab A_ijab F_klab.

The natural flattening (ij)|(kl) is a matrix product. For the crossed flattening (ik)|(jl), define R_ab:V_j->V_i and S_ab:V_l->V_k by

  (R_ab)_ij=A_ijab,   (S_ab)_kl=F_klab.

Then, with the indicated domain and codomain order,

  Q_cross: V_j tensor V_l -> V_i tensor V_k,
  Q_cross=sum_ab R_ab tensor S_ab.                     (1)

No transpose is implicit in (1): its (i,k),(j,l) entry is exactly Q_ijkl.

Factor (1) through H=direct_sum_(a,b)(V_j tensor V_k). Define

  C:V_j tensor V_l -> H,
       (Cz)_ab=(I_(V_j) tensor S_ab)z;
  R:H -> V_i tensor V_k,
       R(w)=sum_ab(R_ab tensor I_(V_k))w_ab.

Then Q_cross=RC and

  RR*= (sum_ab R_ab R_ab*) tensor I_(V_k),
  C*C= I_(V_j) tensor (sum_ab S_ab* S_ab).              (2)

The first Gram in (2) has entries

  (sum_ab R_ab R_ab*)_ii'
       =sum_jab A_ijab A_i'jab.

It is exactly the Gram of the one-versus-three flattening A_(i)|(jab). The second has entries

  (sum_ab S_ab* S_ab)_ll'
       =sum_kab F_klab F_kl'ab,

which is the Gram of the singleton-l flattening F_(l)|(kab). If every one-versus-three flattening of A and F has norm <=eta_A and eta_F respectively, equations(1),(2) give

  ||Q_cross||op<=||R||op||C||op<=eta_A eta_F.          (3)

For the other crossed cut (il)|(jk), replace S_ab by its transpose: its row and column roles exchange, and the singleton-k Gram of F is used. Permuting the free indices covers all orderings. Permuting the four indices within each original A before contracting only changes which singleton Gram appears; the hypothesis explicitly bounds every such Gram.

For completeness, the singleton-i flattening of Q is bounded using a different argument. Fix a unit x in V_i and form (A_x)_jab=sum_i x_i A_ijab. Its HS norm is <=eta_A. Apply the natural (kl)|(ab) flattening of F separately for each j; if that flattening norm is <=eta_F, then ||Q_x||HS<=eta_F||A_x||HS<=eta_A eta_F. Other singleton cuts are analogous. The total HS bound ||Q||HS<=eta_A ||F||HS follows from the natural two-versus-two matrix product (or with the factors exchanged).

Thus all the bounds used for the two-index quadratic contractions in operator-density-correction.md Section1 follow with the claimed constant1. The crossed proof does not infer a bound from the natural two-versus-two norm alone; it explicitly uses both singleton Grams in (2).

The accompanying check_crossed_contraction.py verifies equations(1),(2) and their identification with singleton Grams over exact integer tensors with different permutations. It is a finite identity diagnostic, not a replacement for the argument above or a numerical proof of the global target.
