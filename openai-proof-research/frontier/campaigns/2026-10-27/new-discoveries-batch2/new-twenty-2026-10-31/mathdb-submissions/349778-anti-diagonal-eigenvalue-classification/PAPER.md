# Stochastic matrices with the global anti-diagonal eigenvalue property

## Status and scope

This manuscript proves Britnell–Wildon's Conjecture 2.6 in every finite dimension. The accompanying Lean development proves the literal MathDB 349778 endpoint unconditionally, including the source's real diagonalizability convention and the eigenvalue multiset of every leading block. The zero-tail boundary is proved by a determinant coefficient comparison, so the induction has no boundary hypothesis left over. REPORT.md records the exact declarations, printed axioms and bounded-runner compilation and standalone kernel-check receipts.

## MathDB record and printed conjecture

The following paragraph is the MathDB record, rather than a verbatim quotation from the source.

Let $A$ be a stochastic matrix with distinct eigenvalues. Say that $A$ has the **strong anti-diagonal eigenvalue property** when it satisfies the stronger anti-diagonal eigenvalue condition defined in the paper, and let $H^\lambda$ denote the parameterized family of lower-triangular matrices introduced there. **Strong anti-diagonal eigenvalue property conjecture.** $A$ has the strong anti-diagonal eigenvalue property if and only if it is of the form $H^\lambda$. The conjecture would classify stochastic matrices with distinct eigenvalues satisfying this strengthened spectral property; the paper states that it can be proved for $n\leqslant4$, while the general case is left open.


The literal accepted-journal formulation (Conjecture 2.6, p.14) is: “A stochastic matrix with distinct eigenvalues has the global anti-diagonal eigenvalue property if and only if it is of the form H^λ.”

## Source definitions beside their Lean representation

Source: Britnell–Wildon, *Linear Algebra and its Applications* 641 (2022), 1–47, DOI 10.1016/j.laa.2022.01.018. The supplied journal PDF and its text are in `../fresh-shard047-discovery-sol61-20261119-r2/sources/matrix-journal.{pdf,txt}`. No new external requests are necessary.

p.5: “a lower-triangular n × n matrix L has the anti-diagonal eigenvalue property if L is diagonalizable and the eigenvalues of LJ(n) are precisely (−1)^d L_dd for d ∈ n.”

p.5: “the global anti-diagonal eigenvalue property, namely that for all m ≤ n, the m × m top-left submatrix of L has the anti-diagonal property.”

p.5, (1.6): “H^λ = B(n)Diag(λ_0, . . . , λ_{n−1})B(n)^{−1}”, “where B(n) is the n × n Pascal’s Triangle matrix defined by B_xy = binom(x,y).”

p.9: “J(n) is the n × n matrix defined in Iverson bracket notation by J(n)_xy = [x = y′].” Here y′=n−1−y, the source's involution on the total order n.

p.9: “For e ∈ {0, 1, . . . , n}, let V_e be the e-dimensional subspace of R^n of all row vectors (f(0), . . . , f(n − 1)) where f is a polynomial of degree strictly less than e.”

p.14, Conjecture 2.6: “A stochastic matrix with distinct eigenvalues has the global anti-diagonal eigenvalue property if and only if it is of the form H^λ.”

The source uses the standard meaning of stochastic: nonnegative entries and row sums one. The discovery proof denotes the degree-at-most-d space by V_d, offset by one from the source's dimension-indexed V_e. The auxiliary Lean `flag n d` is the span of the first d+1 binomial vectors. The proof below uses that algebraic definition throughout. It does not require an identification with the source polynomial-evaluation space; the optional lemma `flag_polynomial` is not asserted or used.

The MathDB record uses “strong” for the same property; its exact record text is reproduced in PAPER.md. The accepted journal says “global”. The global eigenbasis property of §2.4 is NOT this predicate.

All matrix indices are 0,...,n−1. The source property has a lower-triangular real domain; the Lean predicate extends it to arbitrary real square matrices by declaring it false outside that domain. The parameter vector in H^a is an arbitrary finite real vector. Under the endpoint's stochastic hypothesis it automatically satisfies a_0=1 (for n>0) and

    sum_(k=0)^(i-j) (-1)^k binom(i-j,k) a_(j+k) >= 0,  0<=j<=i<n.

These finite inequalities are precisely entrywise nonnegativity of H^a; row sums are a_0. There is no infinite moment-extension hypothesis. For example a=(1,1/2,0) gives a stochastic H^a, but cannot be the first three moments of a probability measure on [0,1], since its second moment is smaller than the square of its first.

For n=3, write L=[[a_0,0,0],[b,a_1,0],[c,d,a_2]]. The global property requires diagonalizability of each leading block L_m and the spectra, with multiplicities,

    spec([a_0])={a_0},
    spec([[0,a_0],[a_1,b]])={a_0,-a_1},
    spec([[0,0,a_0],[0,a_1,b],[a_2,d,c]])={a_0,-a_1,a_2}.

The empty block adds only the empty-spectrum convention. In the stochastic simple-spectrum setting diagonalizability of all L_m follows from their distinct real diagonal entries. Membership in the binomial family is exactly b=a_0−a_1, c=a_0−2a_1+a_2 and d=2(a_1−a_2), with a_0=1. This explicitly distinguishes the block-by-block spectral property from the stronger eigenbasis-action condition.



## Exact Lean definitions

```lean
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Choose.Basic

namespace Classification349778

abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

def LowerTriangular {n : ℕ} (A : Mat n) : Prop := ∀ i j, i < j → A i j = 0

def Stochastic {n : ℕ} (A : Mat n) : Prop :=
  (∀ i j, 0 ≤ A i j) ∧ ∀ i, ∑ j, A i j = 1

def pascal (n : ℕ) : Mat n := fun i j => (Nat.choose i.val j.val : ℝ)

def pascalInv (n : ℕ) : Mat n :=
  fun i j => (-1 : ℝ) ^ (i.val + j.val) * (Nat.choose i.val j.val : ℝ)

noncomputable def reversal (n : ℕ) : Mat n := fun i j => if i = j.rev then 1 else 0

noncomputable def binomialTransform {n : ℕ} (a : Vec n) : Mat n :=
  pascal n * Matrix.diagonal a * (pascal n)⁻¹

def leading {n : ℕ} (A : Mat n) (m : ℕ) (h : m ≤ n) : Mat m :=
  A.submatrix (Fin.castLE h) (Fin.castLE h)

noncomputable def signedDiagonal {n : ℕ} (A : Mat n) : Vec n :=
  fun i => (-1 : ℝ) ^ i.val * A i i

noncomputable def prescribedCharpoly {n : ℕ} (A : Mat n) : Polynomial ℝ :=
  ∏ i, (Polynomial.X - Polynomial.C (signedDiagonal A i))

def GlobalAntiDiagonalCharpoly {n : ℕ} (A : Mat n) : Prop :=
  ∀ (m : ℕ) (h : m ≤ n),
    ((leading A m h) * reversal m).charpoly = prescribedCharpoly (leading A m h)

def Diagonalizable {n : ℕ} (A : Mat n) : Prop :=
  ∃ (Q : Mat n) (a : Vec n), IsUnit Q.det ∧ A * Q = Q * Matrix.diagonal a

def HasRealSpectrum {n : ℕ} (A : Mat n) (a : Vec n) : Prop :=
  (A.map Complex.ofRealHom).charpoly.roots = (Finset.univ.val.map (fun i => (a i : ℂ)))

def AntiDiagonalEigenvalue {n : ℕ} (A : Mat n) : Prop :=
  LowerTriangular A ∧ Diagonalizable A ∧ HasRealSpectrum (A * reversal n) (signedDiagonal A)

def GlobalAntiDiagonalEigenvalue {n : ℕ} (A : Mat n) : Prop :=
  LowerTriangular A ∧ ∀ (m : ℕ) (h : m ≤ n), AntiDiagonalEigenvalue (leading A m h)

def DistinctEigenvalues {n : ℕ} (A : Mat n) : Prop :=
  ∃ a : Fin n → ℂ, Function.Injective a ∧
    (A.map Complex.ofRealHom).charpoly = ∏ i, (Polynomial.X - Polynomial.C (a i))

def MathDB349778 : Prop :=
  ∀ (n : ℕ) (A : Mat n), Stochastic A → DistinctEigenvalues A →
    (GlobalAntiDiagonalEigenvalue A ↔ ∃ a : Vec n, A = binomialTransform a)

def binomialVector (n k : ℕ) : Vec n := fun i => (Nat.choose i.val k : ℝ)

def difference (n : ℕ) (v : Vec (n+1)) : Vec n := fun i => v i.succ - v i.castSucc

noncomputable def flag (n d : ℕ) : Submodule ℝ (Vec n) :=
  Submodule.span ℝ (Set.range (fun k : Fin (d+1) => binomialVector n k.val))

def KnownRowsHarmonic {N : ℕ} (H : Mat N) (a : ℝ) (u : Vec N) : Prop :=
  ∀ i : Fin N, i.val + 1 < N → ((H * reversal N).mulVec u) i = a * u i

end Classification349778
```

The corresponding literal Lean definitions are in ClassificationDefinitions.lean, reproduced without abbreviation in the source appendix. `LowerTriangular A` means `∀ i j, i < j → A i j = 0`; `Stochastic A` is entrywise nonnegativity and row sums one. `pascal n i j` is the real natural binomial coefficient. `reversal n i j` is the Iverson bracket for `i = j.rev`. `binomialTransform a` is literally `pascal n * Matrix.diagonal a * (pascal n)⁻¹`, using Mathlib's matrix inverse. The inverse is not silently replaced by a formula: `pascal_inv` proves the explicit signed Pascal formula equals that inverse.

`Diagonalizable A` asserts existence of a real invertible matrix Q and a real diagonal a with A Q = Q diag(a). `HasRealSpectrum A a` lists all complex characteristic-polynomial roots, with algebraic multiplicities, as the multiset of the n specified real numbers embedded into ℂ. `AntiDiagonalEigenvalue A` combines lower triangularity, real diagonalizability of A, and the prescribed spectrum of A J. `GlobalAntiDiagonalEigenvalue A` asks for that property on every actual leading block. It never substitutes global eigenbasis action. Including the size-zero leading block only adds the literal empty convention.

The proved endpoint `Classification349778.mathdb349778` has the exact statement:

```lean
theorem mathdb349778 (n : ℕ) (A : Mat n) (hs : Stochastic A)
    (hd : DistinctEigenvalues A) :
    GlobalAntiDiagonalEigenvalue A ↔ ∃ a : Vec n, A = binomialTransform a
```

`DistinctEigenvalues` is a factorization of the complexified characteristic polynomial into n linear factors with injective parameters. This allows complex eigenvalues for arbitrary real stochastic matrices; real spectrum is not assumed before lower triangularity is established. The theorem `lower_distinct_iff` proves the lower-triangular/simple-diagonal bridge, and `lower_distinct_diagonalizable` proves real diagonalizability. Applying these results to the leading blocks gives `global_fidelity`. `spectrum_iff_charpoly` already proves the exact multiplicity-list/characteristic-polynomial equivalence. `global_implies_charpoly` and `global_fidelity_of_diagonalizable` isolate the source's diagonalizability convention honestly; the latter has an explicit hypothesis for each leading block.

## Classification theorem

For every real stochastic lower-triangular n by n matrix L with pairwise distinct diagonal entries λ_i, the global anti-diagonal eigenvalue property is equivalent to L = B diag(λ) B⁻¹. For an arbitrary stochastic real A with distinct eigenvalues, the source property is defined only on the lower-triangular domain. Every binomial transform is lower triangular. Thus this theorem is the literal conjecture, once the simple-spectrum and diagonalizability equivalences are included. Lower triangularity gives real diagonal eigenvalues and distinct diagonal gives a basis of real eigenvectors; each leading block inherits these conditions. The signed diagonal numbers are also pairwise distinct under nonnegative distinct diagonal entries, though diagonalizability of LJ is not part of our definition and is unnecessary for the characteristic-polynomial proof.

## 1. Elementary binomial and difference facts

For the proof, write V_d^(n) for the real linear span of the vectors

    b_k^(n)(i)=binom(i,k), 0<=k<=d,

and put V_(-1)={0}. This is precisely the auxiliary Lean `flag n d`, rather than a replacement for any object in the conjecture. For 0<=d<n these vectors are linearly independent: their first d+1 entries form a unit lower-triangular matrix. Consequently dim V_d^(n)=d+1, and restriction to the first d+1 coordinates is an isomorphism. The signed reflection action on this algebraic flag will be proved directly by finite differences below. Although the binomial vectors are polynomial evaluations, no polynomial-space identification is needed anywhere in the argument.

The inverse Pascal matrix is

    (B_n^(-1))_ij = (-1)^(i-j) binom(i,j), j<=i.

Indeed its product with B has (i,j) entry binom(i,j) times the alternating binomial sum of order i-j, which is 1 for i=j and 0 otherwise. Therefore

    H^lambda_ij = binom(i,j) sum_(k=0)^(i-j) (-1)^k binom(i-j,k) lambda_(j+k)     (1)

for j<=i, and zero otherwise. Also H^lambda b_k=lambda_k b_k. It follows that H^lambda preserves every V_d and has row sums lambda_0.

Let D_n: R^n -> R^(n-1) be the forward difference, (D_n v)_i=v_(i+1)-v_i. Then

    D_n J_n = -J_(n-1) D_n,                                                 (2)
    D_n H^(lambda_0,...,lambda_(n-1))
        = H^(lambda_1,...,lambda_(n-1)) D_n.                                (3)

Equation (2) is direct. To prove (3), apply both sides to the basis b_k, using D_n b_0=0 and D_n b_k=b_(k-1) for k>=1. Iteration gives, with D^j denoting j successive forward differences,

    D^j H^lambda J_n = (-1)^j H^(lambda_j,...,lambda_(n-1)) J_(n-j) D^j.      (4)

A vector v belongs to V_j^(n) exactly when D^j v is constant, for j<n. Here is a direct algebraic proof. The Pascal basis gives an expansion v=sum c_k b_k. One difference removes c_0 and shifts every remaining coefficient down by one. Thus Dv belongs to V_d^(n-1) if and only if v belongs to V_(d+1)^(n): the reverse direction follows by lifting the binomial expansion of Dv, and adding the constant v minus that lift. Iterating, with V_0 exactly the constants, gives the assertion. The same unit triangular basis proves that restriction of V_(n-2)^(n) to its first n-1 positions is an isomorphism onto R^(n-1).

Reflection acts by (-1)^d on V_d/V_(d-1). To prove this without polynomial evaluation, induct on d, simultaneously for all sizes n. For d=0 reflection fixes constants. For d>0, put w=J_n b_d-(-1)^d b_d. Equation (2) and D b_d=b_(d-1) give

    D w = -(J_(n-1) b_(d-1)-(-1)^(d-1) b_(d-1)).

By induction the right side lies in V_(d-2). The one-difference criterion then places w in V_(d-1); when d=1 the right side is zero and w is constant. The zero-dimensional case is empty. This proves the quotient action and invariance of each flag subspace in all sizes used here. Together with H b_k=lambda_k b_k, it also proves that B^-1 J B is upper triangular with diagonal (-1)^k.

For later use, (1) gives

    H^lambda_(i+1,i)=(i+1)(lambda_i-lambda_(i+1)).                            (5)

If H^a of size n-1 is nonnegative, then for any j>=0 its shifted matrix on the known rows, with parameters a_j,...,a_(n-2), is nonnegative. Explicitly, for 0<=k<=i<=n-j-2, its (i,k) entry is

    binom(i,k)/binom(i+j,k+j) * H^a_(i+j,k+j),                               (6)

which is nonnegative. Its row sum is a_j. Formula (6) is just (1) with the same finite difference and a different positive binomial prefactor.

## 2. A finite maximum principle

**Lemma.** Suppose N>=2 and a_0>...>a_(N-2)>0. Assume the first N-1 rows of the size-N binomial transform H^(a_0,...,a_(N-2),*) are nonnegative. If u in R^N satisfies

    (H J_N u)_i=a_0 u_i, 0<=i<=N-2,                                        (7)

then u is constant. The final parameter and final row of H are irrelevant.

*Proof.* Row 0 gives u_0=u_(N-1). If N=2, this proves the claim. Assume N>=3, and subtract this common constant from u. This does not affect (7), because every known row sums to a_0. Thus we may assume u_0=u_(N-1)=0.

Let M=max_(1<=i<=N-2) |u_i|. If M>0 and |u_i|=M, (7) and nonnegative row sums give

    a_0 M = |sum_k (H J)_ik u_k|
          <= sum_k (H J)_ik |u_k| <= a_0 M.                                 (8)

Consequently every index k with positive coefficient in this row must have |u_k|=M. In particular there can be no positive coefficient to an index with u_k=0.

For each interior i, the coefficient from row i to index N-1-i is a_i>0. For interior i>=2, the coefficient to index N-i is i(a_(i-1)-a_i)>0. These two kinds of edges connect every interior index to 1: for i>=2, take i -> N-i -> i-1, and repeat. All indices on this two-step path are interior, and both coefficients are positive. Starting at an index attaining M, (8) propagates |u|=M to index 1. But row 1 has coefficient a_0-a_1>0 to index N-1, whose value is 0. This contradicts (8). Hence M=0 and u=0 after the subtraction. QED.

This lemma is elementary finite convexity; no irreducibility assumption about the unknown final row is used.

## 3. A zero-tail obstruction

**Lemma.** Let n=r+2>=3. Suppose a_0,...,a_(r-1)>0 and a_r=0, and let L be lower triangular with leading (r+1)-block H^a. Write z=L_(r+1,r+1) and b_r=L_(r+1,r). If

    charpoly(L J_n)=product_(i=0)^(n-1) (X-(-1)^i L_ii),

then b_r=-(r+1)z. In particular, entrywise nonnegativity implies z=0.

*Proof of the maximal minors.* Put c=product_(i=0)^(r-1) a_i>0. Let R be the (r+1)-by-r matrix consisting of the first r columns of H^a. Denote by M_k the determinant of R after deleting row k. We prove

    M_k=binom(r,k)c.                                                       (9)

The adjugate of diag(a) is c times the matrix with its only nonzero entry 1 at (r,r). Indeed its r-th diagonal cofactor is c and every other diagonal cofactor contains a_r=0; all off-diagonal cofactors vanish. The Pascal matrices have determinant one and their adjugates are their inverses. Hence the product rule for adjugates gives

    adj(H^a)=B adj(diag(a)) B^-1.

Column r of B is the final coordinate vector. Therefore the (r,k) entry of this adjugate is c(-1)^(r+k)binom(r,k). By the cofactor formula it is also (-1)^(r+k)M_k. Cancelling that nonzero sign proves (9). The identity in fact needs no positivity assumptions.

*Proof of the coefficient comparison.* Let lambda be the full diagonal of L and H=H^lambda. Its leading block equals H^a, so L and H agree in their first n-1 rows. Let e be the last row of L-H; then e_(n-1)=0. For any matrix A define the polynomial matrix

    Q_A(X)=X J_n-A.

Multiplication of the characteristic matrix of A J_n by J_n proves

    det Q_A(X)=charpoly(A J_n) det J_n.                                   (10)

Let D(X) have the first n-1 rows of Q_H(X), and last row e (a constant polynomial row). Linearity of the determinant in the last row gives

    det Q_H=det Q_L+det D.                                                 (11)

We now compute exactly the coefficient needed:

    [X] det D=-e_r c.                                                     (12)

The final column of D is X in row 0 and zero everywhere else: lower triangularity kills that column of H on every known row, and e_(n-1)=0 kills the new final row entry. Expanding along this column gives

    det D=(-1)^(r+1) X det S(X),

where S is obtained by deleting row 0 and the final column. Thus its linear coefficient is (-1)^(r+1)det S(0). The first r rows of S(0) are minus rows 1,...,r of H^a, and its last row is (e_0,...,e_r). The last column of H^a is zero, since H^a is lower triangular and a_r=0. Expanding det S(0) along that last column leaves only e_r in the last row. The remaining matrix is minus R with row 0 deleted, so its determinant is (-1)^r M_0=(-1)^r c by (9). Consequently

    [X] det D=(-1)^(r+1)e_r(-1)^r c=-e_r c,

as asserted. This is the perturbation-form coefficient identity formalized as `zero_tail_coefficient`; no dimension-dependent reversal sign needs to be computed.

*Conclusion.* The given characteristic polynomial of LJ equals that of HJ, since H has the same diagonal as L and the binomial-transform converse holds for all parameters, independently of this lemma. Equation (10) therefore makes det Q_H=det Q_L. Equation (11) gives det D=0, and (12), with c>0, gives e_r=0. The subdiagonal formula (5) gives

    H_(r+1,r)=(r+1)(a_r-z)=-(r+1)z.

Since e_r=b_r-H_(r+1,r), this proves b_r=-(r+1)z. If b_r,z>=0, the positive number r+1 forces z=0. This is exactly the proposition `ZeroTailBoundary`, proved as `zero_tail_boundary`. No row-sum condition, diagonalizability or sign restriction on z was used before this final nonnegative consequence. QED.

The coefficient identity can equivalently be written

    [X](det(XJ-L)-det(XJ-H))=c(b_r+(r+1)z).

The exact rational script `exact_zero_tail.py` in the formalization packet checks this formula in 42 cases of sizes 3 through 8, including zero and negative z. These checks pin down the statement and sign; the universal proof is the two Laplace expansions above, checked in Lean.

## 4. Proof of the classification

Before the induction, we record the exact spectral bridges used by the formal proof. A lower-triangular real matrix A has complex characteristic polynomial product_i(X-A_ii). Thus its distinct-eigenvalue hypothesis is equivalent to pairwise distinct diagonal entries: equality of the root multisets transfers the absence of repeated factors in either direction. Each leading block inherits distinct diagonal entries. Every real diagonal entry of such a block supplies a nonzero real eigenvector, since the corresponding real characteristic determinant vanishes. Eigenvectors for distinct eigenvalues are linearly independent (apply the operator minus one eigenvalue to a minimal linear relation and induct). There are as many as the dimension, so their columns form an invertible real matrix. This proves real diagonalizability of every leading block, exactly as required in the source's definition.

For any real matrix P, equality of its complex root multiset with the list of m prescribed real numbers is equivalent to the real identity charpoly(P)=product_i(X-t_i). In the forward direction the characteristic polynomial is monic of degree m and its listed roots have total multiplicity m, so the monic polynomial is exactly that product; injectivity of the real embedding into the complex numbers gives the real identity. The reverse direction reads the roots of the product. This uses multiplicities and does not assume diagonalizability of P. Finally, every H^lambda is real diagonalizable even when parameters repeat, because its real Pascal matrix is invertible and H^lambda B=B diag(lambda). These observations justify the characteristic-polynomial formulation used below for LJ while retaining diagonalizability of L, rather than LJ, in the literal endpoint.

We prove the nontrivial direction by induction on n. The empty case is immediate, and n=1 follows because a stochastic one-by-one matrix is (1). Suppose n>=2 and L satisfies the hypotheses. Write lambda_i=L_ii. Because L is lower triangular, its eigenvalues are exactly these diagonal entries, so the distinct-eigenvalue hypothesis says they are pairwise distinct. Nonnegativity gives lambda_i>=0, and stochasticity gives lambda_0=1.

The top-left (n-1)-block is stochastic: all entries in its top rows to the final column of L are zero. It inherits the global property and distinct diagonal. By induction this block equals H^a with a=(lambda_0,...,lambda_(n-2)). Since it is nonnegative, (5) gives a_i>=a_(i+1). Distinctness strengthens this to

    1=a_0>a_1>...>a_(n-2)>=0.                                              (14)

If n>=3 and a_(n-2)=0, the zero-tail lemma gives lambda_(n-1)=0, contrary to distinctness. For n=2 its sole old parameter is a_0=1. We may therefore assume in every remaining case that all old a_i are positive.

Let H=H^lambda be the full binomial transform of the diagonal of L, and E=L-H. The first n-1 rows of E are zero by induction and the last diagonal entry E_(n-1,n-1) is zero by definition.

Set P=LJ_n. The full-size global property says that for each 0<=j<=n-2, t_j=(-1)^j a_j is a real eigenvalue of P. Choose a nonzero real eigenvector v_j. Such a vector exists since det(P-t_j I)=0. The t_j are pairwise distinct by positivity and (14).

Fix j, put N=n-j and u=D^j v_j. As E is supported in its last row, D^j E J_n v_j is also supported only in the last coordinate of R^N. Thus the first N-1 entries of the eigenvalue equation P v_j=t_j v_j, together with (4), give

    (H^(lambda_j,...,lambda_(n-1)) J_N u)_i=a_j u_i, 0<=i<=N-2.              (15)

The known parameters a_j,...,a_(n-2) are strictly decreasing and positive. The known rows in (15) are nonnegative by (6), and have row sum a_j. Apply the maximum-principle lemma: u is constant. By the difference criterion of §1,

    v_j in V_j^(n) subset V_(n-2)^(n).                                    (16)

There are n-1 such nonzero eigenvectors with distinct eigenvalues, so they are linearly independent. Since dim V_(n-2)^(n)=n-1, they form a basis of that space. Therefore P preserves V_(n-2)^(n). The operator HJ_n also preserves that space, by §1. The two operators agree in their first n-1 output coordinates, because L and H have identical first n-1 rows. Consequently, for v in V_(n-2),

    (P-HJ_n)v in V_(n-2)

has its first n-1 coordinates zero. The restriction isomorphism of §1 forces it to be zero. We have shown E J_n annihilates V_(n-2). Since J_n preserves this subspace, E itself annihilates it.

Only the last row e of E can be nonzero, and e_(n-1)=0. For any arbitrary values at coordinates 0,...,n-2, there is a vector in V_(n-2) with exactly those values. Since e annihilates all of them and ignores the last coordinate, every remaining entry of e is zero. Hence E=0 and L=H^lambda, completing the induction.

For the converse, if L=H^lambda, L is real diagonalizable by its Pascal basis. Both H^lambda and J_n preserve the binomial flag V_0 subset V_1 subset ... subset V_(n-1). On V_j/V_(j-1), H acts by lambda_j and J by (-1)^j. Thus HJ is upper triangular in any basis adapted to this flag, with diagonal lambda_0,-lambda_1,... . The same argument applies to every top-left block, which is again a binomial transform of the truncated diagonal. This proves the characteristic-polynomial identity for every block, hence the global property. QED.


## Significance and limits

The source already proved the easy direction (Proposition 2.3), the converse away from an exceptional algebraic set (Theorem 2.4), and the conjecture for n<=4 by determinant calculation. The present contribution is the all-dimensional converse, including the stochastic boundary and the positive parameters on the exceptional set. The known-row maximum principle constrains each signed eigenvector after the appropriate number of finite differences. The zero-tail coefficient obstruction removes a boundary configuration in which positivity of an old diagonal parameter fails. These steps explain why neither generic spectral uniqueness nor an argument assuming an infinite moment extension suffices. The theorem is about this particular strengthened spectral condition and binomial transforms; it does not settle the source's separate reversibility conjecture. The finite rational computations mentioned in the supplied discovery and review test identities and signs but are not proofs of universal claims. The endpoint is now formalized without a boundary hypothesis. The optional, unused identification of the algebraic flag with polynomial evaluations is not included.

## Prior art (independent review's assessment)

Source Lemma 2.2 gives the Pascal formula, its eigenvectors, and the finite-difference entries; Proposition 2.3 proves the entire easy direction H^lambda ⇒ global property. These should be reused conceptually. Source Theorem 2.4 / Ochiai–Sasada–Shirai–Tsuboi Theorem 2.17 gives the converse only off an exceptional algebraic locus. Distinctness alone is explicitly insufficient (Example 2.5 has a negative entry); stochasticity alone is also insufficient (its other example repeats diagonal entries). The published theorem does not show their conjunction avoids the exceptional locus.

Theorem 2.9 classifies *global eigenbasis action*, an extra hypothesis unavailable here. Section 6 describes stochasticity inside the binomial family, not a converse from the spectral property. The earlier 1403.6797 Theorem 2.34 characterizes stochastic matrices already in VP, via probability measures; Theorem 2.35 still assumes its exceptional-set condition E. Neither may be invoked to assume the classification being proved. Extending an arbitrary finite stochastic spectral example to an infinite moment matrix would itself require an unproved bridge.

A standard maximum principle supplies only one ingredient: constancy of a harmonic vector for the known-row substochastic system. It does not on its own force all eigenvectors into the polynomial flag, nor handle the zero old diagonal. The independent review found that the shortest complete route still requires the shifted-row argument, zero-tail obstruction and eigenvector-span induction above. The review therefore did not classify this as ROUTINE; this is a bounded assessment rather than a claim of global priority.


The review's searches were bounded, not a certification of global priority. It read the actual typeset journal text, whose conjecture remains stated as open, and screened the cited generic-case results and relevant citing mathematical papers. ProbXiv refused access and that refusal was respected. The formalization lane made no new web requests and relied on the supplied source and independent review for the historical discussion. The separate final-check report records a fresh bounded registry, issue and citation search.

## Reproducibility

All submitted Lean modules use specific imports and the copied 32 GiB runner, with one Lean thread and affinity to at most two CPUs per run. All 30 modules are compiled and independently kernel checked from an empty build directory. Receipts are listed in REPORT.md. Both endpoint declarations print only `[propext, Classical.choice, Quot.sound]`. A checked two-dimensional witness, H^(1,1/2), satisfies stochasticity, distinct eigenvalues, and the source global property, so the formal hypotheses are jointly satisfiable. The appendix is generated by `python3 -I build_packet.py`, which verifies that every fenced module is byte-identical to src in dependency order. Rebuild sequentially with `./rebuild.sh`, or use `python3 -I rebuild_parallel.py` (at most three runner jobs, each restricted to two CPUs; no more than six nominal cores). No unproved theorem, new axiom, native evaluation tactic or hidden model equivalence is used in the checked modules.

## References

1. J. R. Britnell and M. Wildon, *Involutive random walks on total orders and the anti-diagonal eigenvalue property*, Linear Algebra and its Applications 641 (2022), 1–47, DOI 10.1016/j.laa.2022.01.018; arXiv:2102.08469v1.
2. The independent review of MathDB 349778, `../round2-review-RH-sol61-20261120-r1/REVIEW-349778.md`, verdict PASS, and its result.json.
3. The Opus cross-model confirmation, `../round2-confirm-G12-opus-20261120-r1/CONFIRM.md`, section 349778.
4. The supplied discovery proof, `../fresh-shard047-discovery-sol61-20261119-r2/PROOF-349778.md`.
