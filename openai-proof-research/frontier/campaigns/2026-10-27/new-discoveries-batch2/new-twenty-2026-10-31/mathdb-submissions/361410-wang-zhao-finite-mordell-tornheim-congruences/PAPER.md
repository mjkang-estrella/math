# Wang--Zhao finite-sum congruences: a proof with a Lean certificate

Stage 3 continuation, 2026-11-20. MathDB 361410. Editorial revision after independent final review. **Formal status: COMPLETE.**
The Lean theorem `FiniteMT.wang_zhao_conjecture_3_4 : FiniteMT.SourceConjecture`
proves all five assertions with the unchanged source definitions and ranges.
Its only axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Source and literal definitions

Crystal Wang and Jianqiang Zhao, *Mordell--Tornheim Zeta Values, Their
Alternating Version, and Their Finite Analogs*, arXiv:2401.03380v1,
pp. 3, 11--12; the source PDF is retained in the original packet at `sources/2401.03380.pdf`. The live arXiv history has only v1. The open journal version, WSEAS Transactions on Mathematics 22 (2023), 980–987, DOI 10.37394/23206.2023.22.107, retains the same conjecture, numbered (14)–(18) rather than arXiv (12)–(16).
The MathDB record was read with the prescribed corpus reader, from this lane.
The three relevant pages were rendered and inspected in stage 1; their
local source copies are preserved here. This continuation does not claim
an independent new source-page inspection or prior-art search.

The source declares: “Let N and N₀ be the set of positive integers and
nonnegative integers, respectively.” It defines the depth to be d and the
weight by “|s| := s₁ + ··· + s_d”. On p. 3 it states:

> Let \(\mathcal P_p\) be the set of positive integers not divisible by p.
> For any positive integers \(r,d,s_1,\ldots,s_d\) and any prime p, we define
> \[
> Z_{p^r}(s_1,\ldots,s_d):=
> \sum_{\substack{k_1+k_2+\cdots+k_d=p^r\\k_1,\ldots,k_d\in\mathcal P_p}}
> \frac{1}{k_1^{s_1}k_2^{s_2}\cdots k_d^{s_d}}.
> \]

Here is Conjecture 3.4 as printed, with notation typeset in Markdown:

> **Conjecture 3.4.** Let \(r\in\mathbb N\), p be a prime and
> \(\mathbf s\in\mathbb N^d\) such that \(p>|\mathbf s|+1\).
>
> 1. If d = 4 and |s| is odd:
> \[
> Z_{p^r}(\mathbf s)\equiv p^{2r-2}Z_p(\mathbf s)\pmod{p^{2r-1}}.\tag{12}
> \]
> 2. If d = 4 and |s| is even:
> \[
> Z_{p^r}(\mathbf s)\equiv p^{r-1}Z_p(\mathbf s)\pmod{p^r}.\tag{13}
> \]
> 3. If d = 5 and |s| is even:
> \[
> Z_{p^r}(\mathbf s)\equiv p^{2r-2}Z_p(\mathbf s)\pmod{p^{2r-1}}.\tag{14}
> \]
> In general, if r ≥ 2 and d + |s| is odd then we have
> \[
> Z_{p^r}(\mathbf s)\equiv0\pmod{p^{2r-2}}.\tag{15}
> \]
> If r ≥ 2 and d + |s| is even then we have
> \[
> Z_{p^r}(\mathbf s)\equiv0\pmod{p^{r-1}}.\tag{16}
> \]

The source then prints the sharpness example
\(Z_{13^3}(8,1,1,1)\equiv13^4 Z_{13}(8,1,1,1)\pmod{13^5}\),
with failure modulo \(13^6\). The congruence is kernel-certified as `printed_example13`, as a consequence
of clause (12). The separate failure modulo 13^6 is not formalized here and is
not used in the conjecture proof.

The exact Lean definitions beside these source definitions follow. The file
was copied verbatim from the proof lane, as required. In a source summand,
each denominator is a p-unit. Its modular inverse is its usual p-integral
reduction. `coordinate_isUnit` proves the needed unit property; the prototype
also proves its formulas with the actual `ZMod` inverse. The source-to-carry reindexing is proved in `DigitReindex.lean` and
`CarryReindex.lean`; unit inversion, concrete moments, and the full lift
are connected in `CarryFiber.lean` and `DoubleLift.lean`.

```lean
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity

open scoped BigOperators
noncomputable section
namespace FiniteMT

def weight {d : ℕ} (s : Fin d → ℕ) : ℕ := ∑ i, s i

/-- The literal rational sum, represented modulo `p ^ k`.
    In the source range every denominator included by the filter is a unit. -/
def sumMod (p r k : ℕ) {d : ℕ} (s : Fin d → ℕ) : ZMod (p ^ k) :=
  ∑ x : Fin d → Fin (p ^ r),
    if (∀ i, 0 < (x i).val ∧ ¬ p ∣ (x i).val) ∧
        (∑ i, (x i).val) = p ^ r then
      ∏ i, (((x i).val : ZMod (p ^ k))⁻¹) ^ s i
    else 0

/-- All five conclusions of Wang--Zhao Conjecture 3.4. -/
def Conclusions (p r d : ℕ) (s : Fin d → ℕ) : Prop :=
  (d = 4 → Odd (weight s) →
    sumMod p r (2 * r - 1) s =
      (p : ZMod (p ^ (2 * r - 1))) ^ (2 * r - 2) * sumMod p 1 (2 * r - 1) s) ∧
  (d = 4 → Even (weight s) →
    sumMod p r r s = (p : ZMod (p ^ r)) ^ (r - 1) * sumMod p 1 r s) ∧
  (d = 5 → Even (weight s) →
    sumMod p r (2 * r - 1) s =
      (p : ZMod (p ^ (2 * r - 1))) ^ (2 * r - 2) * sumMod p 1 (2 * r - 1) s) ∧
  (2 ≤ r → Odd (d + weight s) → sumMod p r (2 * r - 2) s = 0) ∧
  (2 ≤ r → Even (d + weight s) → sumMod p r (r - 1) s = 0)

/-- Target proposition only. No proof of it is claimed by this file. -/
def SourceConjecture : Prop :=
  ∀ (p r d : ℕ) (s : Fin d → ℕ),
    p.Prime → 0 < r → 0 < d → (∀ i, 0 < s i) →
    weight s + 1 < p → Conclusions p r d s

#check SourceConjecture
#print axioms sumMod
#print axioms SourceConjecture
end FiniteMT

```

## Complete written proof

The following proof was supplied to this lane and checked in the independent
Opus review. The formal certificate implements it with the coefficient and
homogeneity arguments described below. The equation numbers in this proof are internal
and differ from source equation numbers when explicitly described as such.
The proof is included in full, with the exact finite sums connected to the
carry vectors by proved Euclidean and finite-field reindexings.


Put \(w=\sum_i s_i\). For \(d=1\) the defining sum is empty, so the two general claims hold. We henceforth take \(d\ge2\). The hypothesis implies \(p>d+1\). In fact the general divisibility argument below allows arbitrary positive exponents whenever \(p>d+1\); the weight bound is used additionally for the initial total-carry sum.

For any positive exponent vector \(\mathbf t\) of length \(d\), define a column vector, indexed by \(1\le b\le d-1\), by
\[
 T_r(\mathbf t)_b=
 \sum_{\substack{0<x_i<p^r,\ p\nmid x_i\\\sum_i x_i=bp^r}}
          \prod_i x_i^{-t_i}.
\]
The first coordinate of \(T_r(\mathbf s)\) is \(Z_{p^r}(\mathbf s)\). Let \(R\) reverse the carry coordinates: \((Rv)_b=v_{d-b}\). For \(\epsilon\in\{1,-1\}\), write \(P_\epsilon=(I+\epsilon R)/2\). These projections are defined over \(\mathbb Z_{(p)}\).

### 1. Carry counts and their first two moments

For \(1\le a,b\le d-1\), set
\[
 D_{ab}=\{\mathbf y\in\{0,\ldots,p-1\}^d:\sum_i y_i=ap-b\},\qquad
 M_{ab}=|D_{ab}|.
\]
Let \(L_{ab}=\sum_{\mathbf y\in D_{ab}}y_i\), which is independent of \(i\) by symmetry. Then
\[
 L_{ab}=\frac{ap-b}{d}M_{ab}. \tag{1}
\]
Every entry of \(M,L\), and each second moment
\(\sum_{D_{ab}}y_i^2\), \(\sum_{D_{ab}}y_i y_j\) for \(i\ne j\), is divisible by \(p\).

Here is an elementary proof including the second moments. Put
\(F(z)=1+z+\cdots+z^{p-1}\). Over \(\mathbb F_p\),
\(F(z)=(1-z)^{p-1}\). The generating polynomials for the zeroth moment, first moment, second falling-factorial moment, and mixed moment are respectively
\[
 F^d,\quad zF'F^{d-1},\quad z^2F''F^{d-1},\quad (zF')^2F^{d-2}.
\]
The last three are, modulo \(p\), respectively
\[
 z(1-z)^{d(p-1)-1},\quad
 2z^2(1-z)^{d(p-1)-2},\quad
 z^2(1-z)^{d(p-1)-2}.
\]
For \(k=0,1,2\), write
\[
 d(p-1)-k=(d-1)p+(p-d-k).
\]
Since \(p>d+1\), the last term is between 0 and \(p-1\). In characteristic \(p\),
\[
 (1-z)^{d(p-1)-k}=(1-z^p)^{d-1}(1-z)^{p-d-k}.
\]
The coefficient at degree \(ap-b-k=(a-1)p+(p-b-k)\) vanishes: its residue \(p-b-k\) modulo \(p\) exceeds \(p-d-k\). Thus all the displayed moments vanish modulo \(p\). Finally \(y_i^2=y_i(y_i-1)+y_i\).

The digit involution \(y_i\mapsto p-1-y_i\) maps \(D_{ab}\) to \(D_{d-a,d-b}\). Consequently
\[
 RM=MR. \tag{2}
\]
Put \(B=\operatorname{diag}(b-d/2)_{b=1}^{d-1}\). Then \(RB=-BR\), and (1) gives
\[
 L=\frac{pBM-MB}{d}+\frac{p-1}{2}M. \tag{3}
\]

We also need one additional power of \(p\) on one parity subspace:
\[
 M P_{(-1)^{d+1}}\in p^2\operatorname{Mat}_{d-1}(\mathbb Z_{(p)}). \tag{4}
\]
To prove it, inclusion-exclusion gives
\[
 M_{ab}=\sum_{j=0}^{a-1}(-1)^j\binom dj
             \binom{(a-j)p-b+d-1}{d-1}. \tag{5}
\]
The upper entry is nonnegative for these terms because \(p>d+1\); terms with \(j\ge a\) have no combinatorial contribution. Regard each binomial in (5) as a polynomial in \(p\) with denominator \((d-1)!\), a \(p\)-unit. Its constant coefficient is zero. Its coefficient of \(p\) is
\[
 (a-j)v_b,\qquad
 v_b=\frac{(-1)^{b-1}(b-1)!(d-1-b)!}{(d-1)!}.
\]
Thus \(M_{ab}\equiv p c_a v_b\pmod {p^2}\), where
\(c_a=\sum_{j=0}^{a-1}(-1)^j\binom dj(a-j)\).
But \(v_{d-b}=(-1)^d v_b\), so the row \(v\) annihilates the \(R\)-eigenspace of eigenvalue \((-1)^{d+1}\). This proves (4).

### 1a. A differential proof of the projected carry gain

The Lean continuation uses the following alternative to the general
inclusion--exclusion evaluation for (4). This is a complete algebraic
derivation and does not depend on a numerical matrix check.

Write \(c_n^{(d)}=[X^n]F(X)^d\). Differentiating
\((1-X)F(X)=1-X^p\) gives
\[
 (1-X)(F^d)'=dF^d-dpX^{p-1}F^{d-1}.
\]
Consequently
\[
 (n+1)c_{n+1}^{(d)}-(n+d)c_n^{(d)}
 =-dp[X^n](X^{p-1}F^{d-1}).
\]
Take \(n=ap-b-1\), \(1\le b\le d-2\). The last coefficient is
zero if \(a=1\), and is \(M^{(d-1)}_{a-1,b}\) otherwise. It is
divisible by \(p\) by the zeroth-moment result at depth \(d-1\).
The depth-\(d\) coefficients are also divisible by \(p\), so reducing the
display modulo \(p^2\) gives
\[
 bM_{ab}+(d-1-b)M_{a,b+1}=0\pmod {p^2}.
\]
Set \(n_0=d-2\), \(v_i=M_{a,i+1}\). Multiplying this recurrence by
\(\binom{n_0}{i}\), using
\((i+1)\binom{n_0}{i+1}=(n_0-i)\binom{n_0}{i}\), and cancelling the
unit \(i+1\), induction proves
\[
 \binom{n_0}{i}v_i=(-1)^i v_0 \pmod {p^2}.
\]
The binomial coefficients are units: each divides \(n_0!\), and \(n_0<p\).
Their symmetry now gives
\(M_{a,d-b}=(-1)^dM_{ab}\pmod {p^2}\). Reindexing the second half of
\(MP_{(-1)^{d+1}}v\) by \(b\mapsto d-b\) proves (4) for every vector.
The empty carry range is automatic.

There is also a useful division-free form of the projected first-moment
gain. Put \(\eta=(-1)^{d+1}\), \(M=M_{ab}\), \(N=M_{a,d-b}\), and
\[
 C=L_{ab}-\eta L_{a,d-b}+\eta L_{d-a,b}-L_{d-a,d-b}.
\]
Using \(dL_{ab}=(ap-b)M_{ab}\) on these four entries and \(RM=MR\),
\[
 dC=(2a-d)p(M-\eta N)+(d-2b)(M+\eta N).
\]
The first term has two factors of \(p\), and so does the second by the
column parity just proved. Since \(d\) is a unit, \(p^2\mid C\).
This is the coefficient of \(4P_\eta L P_{-\eta}\). It is the concrete
coefficient estimate used by the formal matrix aggregation in
`MatrixProjection`, `MatrixDivisibility`, `ProjectedDerivative`, and `ProjectedLift`.

### 2. Lifting with the error retained

Define
\[
 U_r(\mathbf t)=\sum_{i=1}^d t_i T_r(\mathbf t+\mathbf e_i).
\]
Writing every lifted coordinate uniquely as \(x_i+p^r y_i\), its low digits have total \(bp^r\), and the upper digits belong to \(D_{ab}\). A Taylor expansion gives
\[
 T_{r+1}(\mathbf t)
 \equiv M T_r(\mathbf t)-p^r L U_r(\mathbf t)
                  \pmod {p^{2r+1}}. \tag{6}
\]
For completeness, the expansion of the product is its old summand times
\[
 1-p^r\sum_i\frac{t_i y_i}{x_i}
 +p^{2r}\left(
    \sum_i\binom{t_i+1}{2}\frac{y_i^2}{x_i^2}
   +\sum_{i<j}\frac{t_it_jy_i y_j}{x_i x_j}\right)
 \pmod {p^{3r}}.
\]
The quadratic coefficients sum to multiples of \(p\) by Section 1, and \(3r\ge2r+1\). The first moment is the same for every \(i\), yielding the single vector \(U_r\). Thus (6) holds also at \(r=1\), with no dropped term of valuation 2.

First establish, simultaneously for all positive exponent vectors \(\mathbf t\),
\[
 T_r(\mathbf t)\in p^{r-1}\mathbb Z_{(p)}^{d-1}. \tag{7}
\]
It is true for \(r=1\). If true at \(r\) for all exponents, both \(T_r\) and \(U_r\) are divisible by \(p^{r-1}\). Since \(M,L\) are divisible by \(p\), (6) proves it at \(r+1\). In particular, (6) also implies the useful weak recurrence
\[
 T_{r+1}(\mathbf t)\equiv M T_r(\mathbf t)\pmod {p^{r+1}}. \tag{8}
\]
Indeed the correction has valuation at least \(r+1+(r-1)=2r\ge r+1\).

Reflection of the low coordinates, \(x_i\mapsto p^r-x_i\), gives, with \(\eta=(-1)^{|\mathbf t|}\),
\[
 R T_r(\mathbf t)
       \equiv\eta\bigl(T_r(\mathbf t)+p^r U_r(\mathbf t)\bigr)
                       \pmod {p^{2r}}.
\]
Together with (7), this yields
\[
 (I-P_\eta)T_r(\mathbf t)\in p^{2r-1}\mathbb Z_{(p)}^{d-1}. \tag{9}
\]
Applying the same argument to each \(\mathbf t+\mathbf e_i\) shows
\[
 P_\eta U_r(\mathbf t)\in p^{2r-1}\mathbb Z_{(p)}^{d-1}. \tag{10}
\]
No restriction on the shifted weights is needed for (7)–(10).

### 3. The projected recurrence at double precision

Suppose \(d+|\mathbf t|\) is odd, so \(\eta=(-1)^{d+1}\). We claim
\[
 T_{r+1}(\mathbf t)
       \equiv M P_\eta T_r(\mathbf t)\pmod {p^{2r+1}}. \tag{11}
\]
This is the decisive step.

Project (6) by \(P_\eta\). Since \(M\) commutes with reflection, its first term is \(M P_\eta T_r\). Split
\(U_r=P_{-\eta}U_r+P_\eta U_r\).
For the latter piece, (10) and \(L\in p\operatorname{Mat}\) show that its contribution after the factor \(p^r\) is divisible by \(p^{3r}\), hence by \(p^{2r+1}\).

For the former piece, (3) gives
\[
 P_\eta L P_{-\eta}
   =\frac{p P_\eta B M P_{-\eta}
                 -P_\eta M B P_{-\eta}}d.
\]
The scalar multiple of \(M\) disappears because opposite parity projections are orthogonal. The first displayed term is divisible by \(p^2\) since \(M\in p\operatorname{Mat}\). For the second, use \(BP_{-\eta}=P_\eta B\) and (4). Hence
\(P_\eta L P_{-\eta}\in p^2\operatorname{Mat}\).
By (7), \(U_r\) is divisible by \(p^{r-1}\), so this part's contribution has valuation at least \(r+2+(r-1)=2r+1\). This proves the projected form of (11). Finally (9) at level \(r+1\) says its omitted parity component is divisible by \(p^{2r+1}\), proving the unprojected statement.

Induct on \(r\) in (11), using (4). At \(r=1\) integrality is enough, and every lift adds two powers of \(p\). Therefore
\[
 T_r(\mathbf t)\in p^{2r-2}\mathbb Z_{(p)}^{d-1}
             \quad\text{if }d+|\mathbf t|\text{ is odd}. \tag{12}
\]
This proves source (15). Equation (7) proves source (16), including its stated parity range.

### 4. An initial finite-field cancellation

Under \(w<p-1\),
\[
 \sum_{b=1}^{d-1}T_1(\mathbf s)_b\equiv0\pmod p. \tag{13}
\]
At level one, each coordinate is in {1,...,p-1}. Every tuple whose
integer total is divisible by p has its total in {p,2p,...,(d-1)p}; thus the
left side is exactly the sum over nonzero field coordinates with total zero.
`initial_total_reindex` proves both this partition and the coordinate equivalence.

Choose a unit c in F_p with c^w != 1. Such a unit exists because the
multiplicative group is cyclic of order p-1 and 0<w<p-1. Scaling every
coordinate by c permutes this zero-sum set and multiplies its summand by
c^(-w). Therefore the sum S satisfies S=c^(-w) S. The multiplier differs
from 1, and a field has no zero divisors, so S=0. These are the actual
arguments of `residueCarrySum_scaling`, `residueCarrySum_zero`, and
`initialCarryCancellation`; no multinomial expansion is a formal premise.

### 5. Explicit depth 4 and depth 5 carry modes

The following elementary matrix identities follow by expanding (5); an independent exact rational-polynomial check is retained beside this revised paper in `carry_algebra.py` and `carry-algebra.json`. (The original packet does not contain the advertised `scripts/carry_algebra.py`.) They can also be verified by multiplying the three or four displayed vectors by (5).

For \(d=4\), the vectors
\[
 v_1=(1,-2,1)^T,\quad v_2=(-1,0,1)^T,\quad v_3=(1,4,1)^T
\]
form a basis and satisfy \(M v_j=p^j v_j\). Their reflection signs are respectively \(+,-,+\); their coordinate sums are respectively \(0,0,6\). The change-of-basis determinant is -12, a unit at every \(p>5\).

If \(d=4\) and \(w\) is odd, \(P_{-}\) has image spanned by \(v_2\). Thus (11) and (9) give
\[
 T_{r+1}(\mathbf s)\equiv p^2T_r(\mathbf s)\pmod {p^{2r+1}}. \tag{14}
\]
In fact \(MP_-=p^2P_-\), and multiplying the discarded part from (9) by \(p^2\) puts it in precisely the asserted modulus. Induction in (14) proves source (12).

If \(d=4\) and \(w\) is even, let \(a_{r,j}\) be the coefficients of \(T_r\) in the displayed basis. By (9), \(a_{r,2}\) is divisible by \(p^{2r-1}\), hence by \(p^r\). Also \(a_{1,3}\) is divisible by \(p\), by (13) and the coordinate sums. Equation (8) implies
\(a_{r+1,3}\equiv p^3a_{r,3}\pmod {p^{r+1}}\), so induction gives \(a_{r,3}\in p^r\mathbb Z_{(p)}\).
Consequently
\[
 (M-pI)T_r=(p^2-p)a_{r,2}v_2+(p^3-p)a_{r,3}v_3
                \in p^{r+1}\mathbb Z_{(p)}^3.
\]
Together with (8) this proves
\[
 T_{r+1}(\mathbf s)\equiv p T_r(\mathbf s)\pmod {p^{r+1}}. \tag{15}
\]
Induction proves source (13).

For \(d=5\), the symmetric subspace has basis
\[
 v_2=(1,-1,-1,1)^T,\qquad v_4=(1,11,11,1)^T,
\]
with \(Mv_2=p^2v_2\), \(Mv_4=p^4v_4\). Their coordinate sums are 0 and 24. Thus
\[
 M P_+v=p^2P_+v+
       \frac{p^4-p^2}{24}\Bigl(\sum_b v_b\Bigr)v_4. \tag{16}
\]
When \(w\) is even, put \(S_r=\sum_b T_r(\mathbf s)_b\). Since the coordinate sum is unchanged by \(P_+\), (11) and (16) give
\[
 S_{r+1}\equiv p^4 S_r\pmod {p^{2r+1}}.
\]
Starting with (13), induction yields \(S_r\in p^{2r-1}\mathbb Z_{(p)}\). Equations (9), (11), and (16) now imply
\[
 T_{r+1}(\mathbf s)\equiv p^2T_r(\mathbf s)\pmod {p^{2r+1}},
\]
since the two error terms have valuations at least \(2+(2r-1)=2r+1\). This proves source (14) by induction.

Taking the first coordinate throughout proves all five assertions. The three scaling assertions at \(r=1\) are identities, so no small level has been omitted. All small admissible primes are covered by \(p>d+1\); no asymptotic prime assumption was introduced. \(\square\)


## The formal certificate

All 41 preceding source modules are preserved byte-for-byte, including the
literal endpoint. New modules add the aggregation of the four-entry first-moment
gain, the projected derivative correction, and `projectedCarryLift`. In the
aggregation, the coefficient before 1/4 is

    C_ab = L_ab - eta L_a,d-b + eta L_d-a,b - L_d-a,d-b.

The first-moment identity and count reflection give

    d C_ab = (2a-d)p(M_ab-eta M_a,d-b)
               +(d-2b)(M_ab+eta M_a,d-b).

The first term has two factors of p; the second has two by projected count
parity. Since d is a p-unit, C_ab is divisible by p^2. The finite matrix
identity in `projected_matrix_cross` sums these actual coefficients against
the derivative vector. Its opposite-parity part has the weak bound p^(r-1),
and its same-parity part has the stronger bound p^(2r-1). The retained outer
p^r makes both corrections zero modulo p^(2r+1). This proves (11) without a
residual matrix or moment hypothesis. `strongCarryDivisibility` and
`assertion15` implement the resulting induction and clause (15).

For the exact small-depth calculation, `count_series` proves

    F(X)^d = (1-X^p)^d (1-X)^(-d)

as an identity of formal power series, using the explicit inverse of
(1-X)^d with coefficient choose(d-1+n,d-1). Extracting coefficients gives
`count_formula_cutoff`; removing zero terms gives exactly (5) in
`count_formula`. Each depth-4/5 row is then computed as an integer polynomial
in p. Multiplication by 6 or 24 clears the binomial denominators. The
identities `matrix4minus`, `matrix4plus`, and `matrix5plus` follow by finite
sums and ring normalization, uniformly for p. These coefficients are units
in the source prime ranges. No table of particular prime values is assumed.

`carryTotal_induction` treats both exceptional total modes, with parameters
(e,f)=(1,3) and (2,4). The concrete bounds are `totalBound4` and `totalBound5`.
`scalarRecurrence12`, `scalarRecurrence13`, and `scalarRecurrence14` implement
the three resulting scalar congruences. All three feed the one existing
`scalar_scaling` induction. `assertion12`--`assertion16` are unconditional
under the exact source hypotheses. `source_of_four` assembles them into
`wang_zhao_conjecture_3_4`, whose type is the unchanged `SourceConjecture`.

The appendix contains every production module in import order, byte-identical
to src/. REPORT.md records exact elaborated statements, axiom output and
successful compile/kernel receipts. The endpoint has no carry, matrix,
recurrence, cancellation or other unproved hypothesis. The development used
only the prescribed guarded runner. Independent final extraction, statement
review and prior-art refresh remain the accepting root's separate review step.

## Significance and limits

The routine general divisibility clause (16) alone is not independently novel.
The substantive completion is the double-precision derivative-retaining lift
and its parity projection, followed by exact small-depth mode cancellation.
The proof is elementary once this projection is identified and builds on known
carry-lifting methods. A formal proof establishes the stated mathematics; it
does not by itself settle the review's bounded novelty or significance judgment.
The printed congruence follows formally; its stronger-modulus failure is not a
certificate endpoint. The pins trust supplied upstream Lean and Mathlib build
artifacts, which were not independently rebuilt here.

## Prior art and novelty qualification

The closest published carry argument is Chen–Zhao, arXiv:1702.08401v2,
Lemma 2.2(ii), and its journal version, JIS 20 (2017), Article 17.6.8,
Lemma 4(ii). It treats the all-ones exponent vector. It is the corresponding
all-ones carry recurrence at modulus p^(r+1), after reducing the carry counts
modulo p^2; it is not literally the present arbitrary-exponent recurrence.
McCoy–Thielen–Wang–Zhao, arXiv:2101.08599, published in IJNT 13 (2017),
109–128, likewise treats all-ones reciprocal products. These works establish
important special cases and methods behind the routine weak divisibility
clause (16). They do not supply the derivative-retaining arbitrary-exponent
lift at modulus p^(2r+1) used here.

The independent final review found no matching proof in the four local
registries, GitHub code searches, or the omega issue and PR searches. The live
source has only arXiv v1, and its journal version retains Conjecture 3.4.
Semantic Scholar's retrieved citing list for Chen–Zhao contains the source
and a 2017 alternating-sums paper. OpenAlex reports zero citations for the
source's journal record. OpenCitations returns no source citations and, for
McCoy et al., a 2022 paper and Shen's 2024 paper on special sums of triple
reciprocals. The accessible 2024 paper concerns fixed all-ones triple sums,
not general exponent vectors or the depth-4/5 laws. A 2026 nearby arXiv paper
(2603.20550) concerns infinite symmetrized zeta functions, not these finite
prime-power congruences.

The full 2024–2026 citing-paper traversal could not be completed: OpenAlex
list/search calls and the remaining Semantic Scholar calls returned HTTP
429 even after the permitted retry. OpenAlex's McCoy record reports seven
citations, whose complete list was not retrieved. A 2025 citing-paper search
hit, Chen Ao and Shen Zhongyan, “Congruences Concerning Quadratic Product
Modulo Primes,” was identifiable, but its full text was not successfully
read. No checked paper proves a clause for general exponents; this is a
bounded negative finding, not complete novelty clearance. The final review
therefore leaves public-list eligibility at DOUBT pending that missing
citation traversal, while passing the mathematics with editorial edits.
