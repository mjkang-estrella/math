# MathDB 362890: exact reduction and partial formalization

Status: NOT accepted; no literal all-n Lean endpoint. Root decides. The rising side and first declining comparison have all-n ordinary proofs below. The remaining declines reduce explicitly to a current public Omega sign theorem. That theorem and its transitive dependencies have NOT been independently rebuilt in this lane. Thus the complete result is reported conditionally, not as an independently certified discovery. There is a serious routine-corollary/subsumption issue if the public sign theorem is usable.

## Statement fidelity

Chen–Kitaev–Zhang, arXiv:2404.18517v1, Section 3, Conjecture 1, page 17, concerns every n >= 3 and each of lmax, rmax, lmin, rmin on ALL separable permutations. The live arXiv abstract page on 2026-11-03 lists only v1 (29 April 2024). The entire cached v1 text was read, including Sections 1, 2.2 and 3. The author manuscript also retains Conjecture 1. The journal version-of-record body has not been independently obtained. Source receipts and exact hashes are in sources/; the original MathDB raw SHA-256 was independently confirmed as e561fd3b5b71f5bfc92f30c5d9841b446501cbb286d438e241526baf829308d9.

A separable permutation is a positive-length permutation avoiding 2413 and 3142; equivalently it is built from the singleton by direct and skew sums. A position is a left maximum if its entry exceeds every earlier entry, and a right maximum if it exceeds every later entry. Minima reverse the entry comparison. Comparisons are strict, counts unshifted, and the first/last position counts by vacuity. The empty permutation is excluded in the source.

For a_n(k) the number with a given statistic equal to k, the exact weak peak-two assertion is a_n(0) <= a_n(1) <= a_n(2) and a_n(k+1) <= a_n(k) for every k >= 2. Counts vanish above n. The source does not explicitly demand a unique peak or prohibit ties. Below the rise is actually strict for n >= 3.

Reversal sends occurrences of 2413 to 3142 and vice versa, so preserves avoidance; complement does the same. Each is an involution. Reversal sends lmax positions bijectively to rmax positions. Complement sends lmax positions to lmin positions and rmax positions to rmin positions. Their composition sends lmax to rmin. Restrict these involutions to avoidance classes and then to the corresponding statistic fibers. These are cardinality-preserving bijections at each n and k, proving the four distributions equal. This is also source Lemma 1.

## Canonical decomposition and scalar series

Use rmax for the generating-function derivation. Write U(t,z) for all positive separable permutations, J(t,z) for the direct-indecomposable ones, q(t)=U(t,1), and A(t)=J(t,1). For direct sums, rmax comes only from the last nonempty block; for skew sums it adds across blocks. Cutting at the first canonical direct or skew block, with complementary indecomposability related by complement, gives the source Section 2.2 equations (20)–(22). Equivalently,

    U = (1+q) J,
    J = zt + zt(1+q)J + q(1+q)J^2,
    q = t + tq + q^2,    A = q/(1+q).

These are identities on actual permutations, justified by the unique canonical blocks, not arbitrary binary parse trees. One must formalize those bijections; no such Lean bridge has been completed here.

The scalar identity t(1+q)=q(1-q) is used repeatedly. Let q_n=[t^n]q. Then q_0=0, q_1=1, q_2=2, and

    n q_n = 3(2n-3) q_(n-1) - (n-3) q_(n-2)   (n >= 3).

This follows by differentiating q^2+(t-1)q+t=0, eliminating q^2, and comparing coefficients. The quadratic itself also proves all q_n positive. In particular q_10=206098, q_11=1037718. Hence q_11 >= 5q_10, and induction gives q_n >= 5q_(n-1) for n >= 11: use q_(n-2) <= q_(n-1)/5 in the displayed recurrence to obtain q_n >= (29/5-42/(5n))q_(n-1) >= 5q_(n-1).

## Complete ordinary proof of the rising side

Let U_k=[z^k]U. The quadratic gives U_1=t(1+q) and U_2=t^2(1+q)^3. Reduce powers of q using q^2=(1-t)q-t:

    (1+q)^3 = 1-4t+t^2 + (7-6t+t^2)q.

For n >= 5,

    [t^n](U_2-U_1)
      = -q_(n-1)+7q_(n-2)-6q_(n-3)+q_(n-4)
      = (1+9/(n-1))q_(n-2)
          -(5+3/(n-1))q_(n-3)+q_(n-4).

For n >= 13 use q_(n-2) >= 5q_(n-3). The result is at least 42q_(n-3)/(n-1)+q_(n-4)>0. The exact differences for n=3,...,12 are

    1, 3, 9, 30, 110, 434, 1810, 7878, 35462, 164010.

Together with the zero record-zero fiber, this proves the entire rising side for every n >= 3, in ordinary mathematics.

## Complete ordinary proof of the first decline

Let D_2=U_2-U_3. Its exact form is

    D_2=t^2 (1+q)^3(1-q-q^2+2q^3).

The polynomial after removing t^2 reduces to P(t)+B0(t)q, where

    P(t)=1-5t+42t^2-53t^3+19t^4-2t^5,
    B0(t)=7-53t+122t^2-87t^3+23t^4-2t^5.

For m=n-2 >= 6, repeated application of the scalar recurrence gives exactly

    m(m-1)(m-2)(m-3) [t^n]D_2
      = A(m) q_(m-4)+B(m) q_(m-5),
    A(m)=1282m^4-21003m^3+135851m^2-412770m+496440,
    B(m)=-220m^4+3933m^3-27227m^2+88074m-113400.

This algebraic identity can be checked by substituting the recurrence four times; scripts/reduce.py computes it with rational arithmetic and scripts/newton.py independently checks the exact identity at every n=8,...,250. The interpolation step in reduce.py is diagnostic, not the proof of the rational identity: scripts/symbolic.py now independently verifies the exact rational-function identity in the integer polynomial ring, without interpolation, and logs PASS in symbolic-01.log. The Lean recurrence bridge is still outstanding.

For m=20+x, x >= 0,

    A(m)=83677440+20841670x+1952471x^2+81557x^3+1282x^4,
    5A(m)+B(m)=405408480+100886944x+9443108x^2+394118x^3+6190x^4.

Both are positive; these polynomial identities and their nonnegativity are proved in the compiled Lean module. For n >= 22 the right-hand side is

    A(m)(q_(m-4)-5q_(m-5))+(5A(m)+B(m))q_(m-5)>0.

The differences for n=3,...,21 are

    2, 3, 5, 12, 43, 194, 960, 4920, 25608, 134464,
    710528, 3774264, 20141960, 107947136, 580785280,
    3136085880, 16990764744, 92338990720, 503277996736.

Thus the first decline is strict for every n >= 3.

## Uniform remaining tail: explicit Newton bridge

Here u is an independent polynomial variable. Define

    a=u(3+2u), b=u(1+u)^3,
    T_0=1,
    T_r=a T_(r-1)+b sum_(i+j=r-2) T_i T_j   (r >= 1),
    M_r=sum_(j=0)^r binom(r,j) T_j.

An empty sum is zero. Thus T are Motzkin moment polynomials for parameters a,b. Their binomial transform M has parameters 1+a,b. Write M(x)=sum M_r x^r; then M=1+(1+a)xM+bx^2 M^2. This follows either by the substitution M(x)=(1-x)^(-1)T(x/(1-x)) or by coloring the formerly weight-one horizontal steps. Since 1+a=(1+u)(1+2u), solving the record quadratic coefficientwise gives

    U_k(t)=t^k(1+q(t))^3 M_(k-2)(q(t))   (k >= 2).

One verification is to put F=J/(zt), so F=1+(1+q)ztF+q(1+q)ztF^2, and set F=1+zt(1+q)^2 M(zt). Substitution gives exactly the Motzkin equation above. This supplies the correct normalized coefficient formula without assuming positivity.

Define exactly the public Omega kernels

    G_j(u)=(1+u)^2(T_j+T_(j+1))
       -u(1-u)(1+u)(T_j+2T_(j+1)+T_(j+2)).

For k >= 3, put r=k-2 >= 1. The exact difference identity is

    U_k-U_(k+1)
      = t^k(1+q) sum_(j=0)^(r-1) binom(r-1,j) G_j(q).

To prove it, set F_j=(1+u)T_j-u(1-u)(T_j+T_(j+1)). Pascal's identity gives

    (1+u)M_r-u(1-u)M_(r+1)
      = sum_(j=0)^(r-1) binom(r-1,j)(F_j+F_(j+1)),
    (1+u)(F_j+F_(j+1))=G_j.

The second identity is formalized by newton_pair in Partial.lean. Multiply by t^k(1+q)^2 and use t(1+q)=q(1-q) to get the claimed decline identity. All sums are finite and the substitution q(0)=0 is legitimate. scripts/newton.py checks this as a polynomial identity for r=1,...,40. This is a general algebraic argument; the finite check is not used as an all-index proof.

The public theorem RecordNewtonPositivity.actual_q_record_newton_nonnegative states exactly that [t^n]G_j(q(t)) >= 0 for every j,n. If that theorem is validated as a usable supplier, the displayed identity proves ALL remaining declines. Combining the two ordinary scalar arguments above would then resolve the full-class Conjecture 1. This does NOT infer Conjecture 1 merely from Omega's problem title or Conjecture 2; it gives an explicit formula matching the theorem's independent kernels.

## Public dependency and novelty limit

Current Omega HEAD was fetched ONLY via /commits/HEAD and is e4b00585d5883d418860e7fa253bb76eb04f8da7 (commit metadata retained). The pinned raw files RecordPeak, RecordFirstDecline, RecordTransport, RecordNewtonPositivity and the problem/library dossiers were fetched with HTTP 200 receipts. The problem dossier still explicitly leaves the actual-record Newton bridge open for its irreducible Conjecture 2. The sign theorem is a substantial existing public contribution, not new work of this lane. Its statement, recurrence, propagation mechanism, initial-certificate structure and final theorem were inspected; its entire dependency closure was not rebuilt. No blanket assumption of Omega correctness is made.

A source-backed independent proof of the sign theorem is still necessary if root does not accept the published theorem as a supplier. If root does accept it, the remaining mathematical route is a relatively short coefficient/binomial-transform corollary. This is a material significance/subsumption concern under campaign rules, independent of the formalization gap. No credit is requested here.

## Rejected shortcuts and diagnostics

The first exploratory scripts kernels.py and polynomial.py use an INCORRECT normalized Motzkin index/model for actual record counts. A wrong factorial closed form was also explored in algebra.py/polynomial.py; it was not used in the corrected results. Those early logs are retained to make the correction auditable. They supply no valid actual-permutation inequalities. validate-01 failed at n=3 and is superseded by validate-02. The correct formulas are in validate.py and newton.py and are stated above.

Real-rootedness fails already at n=4: after removing z the polynomial is z^3+6z^2+9z+6, whose discriminant is -216. Log-concavity was checked for n <= 250 in the exact row log, without an all-n proof. Coefficient positivity and even the simple coefficient-prefix cone fail for the corrected uncomposed tail kernels, as recorded in validate-02; no hidden polynomial-positivity assumption is used.

## Lean status and exact gaps

formal/Partial.lean compiled with Lean 4.34.1 and the pinned read-only mathlib cache. It contains actual Finset (Equiv.Perm (Fin n)) definitions, literal pattern avoidance, all four strict record counts, and LiteralEndpoint, which is the desired proposition. It does NOT contain theorem mathdb_362890 or a proof of LiteralEndpoint. Compiled lemmas newton_pair, A_shift, AB_shift, A_nonnegative, AB_nonnegative have no unpermitted axioms. The last three axiom reports list only propext, choice, Quot.sound (or a subset).

Remaining formal Props, in dependency order:

1. Cardinality equality of the four actual record fibers under reversal/complement, including avoidance preservation.
2. The unique canonical direct/skew decomposition equivalences and their record laws on the literal avoidance Finsets.
3. The actual generating-function identities U=(1+q)J and J=zt+zt(1+q)J+q(1+q)J^2; scalar recurrence and positivity.
4. The all-index coefficient formula U_k=t^k(1+q)^3 M_(k-2)(q) for k >= 2, and the binomial decline identity for k >= 3.
5. A locally compiled theorem with conclusion forall j n, 0 <= [t^n]G_j(q(t)), with the actual scalar q. The downloaded public text alone is not a local certificate.
6. The recurrence-substitution identity for D_2, the q ratio induction, and exact finite initial inequalities (ordinary decide is allowed; no native_decide).
7. Coefficient extraction, counts above n vanish, and the literal theorem mathdb_362890 : LiteralEndpoint.

Replay: bash scripts/replay.sh. It sets lane-local TMPDIR/cache, one CPU affinity, MALLOC_ARENA_MAX=2, CPU 120 s, wall 140 s, Lean -j1 -M3500. Lean's mapped cache exceeds a 6 GiB virtual-address limit even at small RSS, so the initial RLIMIT_AS attempt failed and was replaced by Lean's managed-memory cap. The successful replay has measured RSS in logs/lean-07.resources.log. Failed earlier logs are retained; they are not successful certificates. No background process remains.
