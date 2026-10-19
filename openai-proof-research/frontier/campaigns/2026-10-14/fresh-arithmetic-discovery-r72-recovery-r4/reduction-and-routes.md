# T242Z — reductions, route attempts and proved route limits

Everything below is original work of this recovery. Statements labelled
"source" are the stipulated pinned source242 inputs. Nothing here proves
T242Z; Section 4 states the remaining gap. None of these lemmas is nominated:
they are reformulations or obstructions to specific routes.

Notation. Tri = {k(k+1)/2 : k ∈ ℕ}. "Single-fold over ℤ" means: exactly one
complete integer auxiliary tuple for members and none for non-members, for
every integer input.

## 1. Elementary parametrizations (proved)

**F1.** t ↦ t(2t+1) is a bijection ℤ → Tri.
*Proof.* For t ≥ 0, t(2t+1) = T(2t) with T(k)=k(k+1)/2. For t = −u, u ≥ 1,
t(2t+1) = u(2u−1) = T(2u−1). Every k ∈ ℕ is uniquely 2t (t ≥ 0) or 2u−1
(u ≥ 1), and T is injective on ℕ. ∎

**F2 (Gauss).** Every n ∈ ℕ is a sum of three elements of Tri (classical).

**F3.** The map w ↦ (A,B) = (w(w+1)/2, w(w−1)/2) is a bijection from ℤ onto
{(A,B) ∈ ℕ² : 2A = (A−B)(A−B+1)}, with inverse w = A−B, and A,B ∈ Tri.
*Proof.* For w ∈ ℤ both w(w+1)/2 and w(w−1)/2 are triangular (each is T(j)
for j = w, −w−1, w−1 or −w, whichever is ≥ 0), so lie in ℕ, and A−B = w
gives the equation. Conversely, if (A,B) ∈ ℕ² satisfies it, put w = A−B;
then A = w(w+1)/2 and B = A−w = w(w−1)/2. ∎

## 2. Reduction theorem (proved, conditional only on source Theorem `thm:main`)

Let L ⊆ ℕ³ be the decidable relation: τ ∈ Tri³ and τ is the
lexicographically greatest element of {σ ∈ Tri³ : σ₁+σ₂+σ₃ = τ₁+τ₂+τ₃}.

**Theorem R.** The following are equivalent.

1. T242Z.
2. (N_ℤ): some Q ∈ ℤ[Z,Y₁,…,Y_k] has exactly one integer Y-solution for each
   z ≥ 0 and none for z < 0.
3. (Tri-witness form, purely over ℕ): there is P_L ∈ ℤ[τ₁,τ₂,τ₃,W₁,…,W_m]
   with #{w ∈ ℕ^m : P_L(τ,w)=0} = [τ ∈ L] for all τ ∈ ℕ³, and whose unique
   witness for τ ∈ L lies in Tri^m.
4. The exponential graph Γ = {(z,2^z) : z ∈ ℕ} ⊆ ℤ² has a single-fold
   Diophantine definition over ℤ.

*Proof.* (1⇒2) and (1⇒4): ℕ ⊆ ℤ and Γ ⊆ ℤ² are r.e.

(2⇒1). Let S ⊆ ℤ^n be r.e. Then S⁺ = {(p,q) ∈ ℕ^{2n} : p_i q_i = 0 for all i,
p−q ∈ S} is r.e., so the source gives P⁺ ∈ ℤ[p,q,W₁..W_m] single-fold over ℕ.
Over ℤ impose, with separate Y-tuples for every call,
a_i = p_i − q_i, p_i q_i = 0, Q(p_i,·)=0, Q(q_i,·)=0, Q(w_j,·)=0,
P⁺(p,q,w) = 0. In any solution all p_i, q_i, w_j are ≥ 0 (by Q); then
p_i = max(a_i,0), q_i = max(−a_i,0) (the sign code is unique), w is the
unique ℕ-witness of P⁺ at (p,q), which exists iff a ∈ S, and every Y-tuple
is unique by (N_ℤ). Over ℤ a finite system F₁=…=F_r=0 is equivalent to
ΣF_i² = 0 with the same unknowns. Hence exactly one complete integer tuple
for a ∈ S and none otherwise.

(1⇒3). Apply T242Z to L ⊆ ℤ³: P_ℤ(τ,y) single-fold over ℤ with y ∈ ℤ^m.
Over ℕ use unknowns A_j,B_j with 2A_j = (A_j−B_j)(A_j−B_j+1) and
P_ℤ(τ, A−B) = 0. By F3 the ℕ-solutions correspond bijectively to integer
y = A−B, so the count is [τ ∈ L], and every witness coordinate is in Tri.

(3⇒2). Unknowns t ∈ ℤ³, u ∈ ℤ^m with
z = Σ t_i(2t_i+1) and P_L(t(2t+1), u(2u+1)) = 0 (coordinatewise).
In a solution, τ = t(2t+1) ∈ Tri³ and w = u(2u+1) ∈ ℕ^m solve P_L, so τ ∈ L,
w is its unique witness, and z = Στ_i ≥ 0. For z ≥ 0, F2 makes the finite
set of Tri³-representations nonempty, so exactly one τ ∈ L has sum z; its
witness lies in Tri^m, and F1 determines t and u uniquely.

(4⇒2). If R(z,x,v)=0 defines Γ single-fold, then for z ≥ 0 the only x is 2^z
with one v, and for z < 0 there is none. ∎

**Operation-level reading.** Form 3 says exactly what the source does not
supply: a single-fold ℕ-system in which *every* auxiliary value, including
every inequality slack, Pell coordinate, quotient and digit, is triangular.
The source's operations use arbitrary nonnegative slacks and the uniqueness
of nonnegative square roots (`build/power.tex`, witness-uniqueness paragraph;
sign codes in `build/main.tex` §conventions and `build/elliptic.tex`
rational-code lemma). None of these operations is sign-invariant.

**Routine consequences (no credit).** Over ℤ every r.e. set has a
*finite-fold* representation: substitute w_j = Σ_{l≤4} e_{j,l}² in the
source polynomial (r₄(w) < ∞), and treat integer inputs by sign codes,
whose nonnegativity is also given by four squares. Under T242Z the integer
promise analogue of the source corollary follows by the source's own
specialization argument. Neither is nominated.

## 3. Route attempts and proved route limits

**A1 (Gauss/Lagrange plus canonical selection).** Choosing the
lexicographically greatest representation is single-fold over ℕ by the
source, but the selector's own witnesses need positivity over ℤ. Theorem R
shows this regress is not an artifact: closing it is equivalent to T242Z.

**Lemma O1 (no eventually polynomial witnesses).** Let Q define ℕ
single-fold over ℤ with witness y(z). There are no M ≥ 1, c ∈ ℤ and
φ ∈ ℚ[t]^k with y(z) = φ(z) for all sufficiently large z ∈ c + Mℕ.
*Proof.* ψ(s) = φ(c+Ms) is integer-valued for s ≥ s₀, hence a ℤ-combination
of binomials (s−s₀ choose j), hence integer-valued on ℤ. The polynomial
Q(c+Ms, ψ(s)) vanishes for all s ≥ s₀, so identically. For s < −c/M,
z = c+Ms < 0 has the integer witness ψ(s): contradiction. ∎
Consequence: explicit polynomial normal forms (Cantor-type pairings,
polynomial parametrizations restricted to progressions) cannot supply the
witness; positivity must be carried by non-polynomial (e.g. archimedean or
exponential) structure.

**Lemma O2 (Pell positivity cannot be selected by congruences).** Let D > 0
be a nonsquare, M ≥ 1 and R ⊆ (ℤ/M)². Then
{(y,w) ∈ ℤ² : y² − Dw² = 1, (y,w) mod M ∈ R} is empty or infinite.
*Proof.* The solutions are ±εⁿ (n ∈ ℤ) for the norm-one generator ε of
ℤ[√D]. The image of ε in the finite ring ℤ[√D]/(M) is a unit, so εᴾ ≡ 1 for
some P ≥ 1; membership is P-periodic in n while the ±εⁿ are distinct. ∎
**A2.** Robinson's Pell criterion makes positivity of 4z+2 (never a square)
equivalent to a nontrivial solution of y² − (4z+2)w² = 1; the solutions
for z < 0 are only w = 0. By O2, any additional congruence selection leaves
infinitely many witnesses. Selecting the fundamental solution is a size
comparison, i.e. positivity again. This route reduces (N_ℤ) to itself.

**A3 (square-root recursion).** For every z ∈ ℤ, the integers s with
s² ≤ z < (s+1)² form a singleton if z ≥ 0 and are empty if z < 0. (If z ≥ 0
and s ≤ −1 then (s+1)² ≤ s² ≤ z; so s = ⌊√z⌋.) Hence
Pos(z) ⇔ ∃! s: Pos(z−s²) ∧ Pos(2s+s²−z), and when these hold both
arguments lie in [0, 2√z]. This contracts sizes by a square root but needs
depth about log₂log₂ z and about log z nodes. A fixed polynomial system can
only carry such an unbounded tree through sequence coding, and single-fold
coding over ℤ (digits or residues in canonical ranges) again requires
positivity of quantities as large as the coding base. The source's own
height-window selection (`build/main.tex`, proof overview: choose k with
W_k ≤ u + W₁ < W_{k+1}) is likewise a pair of comparisons, i.e. two
nonnegative slacks. Exact failure point:
single-fold sequence coding over ℤ. No constant-depth contraction to bounded
size exists in this form, since d steps reach only z^{1/2^d}.

**Lemma O3 (fixed-point closure fails for exponential-growth systems).**
Let P(c,w) be single-fold over ℕ and suppose every solution satisfies
max_j w_j ≥ 2^{max_i c_i}. Then there is no solution in which the inputs c
contain, for every j, codes g(e) = e(2e+1) of integers e_{j,1..4} with
Σ_l e_{j,l}² = w_j, unless all w_j ≤ 16.
*Proof.* Put W = max w_j > 0. Some |e_{j,l}| ≥ √(W/4) ≥ 1, and
g(e) ≥ 2e² − |e| ≥ e² ≥ W/4, so max c ≥ W/4 and W ≥ 2^{W/4}, false for
W ≥ 17. ∎
**A4.** Thus feeding canonical four-square certificates of a transcript-type
witness back into the same system cannot represent an infinite set. Whether
the source's specific polynomial has this growth is not claimed.

**A5 (reciprocity).** For odd a, Hilbert reciprocity with b = −1 transmits
sign(a) only as the comparison of a mod 4 with |a| mod 4; the latter needs
|a|, so the route is circular. **A6 (2-adic).** Negativity corresponds to an
infinite 2-adic tail of ones; certifying a finite tail again needs a
comparison r < 2^K.

## 3b. Second round of bridge attempts

**A7 (polynomial bijection ℤ^k → ℕ).** If some integer-valued
f ∈ ℚ[y₁,…,y_k] maps ℤ^k bijectively onto ℕ, then Q = Dz − Df(y) (D a common
denominator) proves (N_ℤ), hence T242Z, with no use of the source beyond
Theorem R. Iterated Cantor polynomials show the same holds for a polynomial
injection ℤ^k → ℤ^m with image ℕ^m. This is the most direct possible
route; the following lemma shows it needs degree ≥ 4.

**Lemma O4.** No integer-valued polynomial of degree ≤ 3 (any k ≥ 1) is a
bijection ℤ^k → ℕ; more generally a nonnegative one has even degree.
*Proof.* Integer-valued polynomials have rational coefficients. Degree 0 is
not injective. If the degree d is odd, the top form f_d is a nonzero
rational polynomial, so f_d(v) ≠ 0 for some v ∈ ℤ^k; f_d(−v) = −f_d(v), so
some w ∈ {v,−v} has f_d(w) < 0 and f(tw) → −∞ as t → ∞ in ℕ, contradicting
f ≥ 0. Let d = 2, f(y) = yᵀAy + L(y) + c with A rational symmetric.
(i) If A is not positive semidefinite, rational vectors are dense, so some
v ∈ ℤ^k has vᵀAv < 0 and f(tv) → −∞. (ii) If A is semidefinite and
singular, ker A is a nonzero rational subspace, so contains v ∈ ℤ^k∖{0};
then f(y+tv) = f(y) + tL(v) for all t ∈ ℤ: if L(v) ≠ 0, f takes negative
values; if L(v) = 0, f is constant on y + ℤv, not injective. (iii) If A is
positive definite, f(y) = (y−y₀)ᵀA(y−y₀) + c′ with y₀ ∈ ℚ^k, and the lattice
count in the ellipsoid gives #{y ∈ ℤ^k : f(y) ≤ N} = ω_k N^{k/2}/√det A +
O(N^{(k−1)/2}). A bijection onto ℕ has count exactly N+1 for every N ∈ ℕ,
forcing k = 2 and π/√det A = 1, i.e. det A = π² ∉ ℚ. ∎
Whether a degree ≥ 4 bijection ℤ^k → ℕ exists is not known to this
recovery; for a positive-definite top form of degree d the same count
forces k = d and vol{f_d ≤ 1} = 1, a period identity this recovery could
neither realize nor exclude. Route stopped there.

**A8 (odd-degree norm forms).** In an order O of a number field of odd
degree, N(−α) = −N(α), so the norm-one equation removes the global sign
that defeats Pell in O2. The exponent sign remains:

**Lemma O5.** Let O be an order in a number field, G ⊆ O^× an infinite
subgroup, M ≥ 1 and R ⊆ O/MO. Then {u ∈ G : u mod M ∈ R} is empty or
infinite.
*Proof.* (O/MO)^× is finite, so G_M = ker(G → (O/MO)^×) has finite index
in G, hence is infinite, and the set is a union of G_M-cosets. ∎
Thus a norm-one unit u = ε^n (or ε₁^{n₁}⋯ε_r^{n_r}) can be pinned to
n ≥ 0 only by an archimedean comparison (|u| ≥ 1 in a chosen embedding),
which is positivity again. Fixing the global sign by odd degree does not
help, because the obstruction lives in the free part of the unit group.

**A9 (self-reference).** One may try to apply the source to a set S_e whose
definition refers to the witness shape of its own polynomial (Kleene
recursion theorem), e.g. S_e = {τ ∈ L : P_{Φ(e)}(τ,w)=0 for some w ∈ Tri^m}.
Two independent failures: (a) the source gives existence of P for each S
and says it "gives existence of an integer polynomial without displaying its
coefficients or a procedure for numerically choosing those constants"
(`build/main.tex`, paragraph before Corollary `cor:unique-h10`), so no
computable Φ is supplied; (b) even with
a computable Φ the fixed point only certifies S_e ⊆ L with triangular
witnesses on S_e, and nothing in the interface ("each r.e. S has some
single-fold P") forces S_e = L; the witness shape of P is not controlled by
the choice of S. Feeding the witness into the input instead is the O3
situation and needs witnesses bounded polynomially in input values.

**A10 (elliptic index sign).** The source's rank-one mechanism measures an
index n through ĥ(nP) = n²ĥ(P), which is invariant under n ↦ −n
(−nP = (x,−y)). Over ℤ the index sign is the sign of a y-coordinate (or of
its numerator code), so this mechanism transports, but does not certify,
positivity.

## 4. Status and remaining gap

T242Z is **unresolved**. By Theorem R it is equivalent, given the source, to
one positivity gadget: a single-fold Diophantine definition of ℕ in ℤ,
equivalently a single-fold ℕ-system for L with triangular witnesses. Lemmas
O1–O5 exclude polynomial normal forms, polynomial bijections ℤ^k → ℕ of
degree ≤ 3, congruence-selected unit groups (any order, any degree) and
transcript fixed points; A9 records why self-reference through the source
interface does not control witness shape, and A10 why the source's elliptic
index mechanism is sign-blind. A3 isolates single-fold sequence coding over
ℤ as the missing operation for the only size-contracting route found.
Lexicographic selection among the finitely many Gauss representations is a
universal condition, so it must pass through the computation encoding,
whose slacks are exactly the unpaid positivity (Theorem R, form 3). No
counterexample or impossibility for (N_ℤ) is known to this recovery.
Unread search hits and the unverified status of (N_ℤ) in the literature are
navigation only; neither novelty nor priority is cleared.
