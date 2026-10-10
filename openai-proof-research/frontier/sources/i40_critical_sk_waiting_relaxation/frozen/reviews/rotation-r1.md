# Review R1 of `proposals/rotation.md` (Candidate R)

Reviewer: independent adversarial review sub-agent, round 1.
Upstream revision: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` (matches `sources/upstream.json`).
Upstream truth assumed, per `AGENTS.md`. No previous findings existed.
I did no finite testing. Everything below is checked by hand.

## Verdict

**Accept with corrections.** Every mathematical claim in the Theorem is
correct, and the proof is correct up to the minor precision fixes in §3.
The **novelty framing must change** (§2, corrections C1–C4). Parts (1)+(2)
together are *logically equivalent* to μ(π)=2. They are not a downstream
consequence carrying new information. Parts (2) and (3) do not use the
upstream theorem at all. The key small-divisor inequality already appears,
in substance, inside the upstream proof of Corollary `thm:flinthills`. It
should be recorded as a new-to-this-project reformulation, not a new
theorem.

## 1. Source check

- Pinned `build/main.tex`, `\label{thm:main}` (lines 64–71): "for every real
  ν>2 there is an integer Q(ν) such that |π−p/q| ≥ q^{−ν} (p∈Z, q∈Z,
  q≥Q(ν))". It applies to all fractions, reduced or not. Lines 73–77 say the
  threshold is ineffective. They also say exponent 2 differs from a uniform
  bound c/q², "or equivalently from bounded continued-fraction partial
  quotients". The proposal's paraphrase (ε=ν−2) is accurate.
- Pinned `build/sections/series.tex`, proof of `thm:flinthills` (lines
  47–94). It derives ‖qπ‖ ≥ c q^{1−ν} for **all** q≥1, with the finite
  exceptions absorbed using irrationality. It then derives
  |sin n| ≥ (2/π)‖qπ‖ with q the nearest integer to n/π and n ≥ πq/2.
  Combining the two gives |sin n| ≥ c′ n^{1−ν}. That is exactly the
  multiplier bound in the proposal's Part (1) (see C3). Corollary
  `series:generalized` (Σ n^{−a}|sin n|^{−b} converges iff a>max{1,b}) is
  a different statement. It does not duplicate the Sobolev claim.
- Prior bounds quoted upstream (main.tex lines 113–135): Zeilberger–Zudilin
  give μ(π) ≤ 7.103205334137…; Salikhov gives 7.606308…; Hata gives
  8.01604539…. Bai 2026 is only a *claim*, < 7.101862832357.

## 2. Novelty and attribution: required corrections

**C1 (equivalence, not consequence).** For every irrational β, a uniform
loss τ is admissible for L_β exactly when ‖kβ‖ ≥ c k^{−τ} for all k≥1.
Hence

  inf{admissible τ} = μ(β) − 1.

This is the standard "irrationality measure equals 1 + the infimum of
small-divisor exponents" identity. Also μ(1/π)=μ(π), by GL₂(Z)/Möbius
invariance of the irrationality exponent. So "the infimum loss for
R_{1/π} is exactly 1" ⟺ μ(π)=2. Replace the sentence "The contribution here
is the sharp infimum … using the new input" with:

> Parts (1)–(2) are an equivalent reformulation of μ(π)=2 in terms of the
> rotation cohomological equation, through the classical identity
> inf loss = μ(α)−1 and μ(1/π)=μ(π). They add no information beyond
> upstream Theorem 1.1. They are recorded as a new-to-this-project
> explicit-angle corollary, with no new-to-literature claim.

**C2 (input dependence by part).** State explicitly:
- Part (1) uses upstream Theorem 1.1.
- Part (2), both the single-mode and fixed-forcing versions, holds for
  **every irrational α**. It uses only Dirichlet's theorem.
- Part (3)'s equivalence holds for every irrational α (with π replaced by
  1/α). It also does not use upstream.

So the only part that depends on upstream is the upper bound "loss 1+δ
for every δ>0".

**C3 (upstream already contains the divisor bound).** For α=1/π,
d_k = e^{2ik} − 1, so |d_k| = 2|sin k|. The multiplier is the Flint–Hills
denominator itself. Add:

> The bound |d_k| ≥ c_δ|k|^{−1−δ} is |sin k| ≫_δ k^{−1−δ}. This is
> established inside the upstream proof of Corollary `thm:flinthills`
> (`sections/series.tex`), although it is not stated as a labelled result.

**C4 (quantify the "older finite bound" improvement).** Replace "Smooth
solvability itself already followed from older finite irrationality bounds
for π" with:

> Before the upstream result, the best proved bound μ(π) ≤ 7.103205334137…
> (Zeilberger–Zudilin) gave admissible loss 6.103205334137…+δ, and smooth
> (C^∞) solvability. The upstream result lowers the infimum loss to exactly
> 1. The improvement is genuine relative to the pre-upstream literature,
> but it is the standard translation of the exponent improvement.

Bai's bound is only claimed. Do not cite it as an established improvement.

**C5 (Matheus links).** The Matheus blog posts are about Roth-type interval
exchange maps. That is a generalisation, not the right primary attribution
for circle rotations. Keep them if desired, but add or replace them with
the classical rotation statement: the cohomological equation
u∘R_α − u = f for Diophantine α loses τ+ε derivatives (Kolmogorov 1954;
Arnold 1961; standard in Herman 1979 and in textbooks such as Katok–Hasselblatt). Phrase it
as "classical", without specific theorem numbers unless they are checked.

**C6 (ineffective constant).** In Part (1), add: "C_δ is independent of s
and is not effective, because Q(ν) in upstream Theorem 1.1 is not
effective."

## 3. Line-by-line proof check

**Fourier setup.** For L u = u∘R_α − u, the k-th coefficient is
(e^{2πikα}−1)û(k) and d_0=0. Correct. The inequality
4‖t‖ ≤ |e^{2πit}−1| = 2|sin πt| ≤ 2π‖t‖ is correct, by Jordan's inequality
and |sin x| ≤ |x|.

**Reciprocal normalisation (objection 1). Resolved, correct.** Let k ≥ 2
and let m be the nearest integer to k/π. Then m ≥ 1 and m ≤ k/π + 1/2 ≤ k.
We have ‖k/π‖ = |k/π − m| = |k − πm|/π = m|π − k/m|/π.

For m ≥ Q(2+δ), upstream (with q=m, p=k) gives m|π−k/m| ≥ m^{−1−δ}.
Therefore ‖k/π‖ ≥ m^{−1−δ}/π ≥ k^{−1−δ}/π, using m ≤ k and −1−δ < 0.
As k→∞, m→∞, so only finitely many k have m < Q. For those k,
‖k/π‖ > 0 by irrationality.

*Correction (minor):* write "for k ≥ 2" in place of "for k>0 sufficiently
large let m … Then m ≥ 1". Also write "m ≤ k" explicitly in place of "m is
comparable to k". Only the upper comparison is used. Negative k: d_{−k} is
the complex conjugate of d_k. Fine.

**Part (1).** We need (1+k²)^s/|d_k|² ≤ C_δ² (1+k²)^{s+1+δ}. This holds
because |d_k| ≥ c′_δ|k|^{−1−δ} and |k|^{2+2δ} ≤ (1+k²)^{1+δ}, with
C_δ = 1/c′_δ. Termwise domination gives ℓ²
convergence with weight (1+k²)^s, so û defines an element of H^s_0.
L is a Fourier multiplier, so L u = f holds coefficientwise and hence in
𝒟′. Uniqueness: any distributional solution has û(k) = f̂(k)/d_k for k≠0.
**Correct for every real s.** (Objection 2, real orders: fine. Nothing uses
s ≥ 0.)

**Part (2), single mode.** By Dirichlet, irrational α has infinitely many
k ≥ 1 with ‖kα‖ < 1/k, so |d_k| < 2π/k. Take f = e_k. The ratio
‖u‖_{H^s}/‖f‖_{H^{s+r}} = (1+k²)^{−r/2}/|d_k| exceeds k(1+k²)^{−r/2}/(2π),
which is ≍ k^{1−r} → ∞. Correct for all real r<1, negative r included.

**Part (2), fixed forcing (objection 2). Correct.** Take strictly
increasing k_j with k_j^{1−r} ≥ j². This is possible since 1−r > 0. Then
‖f‖²_{H^{s+r}} = 2Σ j^{−2}.

The H^s contribution at k_j is (1+k_j²)^{−r}/(j²|d_{k_j}|²), which is
greater than (1+k_j²)^{−r}k_j²/(4π²j²). For r ≥ 0, (1+k²)^{−r} ≥ 2^{−r}k^{−2r}
when k ≥ 1. For r<0, (1+k²)^{−r} ≥ k^{−2r}. So c_r = 2^{−max(r,0)}/(4π²)
works. Then k_j^{2−2r}/j² ≥ j⁴/j² = j², so the sum diverges.

The constant only affects û(0), and f has real symmetric coefficients, so
f is real. f ∈ H^{s+r} is automatically a distribution. The sentence about
polynomial growth is redundant but harmless.

*Correction (minor):* state c_r = 2^{−max(r,0)}(4π²)^{−1} explicitly. Also
say "strictly increasing k_j" so that the coefficients are well defined.

**Part (3), endpoint (objection 3). Correct, with one addition.** The
uniform estimate ‖L^{−1}f‖_{H^s} ≤ C‖f‖_{H^{s+1}} on H^{s+1}_0 is
equivalent to sup_{k≠0} (1+k²)^{−1/2}/|d_k| < ∞. That is equivalent to
inf_{k≥1} k‖kα‖ > 0, which does not depend on s. This is the standard
characterisation of badly approximable α.

*Add:* "Mere solvability (for every f ∈ H^{s+1}_0 some u ∈ H^s exists) is
equivalent to the estimate, by the closed graph theorem applied to the
multiplier map." This lets "an estimate holds" be read either way.

Reciprocal transfer. The identity |1/α − q/p| = |α − p/q|·q/(|α||p|) is
correct, since 1/α − q/p = −q(α − p/q)/(αp). The argument works as
follows:
- If |1/α − q/p| < η, with η small relative to 1/α, then q/p is near 1/α.
  Hence |q| ≍ |p| and p/q is near α.
- Badly approximable α gives |α − p/q| ≥ c/q². Then
  |1/α − q/p| ≥ c/(|α||p||q|) ≥ c′/p².
- The remaining fractions satisfy |1/α − q/p| ≥ η ≥ η/p².
- Apply the same argument to 1/α to get the converse.

Correct. This is also the classical fact that bad approximability is
invariant under the GL₂(Z) action (tail-equivalent continued fractions).
That fact can be cited instead.

Status: whether π is badly approximable is open. The upstream paper
explicitly does not settle it (main.tex lines 75–77). The proposal's
statement is accurate.

**"Why the endpoint is a real gap."** Take a_n = n+1. Then q_{n+1} ≥ a_{n+1}q_n
and ‖q_nα‖ < 1/q_{n+1}, so q_n‖q_nα‖ < 1/a_{n+1} → 0. Hence α is not badly
approximable. Also μ = 2 + limsup log a_{n+1}/log q_n, and q_n ≥ n! gives
log(n+2)/log n! → 0, so μ=2. Correct. (q_n ≥ n! is a stronger and cleaner
justification than "at least geometrically"; either suffices.) Optionally
add the classical natural example e = [2;1,2,1,1,4,1,1,…]: μ(e)=2, and e is
not badly approximable.

**Infimum statement.** The admissible set contains every 1+δ and no r<1.
So the infimum is 1, and attainment is the open Part (3). Correct as
stated.

## 4. Optional strengthening (not required)

The same proof applies verbatim to any angle β = (aπ+b)/(cπ+d) with
integers a, b, c, d and ad−bc ≠ 0. This includes the rotation by one
radian, β = 1/(2π), where d_k = e^{ik} − 1. The reason is that μ and bad
approximability are invariant under such maps.

## 5. Summary of required edits

1. C1: reframe as an equivalent reformulation of μ(π)=2, not new
   information.
2. C2: mark Parts (2) and (3) as valid for every irrational α,
   upstream-free.
3. C3: note |d_k| = 2|sin k| and cite the bound inside the upstream proof
   of `thm:flinthills`.
4. C4: give the pre-upstream loss 6.103205334137…+δ (Zeilberger–Zudilin)
   and keep Bai labelled as a claim.
5. C5: attribute the rotation cohomological-equation method classically.
   Matheus/IET links are secondary.
6. C6: C_δ is independent of s and ineffective.
7. Minor proof edits: k ≥ 2 and m ≤ k in the reciprocal step; explicit
   c_r and strictly increasing k_j; closed-graph remark in Part (3).
