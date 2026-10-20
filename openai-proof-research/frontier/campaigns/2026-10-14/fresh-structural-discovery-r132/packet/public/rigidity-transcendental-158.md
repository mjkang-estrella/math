# Family 158: Haar rigidity over a transcendental real-closed field

This is a prefreeze screen of the OPTIONAL FOCUS named in the r132 brief. No exact target was frozen. Nothing here is nominated or certified. Sections 3 to 6 are feasibility work done before any freeze decision; they are not presented as a submitted theorem.

Notation follows the source (`def:spectral-groups`), with a prime for the enlarged field. F' is a countable real-closed subfield of R, E' = F'(i), K' = {u in E' : u conj(u) = 1}, D' is the compact dual of the discrete group E', and C' is the image of the continuous characters j(xi), xi in R^2. A K'-invariant probability law nu on D' is *wild* if nu(C') = 0. "Rigidity over F'" means the statement of `thm:rigidity` with these primed objects: every wild K'-invariant law is Haar.

## 1. Full reading of the source rigidity section

r131 read `rigidity.tex` lines 320-618 only. This round read the whole file (lines 1-618) and the whole of `spectral.tex` (lines 1-625) and `transfer.tex` (lines 1-317). The question was whether anything besides the number-field step uses that F is algebraic.

- Lines 1-137 (`lem:compact-tower`): Furstenberg-Zimmer compact tower for an ergodic action of a countable group, finite-rank fiber modules, bounded bases, transfinite stopping by separability. This uses only countability of K and standard Borel structure.
- Lines 139-320 (`lem:multiple-averages`, eq:source-6, eq:source-7): every-Følner mean ergodic theorem, Hilbert-space van der Corput, and power maps u -> u^d. These use that K is countable, abelian and divisible. K' is divisible, because E' is algebraically closed (F' is real closed) and an n-th root of a modulus-one number has modulus one.
- Lines 322-413 (`lem:rigidity-radial`): uses L = sqrt(AB) in F, and that equal nonzero moduli in E differ by an element of K. Both hold over F'.
- Lines 415-505 (`lem:rigidity-general-position`, `lem:rigidity-capped-residues`): the first lemma is stated for number fields only. The second is field-free.
- Lines 507-617 (completion): chooses "a number field N_0 inside F containing the real and imaginary parts of every q_j". This is the only point where algebraicity enters.
- `spectral.tex`: null events (divisibility of K), the line average (invariant mean on F/Z, Bochner on R), the location lemma and relative singularity (square roots in F) all hold for F'.

So r131's diagnosis is confirmed with full reading. **The only algebraic input is the completion step.** After the field-free parts, rigidity over F' reduces to the following radial statement.

**Reduced radial problem.** Let m = e^{-w} : F'_{>=0} -> [0,1] with m(0) = 1 and
- (R1) w(|A-B|) <= w(A) + w(B) for A, B in F'_{>=0} (eq:source-8);
- (R2) for every Følner sequence of K', Avg_{u} m(2r|Re u|) -> m(r)^2 (eq:source-9); also Avg_u m(|A + Bu|) -> m(A)m(B), from eq:rigidity-two-term-limit;
- (R3) I(phi m) = 0 for every phi in C_c(R) (eq:source-2 with a = 1).

Show that m(r) = 0 for every r > 0 in F'.

## 2. Where the completion needs a number field

Suppose m(r) > 0. The source makes A_0 = {u in K' : w(2r|Re u|) <= H} syndetic, with transversals q_1, ..., q_J. For each v in K' it then needs a *good selection*: finitely many k in a fixed finite family of finite sets, with kv in A_0 and a fixed integer relation D_0 * 1 = sum a_k k. Taking real parts gives 2rD_0|Re v| as a bounded integer combination of capped good lengths, and `lem:rigidity-capped-residues` bounds its cost. The selections are q_j S' with S' inside S, a large set in rational general position in N = N_0(i). The relation exists because q_j S' is a Q-basis of N and N contains 1. That needs every q_j inside the finite-dimensional space N.

Over F' the q_j are arbitrary elements of K', and their ratios may be transcendental.

## 3. Repairs tried (all fail)

(a) **Decouple S from the transversals.** Fix any number field N with i in N and take S inside K cap N in general position. Pigeonhole gives j = j(v) and a basis S' inside S with q_j s v in A_0 for s in S'. The relation D_0 = sum a_s s gives D_0 Re(q_j v) = sum a_s Re(s q_j v), so the capped-residue lemma bounds w(2rD_0|Re(q_{j(v)} v)|) when this number is below the cap. The quantity controlled is Re(q_{j(v)} v), not Re v. The index j(v) is chosen by pigeonhole, so for a prescribed small target t the candidates v = q_j^{-1}(t' +- i sqrt(1-t'^2)) may select a different index j', whose real part is not small. The source avoids this only because q_j lies in N and is absorbed into the selection.

(b) **Monomial general position.** Take S inside K' among monomials q^alpha x, with alpha in a box and x in K cap N. If the q_j are N-linearly independent in the relevant sense, then 1 lies only in the alpha = 0 slice. A subset of q_j S of size at least |S|/J can miss that slice entirely, so 1 need not be in its rational span.

(c) **Run the ergodic theory for K_alg = K' cap Q-bar.** The radial identity eq:rigidity-equal-moduli compares two numbers of equal modulus. They are related by an element of K_alg only when A, B lie in F_alg. This reduces to restricting the law to E_alg, where it need not be wild (r131, failure (i)). Averaging along K_alg-Følner sets is not Følner in K' (r131).

(d) **Reuse eq:source-9 along K_alg-cosets.** The every-Følner statement does not give uniform convergence along translates v_N K_alg of K_alg-Følner sets. The multiple-average lemma would need the relative product to be ergodic for K_alg, which is not given.

## 4. Main finding: the full target is at least as strong as refuting Bukh's conjecture in the plane

Primary read in this round: Bukh, *Measurable sets with excluded distances*, arXiv math/0703856v2 (lines 1-140 and 1195-1264 of the text extraction).

- **Bukh, Theorem 1.** For d >= 2 and finite D_1, ..., D_k, if t_1/t_2, ..., t_{k-1}/t_k tend to infinity, then m_{R^d}(t_1 D_1 u ... u t_k D_k) -> prod m_{R^d}(D_i).
- **Bukh, Section 7 conjecture.** "I conjecture that for any dimension d if the elements of D are algebraically independent over Q, then the chromatic number chi_{R^d}(D) is bounded independently of what D actually is." The d = 1 case holds because components are subgraphs of a |D|-dimensional grid. His Theorem 22 proves only that the clique number is bounded by f(d).

**Observation (prefreeze, not nominated).** Suppose rigidity holds over every countable real-closed subfield of R of finite transcendence degree. Then Bukh's conjecture fails for d = 2.

*Derivation.* Let D = {d_1, ..., d_k} be finite and positive, and let F' be the real closure of Q(D) inside R, which is countable and real closed. Re-run `prop:palettes-forward` with the D-distance graph on E'. The group E' ⋊ K' is amenable, and the proper-labelling space is compact and invariant, because du is in E' for d in D and u in K'. Properness gives `<f_i, T_{du} f_i> = 0`. Rigidity over F' kills the wild part b_i at every nonzero displacement. So `<p_i, T_{du} p_i> = 0` on K', and by density and strong continuity also on S^1. The measurable sample then gives a weak measurable coloring for every distance in D. `lem:palettes-density-proper`, applied with u replaced by du (its proof is scale-free), shows that the density-point sets A_i* are disjoint, measurable, D-avoiding and cover a conull set. In balls about the origin, the k proportions sum to one, so some class has upper density at least 1/k. Hence

  chi_D(R^2) >= 1 / m_D(R^2) for every finite D in (0, infinity).  (*)

Now fix k. Take eps > 0 with m_1(R^2) + eps < 1/2; Bukh quotes m_1 <= 12/43. Bukh's Theorem 1 gives R such that every D with consecutive ratios at least R satisfies m_D(R^2) <= (m_1 + eps)^k. Algebraically dependent k-tuples form a countable union of proper subvarieties, so some algebraically independent D has all consecutive ratios at least R. For that D, (*) gives chi_D(R^2) >= 2^k. As k grows, chi_D is unbounded over algebraically independent sets, which contradicts the conjecture for d = 2. QED for the observation.

The density step uses only pigeonhole over balls or cubes centred at the origin. Bukh's formal density convention (his Section 3) was not read. The pigeonhole works for either centred-box convention.

**Consequences for this round.**
1. Full-scope rigidity over transcendental fields, and the "chi = chi_m for every finite D" statement it would yield, would refute a published conjecture. That is not a closable compatibility left by the source. The missing integrated operation is the whole radial completion step, without a known mechanism.
2. Conversely, if Bukh's conjecture holds for d = 2, then for infinitely many k some real closure of Q(d_1, ..., d_k) carries a wild, non-Haar, K'-invariant law. So rigidity genuinely depends on the field. Neither alternative was established here.
3. This strengthens r131's remark (iii). r131 knew the conjecture only through Davies's one-line paraphrase. This round reads the actual statement and gives the exact implication.

## 5. Counterexample attempts (all fail; evidence, not proof)

These rule out the natural sources of wild non-Haar laws over F'. They do not prove rigidity.

(a) **Subgroup indicators.** If H is a K'-invariant additive subgroup of E', then H is a Z[K']-module. But Z[K'] = E'. For t in F' cap [-1,1], u_t = t + i sqrt(1-t^2) is in K' and u_t + conj(u_t) = 2t. Every s in F' is n * 2t with |t| <= 1/2, and i is in K'. So H = 0 or H = E', and 1_H is never a wild non-Haar coefficient.

(b) **Valuation rings.** If v is a nontrivial valuation on E' with v(K') = 0, then the indicator of O_v would be a K'-invariant, positive-definite, wild, non-Haar coefficient. But v(K') = 0 is equivalent to v being conj-invariant. Suppose the residue characteristic is 0, so v(2) = 0. Then v(a + ib) = v(a - ib) forces v(a + ib) = min(v(a), v(b)). Since every sum of squares in F' is a square, the residue field of v restricted to F' is formally real. Baer-Krull then gives an ordering of F' in which O_v cap F' is convex. F' has only its archimedean ordering, so v is trivial. In residue characteristic p, the conj-invariant place has decomposition field F', so (F', v) is henselian. Lifting -1 = x^2 + y^2 from the residue field, by Hensel for p odd, contradicts real-closedness. (The p = 2 case was not written out; nothing here depends on it.)

(c) **Derivation-twisted laws.** Let partial be a derivation of F' extended to E' with partial(i) = 0. Write partial(u) = i u theta(u), where theta is additive on K'. Characters z -> exp(i Re(conj(eta) partial z)), with eta uniform on a circle, transform under K' by a translation along j(R i eta). Restoring invariance through the Bohr closure B_eta of that one-parameter group, with b Haar on B_eta, gives a K'-invariant law. Its Fourier coefficient at z != 0 vanishes unless z is parallel to eta, which is a null event. So the law is Haar.

(d) **Linear (Gaussian-type) laws.** Suppose eta : E' -> C is random, E_alg-linear, with finite second moments, and its law is K'-invariant. Its covariance h(x, y) = E[eta(x) conj(eta(y))] is a K'-invariant, positive semidefinite, E_alg-Hermitian form. In the Hausdorff completion, M_u x = ux is unitary for u in K'. Because Z[K'] = E', each M_z is a finite integer combination of unitaries and M_{conj z} = M_z^*. The closure is a commutative C*-algebra in which E_alg acts by scalars. Every character of it is a ring embedding of E' into C that fixes E_alg and commutes with conjugation. Such an embedding maps F' into R, preserves squares and so order, and is therefore the identity on archimedean F'. By Gelfand, M_z = z. So h(x, y) = h(1, 1) x conj(y), and E|eta(x) - x eta(1)|^2 = 0. Hence eta(x) = x eta(1) almost surely, and every character exp(i Re eta) lies in C'.

Every K'-invariant law restricts on each subspace xE_alg to a K_alg-invariant law. By source rigidity, that restriction is a mixture of a part continuous on xE_alg and a Haar part. Item (d) closes the second-moment linear subcase of "continuous on every algebraic subspace". The general nonlinear and moment-free cases are not addressed.

## 6. Strongest generic reductions tested

- **Real specialization (Artin-Lang).** A finite graph realized at transcendental D specializes to real algebraic D' with all edges kept and possibly more added. This bounds chi_D(R^2) above by algebraic data, which is the wrong direction for (*). Generization from algebraic D' fails exactly for rigid configurations, which is Bukh's heuristic.
- **Restriction to E_alg plus source rigidity.** This leaves characters continuous on every algebraic subspace. Section 5(d) closes only their linear second-moment part.
- **F_alg-line averages** (r131). These fail. Characters that factor through a derivation are continuous on every F_alg-line but not in C'.

## 7. Outcome

PREFREEZE, no nominee. The full optional-focus target was neither built nor refuted. Its full-scope form would refute Bukh's conjecture for d = 2, and its failure would be implied by that conjecture. The repairs in Section 3 fail. The counterexample classes in Section 5 are excluded, but that is evidence only. No algebraic-only or other restricted variant is nominated: the brief forbids it, and the algebraic case is r131's TECHNICAL composition. The implication in Section 4 is a black-box composition of the source transfer, Bukh's Theorem 1 and pigeonhole. It is conditional on an unproved rigidity hypothesis, so it is not a candidate result.
