# Raw H025 Grok independent report — unreviewed

TaskId: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h025-independent-bridges-grok-20261008-r1

Preserved as proposal/claims, not automatic accepted results. Scope and
mathematical/cost exclusions require independent verification before use.

No survivor. Three mechanisms in the requested lanes were priced far enough to close, and none beats negation rho at low memory or the x-only interleaved baby-step giant-step comparator at Θ(√q) memory. Verified improvement stays **NONE**. Nothing was edited, run, or committed.

The public inputs are the ordinary curve, the generator G, and the target Q = [k]G. Group order q is prime, q ≠ p, q ≈ p, gcd(q, p−1) = 1, and the only rational automorphisms are ±1. Memory citations below that are not tied to a file read this session are marked unverified. No external paper was read in full; search hits were snippets only and are not used as bridges.

## 1. Dyadic S3 resultant as an interval-product bridge

**Public computation.** Let P_m(X) = ∏_{j=1}^m (X − x([j]G)), monic. For 1 ≤ m and 2m < q, the abscissae x([j]G) for j = 1..2m are pairwise distinct: x([a]G) = x([b]G) means a ≡ ±b (mod q). H019’s specialization of the third summation polynomial gives the roots of ∏_{i=1}^m S_3(x([i]G), x([m]G), X). For i < m both the sum and the difference abscissae appear; for i = m the diagonal form contributes the single factor (X − x([2m]G)) up to the nonzero unit −4y([m]G)². The resulting root set is {x([j]G) : 1 ≤ j ≤ 2m, j ≠ m}. Hence

P_{2m}(X) = (X − x([m]G)) · ∏_{i=1}^m S_3(x([i]G), x([m]G), X) / C_m,

with C_m ∈ F_p independent of X and nonzero (distinct abscissae, and y([m]G) ≠ 0 because the group order is odd). If P_m is monic, that product is the Y-resultant of P_m(Y) and S_3(Y, x([m]G), X). The case m = 1 matches H019’s diagonal formula and produces (X − x(G))(X − x([2]G)). The case m = 2 reproduces P_4(X)/(X − x([2]G)) by the same root count.

Starting from P_1(X) = X − x(G), the dyadic recurrence builds P_T for T = 2^a using the points [2^b]G, b ≤ a. Those points cost O(log² T) group operations.

**Hoped-for gain.** Baby generation in negation baby-step giant-step costs Θ(T) additions. Replacing it by resultants would leave only the giant phase q/(4T), the project’s negation-BSGS giant count for T stored abscissae, and cut the leading term.

**Costs.** The resultant is bivariate: P_m lies in F_p[Y], while the leading coefficient of S_3 in Y is (X − x([m]G))², not a constant. Evaluation-interpolation uses Θ(T) specializations of a numeric degree-T resultant, Θ(T) work each, so Θ(T²) field operations at the top level and Θ(T²) overall across dyadic levels. A hash of an explicit baby list, after T additions, answers each giant in expected O(1). The polynomial still needs a membership test. Fast multipoint evaluation of a dense degree-T polynomial adds a log² factor that the hash does not pay. At the x-only schedule the baby half is already only (2.5M+S) per stored abscissa. Θ(T²) multiplications are larger than that by a factor T. Θ(√q) coefficients of memory put the algorithm in the high-memory regime, where this build is strictly more field work than generating the same abscissae by additions.

**Prior art.** S_3 and the one-query product are the H019 Bernstein–De Feo–Leroux–Smith resultant identity, already checked in-repo. The search skeleton is negation baby-step giant-step. This is not a memory layout and not a walk step.

**Unsupported assumption.** That some resultant schedule builds P_T and returns the hitting index for cheaper than (b + q/(4b))(2.5M+S) field work at b = θ√q. No such schedule is given. A soft-linear resultant, even if one exists, still has to beat hashing an explicit list; the log² multipoint term grows past any constant saving.

**Falsifier.** Already algebraic: the Θ(T²) interpolation count for this recurrence. An independent check only has to confirm C_m for one m > 2; a wrong unit changes the formula, not the degree or the Θ(T²) bound. Reopen only with an explicit build-and-lookup whose total multiplication count is below the x-only expression above.

## 2. Rational endpoint formula for an orbit sum

**Public computation.** Fix a rational function f on E, regular on the nontrivial rational points (x, y, or the slope from a fixed public point). Form the orbit sum s(k) = ∑_{j=0}^{k−1} f([k]G − [j]G) and hope to evaluate it from the coordinates of Q alone.

**Hoped-for gain.** If s(k) = Φ(Q) − Φ(O) for a rational Φ of degree o(q), and s separates k, one evaluation recovers k. That would be exact recovery with O(1) field work after writing Φ.

**Obstruction.** Translation τ(P) = P − G is a degree-1 automorphism, so deg(Φ ∘ τ^k) = deg Φ. Thus deg(Φ − Φ ∘ τ^k) ≤ 2 deg Φ. On the other side, take f = x, whose only pole is a double pole at O. The translate x ∘ τ^{−j} has its only pole at [j]G. For 0 ≤ j < k < q these poles are distinct, and no other term in the sum has a pole there, so

deg( ∑_{j=0}^{k−1} x ∘ τ^{−j} ) = 2k.

The identity s(k) = Φ([k]G) − Φ(O) for all k < q therefore forces 2 deg Φ ≥ 2(q−1). The same pole addition applies to y (pole order 3 at O) and to a slope with a single uncancelled pole: the sum’s degree grows linearly in k. If instead f itself is a rational coboundary Ψ − Ψ ∘ τ of low degree, the sum collapses to the endpoints, and injectivity in k again forces deg Ψ ≥ q−1 because a degree-D map E → P¹ takes each value at most D times. That is an identity failure, not a runtime claim about high-degree circuits.

**Prior art.** Same degree-counting shape as the H024 diamond-operator bound for a rational function that realizes a character of the scalar, applied here to orbit sums rather than to characters. H018’s rational-image gate (f ∘ [n] = f only for n = ±1) is a different equation.

**Unsupported assumption.** That some rational Φ of degree o(q) agrees with an orbit sum of a non-constant rational f on all rational points. The pole count forbids it.

**Falsifier.** The degree count for f = x. A one-line check for k = 2: x(P) + x(P−G) has poles at O and at G, so it is not a function of [2]P alone of degree 2.

This does not forbid a short straight-line program for a high-degree function. H002’s compact segment circuit remains missing; this pass does not supply one.

## 3. Auxiliary Tate value as an exact scalar residue

**Public computation.** For a small prime ℓ ≠ q, take any ℓ-torsion point T over an extension and evaluate the Tate pairing of the public point Q with T. The hopeful reading is that the value is ζ^k in μ_ℓ, so Chinese remaindering of many such residues recovers k.

**Hoped-for gain.** Each residue would cost one Miller loop in a small extension, and O(log q) primes would determine k, a polynomial complete-work bound.

**Obstruction.** gcd(ℓ, q) = 1, so multiplication by ℓ is bijective on ⟨G⟩. The preimage R = [ℓ^{−1} mod q] Q is rational. Bilinearity gives ⟨Q, T⟩_ℓ = ⟨[ℓ]R, T⟩_ℓ = ⟨R, T⟩_ℓ^ℓ, which is the identity in the Tate codomain. The value is 1 for every rational point and every ℓ ≠ q. It does not depend on k. The Weil pairing e_ℓ is not defined on Q, because Q is not ℓ-torsion. The only prime at which this residue can be nontrivial is ℓ = q, the usual embedding-field pairing. Here p ≡ t − 1 (mod q) with |t| ≤ 2√p, so that residue is a small integer and the extension degree is its multiplicative order modulo q. No small-degree formula is supplied.

**Prior art.** Classical Tate bilinearity. Not a character-sum bias bound, not a p-adic logarithm, and not the H024 power-residue collapse for the division-polynomial normalization φ.

**Unsupported assumption.** That ⟨Q, T⟩_ℓ remembers k when ℓ does not divide q. Bilinearity says it is identically 1.

**Falsifier.** The one-line reduction to an ℓ-th power. No sampling is required.

## What this pass does not reopen

Relation-list indexes, sparse rank and character spikes, p-adic lifts, elliptic divisibility sequences, norm and trace maps, the H024 slope-active escape, and the H024 large-ℓ character window were left as already scoped. Walk-step arithmetic and high-memory arithmetic-progression layouts belong to the other H025 roles. No short circuit, no new detector, and no public feature with a separable scalar came out of the three constructions above.
