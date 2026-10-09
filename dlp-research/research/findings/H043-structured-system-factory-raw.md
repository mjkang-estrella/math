# H043 structured-system Factory Opus raw report — UNACCEPTED

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h043-structured-system-constructions-factory-opus-20261009-r1`.
Provider/model: acpRegistry_factory_droid / claude-opus-5-5. Terminal result.
Raw mathematical and cost rejections require independent review. Provider usage footer is unverified metadata, not research evidence. No experiment admitted.

# H043 report: no new solving operator found in the coordinate/algebra lens

This pass produced no public operator that meets the corrected H041 gate. The best supported exponent is still 1/2, and verified complete-work improvement is still **NONE**. I did not run anything, import executables, edit files, launch child tasks or commit. I did not read any other H043 proposals. I did not revisit H006/H038 Farey or height-lattice work, the H039 hybrid, or the H034 cap.

The gate I tested against: m=5, B=p^(1/5), sparse B² linear algebra and constant success overhead. Under those conditions, each decomposition attempt must cost D < p^(3/10) = B^(3/2). Setup, rank and witness costs are charged separately.

## Access and runtime

- **ePrint returned HTTP 403** for 2017/1262 (McGuire–Mueller) and 2017/609 (APS), with and without a browser user agent. The iris.unitn link from search was truncated and returned 400. FetchUrl cannot read PDFs.
- **Primary sources I did read:**
  - Semaev, arXiv 1504.01175, §§1–3. It gives the S3 chain system (4). For prime fields its factor base is small residues, and the paper says no solver was given.
  - Amadori–Pintore–Sala, Oxford accepted manuscript, §§1–3.4. The factor base is built from random known-log targets, so only one relation is needed. The cost is (q·m^m/s^m)·T(E,m,V), and T is unknown; the authors write "We do not claim this result" about beating r^(1/2).
  - Bi–Cheng–Rojas, arXiv 1204.1113: Theorem 1.1 and Corollary 1.2.
  - Cafure–Matera, arXiv math/0406085: abstract only.
- APS was already reviewed in H001/H013. My read only confirms that scope.
- No model or provider failure occurred.

## Mechanisms I built and rejected on paper

None of these survives. I record them as negative evidence, not as candidates.

### A. Geometric-resolution / rational-point solver for PKM, APS and Semaev-chain systems

- **Operations:** Present the decomposition system as a straight-line regular sequence. That is either S_{m+1}(x, x_R) with f_i(x_i), or PKM's low-degree chain ending in L_n(x_{i,n}) = 0. Run a Kronecker-type solver (Giusti–Lecerf–Salvy style, or the Cafure–Matera rational-point variant), then extract signs, labels and the scalar, and verify.
- **Gain source:** The solver's cost depends on program size and the geometric degree δ of intermediate varieties, not on the Macaulay degree of regularity. PKM chains have small program size.
- **Why it fails:** Every per-variable constraint, including a terminal chain equation, is equivalent to x_i ∈ V. In the direct orders I checked, and with generic linear combinations of the equations, the intermediate variety after the (m−1)th constraint contains about B^(m−1) fibres. So δ is at least about B^(m−1), which is p^(4/5) at m=5, far above B^(3/2).
- **Cafure–Matera hypotheses also fail:** They require an absolutely irreducible variety of positive dimension and q > δ⁴. The decomposition variety is zero-dimensional, and δ⁴ > p here.
- **Scope:** Any B-point factor base over F_p has degree at least B. This constrains solvers whose cost is parameterized by degree. It says nothing about F4/F5-type solvers or other presentations, and it is not a lower bound on the problem.
- **Falsifier:** Already decided by the degree count above.

### B. Torus filter as the H021 output-sensitive reporter

- **Operations:** Take S = x⁻¹(μ_u) with u ≈ q^(2/3) and known-log lists of size n ≈ q^(1/3). For each P in list A, compute h_P(X) = Res_Y(S3(x_P, X, Y), Y^u − 1) in closed form using Lucas powering. Take gcd with Π_B(X) to report the matching points B. Then do the second-level signed matching, recover the scalar and verify.
- **Possible gain:** If the reporter were output-sensitive, the whole method would cost q^(1/3), as stated in H021.
- **Why it fails:** h_P has degree 2u, so each query costs about u + n, and the total is about n·u ≈ q. Fixing Y instead costs u·n as well. The bivariate Res_Y polynomial has about 4u² coefficients.
- **Unsupported step:** An index answering "which B satisfy x(P+B)^u = 1" in polylog time plus output size. That is a power-residue condition of order about p^(1/3), and I know no structure that supports it. This is a named-schedule rejection only.
- **Prior art:** H021, H007 AC2, Wagner 2002.

### C. Base-change Weil descent (E over F_{p²}, factor base x ∈ μ_B ⊂ F_p)

- **Operations:** Choose a target R with x_R ∉ F_p and Weil-restrict S_{m+1} = 0 into two equations over F_p.
- **Why it fails:** Each P_i is either rational (Frobenius acts as +1) or a twist point (Frobenius acts as −1). Applying (1 ± Frobenius) splits any relation into two independent decompositions: R₊ in E(F_p), and R₋ in the twist's q-part. Here 2 is invertible on the odd-order E(F_p).
  - The E(F_p) part is a decomposition with at most m−1 terms. Its success probability is a product of two events, and it still faces the same grid-constrained solve.
  - If x_R ∈ F_p, there is no descent at all.
- **Prior art:** The Gaudry and Diem setting over F_{q^n}.

### Short screens

- **Two pencils of lines:** Lines through fixed points A and A₂ give free relations P + P′ = −A. Composing the two pencils gives translation by A − A₂, so the only relations are progression orbits. That is H042's sumset scope, with no new information.
- **Monomial-subtorus tuple families:** This is a reparametrization of the same problem: a fixed-degree polynomial with a μ_B grid. It has fewer tuples and lower success.
- **Correspondence fibre sums:** These are constant because Hom_{F_p} = 0. This is just the Riemann–Roch/Semaev function-family view.
- **Bi–Cheng–Rojas:** Sparse root detection costs q^((t−2)/(t−1)). Even m=2 gives 9-term polynomials and cost q^(7/8).
- **Kedlaya–Umans / multipoint evaluation:** Already covered by H020.

## What would change the conclusion

The remaining open problem is clean. Given a fixed-degree S_{m+1}(·, x_R) and a structured V (μ_B or a PKM chain), find one zero in V^m at cost below B^(m/2−1)·p^(o(1)). That means beating meet-in-the-middle (B^(m/2)) by more than a factor of B. Two solver families are now accounted for:

- The norm/resultant family saves one coordinate and inflates degree by B (H009, H010, H019 and the native pass).
- The degree-parameterized family pays δ ≥ ~B^(m−1) (mechanism A).

The only named family still unpriced is F4/F5 with small degree of regularity on PKM chains. The cheapest falsifier would be a degree-of-regularity growth check on tiny μ_{2^n} chain systems at m=5. That would need a solver run, which the consumed H034 cap does not admit, and finite sizes cannot prove asymptotics.

---
*Factory usage — local bridge. This turn: 3,842,646 tokens · ≈1,289,432 Factory credits. Saved session total: 3,842,646 tokens · ≈1,289,432 Factory credits (including recorded subagents). Credits are a local estimate, not a dollar charge.*
