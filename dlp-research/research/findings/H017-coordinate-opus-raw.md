# H017 coordinate bridges: raw Claude Opus proposal

Unverified delegate output. Numeric estimates, novelty statements, equivalences and rejection claims below are not accepted without independent review. No experiment or local throughput measurement.

I ended up with **one new mechanism worth carding**, not 3–5. Every other lens I generated died on paper against either the repo's findings or a short argument I give below, so I'm not padding the list. Verified improvement remains **NONE**. I created no files, commits, experiments or child tasks.

I read STATE, H016-ranked-shortlist and RESEARCH_LOOP, then checked the existing cards for overlap. The closest were the H011/H013/H016 fibre and Lang cards, H004 dilation characters, the EDS and Lauter–Stange records, PKM towers, the lattice/CSR cards, slope hashing and multiplicative cosets.

## Card SP3: Singer-plane trilinear form for collinearity

**Construction.** Take E: y² = f(x) over F_p, p > 3, with #E(F_p) = q an odd prime and q ≠ p.
- There is no rational 2-torsion, so f is irreducible. That makes A = F_p[θ]/f(θ) the field F_{p³}.
- The 2-descent map E(F_p)/2E(F_p) → A*/A*² is injective (Silverman, AEC §X.1). Because q is odd its domain is trivial. So x(P) − θ is a square σ(P)² in F_{p³} for every affine P.
- If P1+P2+P3 = O lie on the line y = λx + μ, then f(X) − (λX+μ)² = ∏(X − x_i). Evaluating at θ gives ∏(x_i − θ) = (λθ+μ)², so σ1σ2σ3 = ±(λθ+μ).
- The converse also holds. Suppose the projective class [σ1σ2σ3] lies in span(1, θ), that is, the θ²-coefficient is 0. Comparing degree-≤2 polynomials gives f − ∏(X − x_i) = c²(λX+μ)². So the x_i come from an ±-signed collinear triple on E itself, not on the twist.
- Note that F_{p³}*/F_p* is the cyclic Singer group of PG(2,p), of order N = p²+p+1. Span(1, θ) is a line, which is a translate of a perfect difference set.

**What is new.** Semaev's S3 is biquadratic in each x_i. Taking the descent square roots turns it into a single trilinear form, T(σ1,σ2,σ3) = coefficient of θ² in σ1σ2σ3, on F_p³ × F_p³ × F_p³. Finding a relation becomes finding a zero of a fixed 3×3×3 tensor on three point sets. Equivalently, it is point–line incidence in PG(2,p), or "3SUM into a perfect difference set" in Z/N.

**Paid operation and recovery.**
- Generate three lists of n labelled points a_iG + b_iQ.
- Compute σ for each point with one F_{p³} square root. At 256 bits I estimate this at roughly 2×10³ F_p multiplications per point, against about 6 for a rho step.
- Detect a zero of T. A hit gives a collinear triple, so Σ±(a_i + b_i·k) ≡ 0 mod q, which recovers k when the b-sum is nonzero. Verify kG = Q.

**Expected gain, as a precise gate.** About n³/q triples hit, so n ≈ q^{1/3}. Setup is n square roots and memory is O(n), both negligible. The mechanism beats √q only if the zero detector runs in **O(n^{3/2−ε})**. Note that it must avoid enumerating the n² lines (σ1σ2)^{-1}Λ.

**Main unsupported assumption.** That there is a structured incidence detector that is sub-quadratic in this way. The matrix M[(σ1,σ2), σ3] = T(σ1,σ2,σ3) is an n²×n matrix of rank 3, and we need a zero entry without expanding the rows. I know of no such algorithm over F_p. Pinning this down would refute a 3SUM-type conjecture in a structured setting, so my prior is low.

**Cheapest decisive falsifiers.**
1. On paper (already done): any detector that touches each pair is MITM-equivalent. Computing the line for (σ2,σ3) and meeting it with the conic {z : z² ∈ Λ} costs the same as one group addition, giving n² ≥ √q.
2. A literature check on finite-field Hopcroft and low-rank zero-entry detection. A conditional reduction from integer 3SUM would kill the card.
3. Correctness sanity only: on tiny curves (p ≈ 100), exhaustively compare the T-zeros with collinear triples.

**Prior art.** The 2-descent map and Singer difference sets are classical. The condition itself is S3 in disguise. I found no source that links the square-root linearisation to relation finding ([search](https://arxiv.org/pdf/1504.01175) surfaced only Semaev-type work). That is a search result, not a novelty proof.

## Candidates I generated and killed on paper

Each kill is scoped to the stated construction; none is a universal claim.

| Candidate | Why it dies |
|---|---|
| Incidence configurations with fixed anchors (extends H016) | For a fixed combinatorial type, the configuration exists if and only if Σε_j·A_j + 3n1·Q = O, which does not depend on the slopes or intercepts. Solving the configuration system is therefore just testing one candidate key. |
| Frobenius-type features of isogeny or [ℓ]-division fibres (ℓ ≠ q) | Isogenous curves have order q and the degree is coprime to q, so ψ(E′(F_p)) = E(F_p). The Kummer class δ(P) is then 0, every fibre over a rational point is the same trivial torsor, and the feature is constant. Only the ℓ = q (Lang) case is nontrivial, and that is already H013. |
| Logs of σ(P) in F_{p³}* (subexponential DLP there) | χ(kG) − kχ(G) is a log of a Miller function value at the 2-torsion point (θ,0). That is the EDS/elliptic-net residue setting of [Lauter–Stange](https://arxiv.org/abs/0803.0728), which is equivalent to ECDLP in the subexponential sense. The descent identity is automatic and carries no scalar information. |
| Trace factor bases from E(F_{pⁿ}) to E(F_p) | V must be an F_p-subspace of dimension at least 1, so the factor base has size at least about p. Eliminating the free trace-zero coset falls back to prime-field decomposition with a curve-parametrised base, which is PKM-type and already covered. |
| Sibling-rank walk: share the R±M inverse, step to the lower-ranked point | The image bias gives Σp² = 4/(3N), at most a 1.155× step gain. The cost is about 1M+1S extra on a ~5M+1S step, roughly 1.31×, so the net is about 0.88×. With r jumps the gain is √r for about 2r candidates. This is close to the known simultaneous-± trick. |
| Double covers of E branched at {G, Q}, and their Prym | By translation, the isomorphism class depends only on the coordinates of Q − G. The Prym is generically not isogenous to E, so the induced map is zero. |

One more family was not carded but is not refuted either. Bounded-degree auxiliary families evaluated at x(Q), such as Frobenius traces computed by Schoof's algorithm, are heuristically expected to have Deligne-type correlation of about p^{-1/2} with the log. That is a heuristic, not a proof.

## Five-item summary
1. **Best supported work:** classical √q with the known automorphism constants; nothing here changes it.
2. **Verified improvement:** NONE.
3. **Hypothesis:** SP3, the trilinear linearisation of S3 through 2-descent square roots, gated on a sub-n^{3/2} zero detector at n = q^{1/3}.
4. **Evidence:** the construction is exact, I checked it by hand above, and it has not been run. Any pairwise detector is MITM-equivalent, and the other six lenses are killed in the table.
5. **Next step:** before any code, do a literature and conditional-hardness check on structured finite-field point–line incidence. Drop SP3 if a 3SUM reduction exists.

Sources: [Lauter–Stange, arXiv 0803.0728](https://arxiv.org/abs/0803.0728), [eprint 2008/099](https://eprint.iacr.org/2008/099), [Semaev, arXiv 1504.01175](https://arxiv.org/pdf/1504.01175).
