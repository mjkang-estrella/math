# H015 primary mathematical bridges — raw Opus report, unreviewed

2026-10-08. claudeAgent/claude-opus-5-5, explicit replacement for Factory's
missing-output delivery. Task `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h015-primary-bridges-opus-20261008-r2`.
COMPLETED with substantive output, no pending child work. Raw negative extensions
are NOT accepted without independent review. No experiments were run.

I couldn't find a credible improvement, and none of the bridges I examined justifies an experiment. Verified improvement over the accepted baseline stays **NONE**. I examined five primary-source bridges from ordinary prime-field, prime-order ECDLP to cheaper computation. Four end in scoped obstructions, and the fifth repeats existing work. Nothing was edited and nothing was run. Every argument below is a paper derivation and has not been independently reviewed.

## Sources: what I actually read

| Source | How much I read | Relevance |
|---|---|---|
| [Huang–Raskind, arXiv:0710.2363](https://arxiv.org/pdf/0710.2363) | Full PDF via pdftotext: §1, §5.1.2, §6, theorem statements | Card A |
| [Schütt–Shioda, arXiv:0907.0298](https://arxiv.org/pdf/0907.0298) | Full PDF: §6.11 (Shioda–Tate, Hodge numbers, ρ≤h^{1,1}=10χ, Igusa ρ≤b₂) and §11.17 (integral sections) | Card B |
| [Silverman, "Four Faces of Lifting" slides](https://maths.ucd.ie/~gmg/ECC2007Talks/ECC4FacesOfLifts.pdf) | Full slides | Prior art for Cards B and D |
| [Semaev 2015, arXiv:1504.01175](https://arxiv.org/pdf/1504.01175) | §§2–4.2 | Says outright: "It is not quite clear how the system (4) may be resolved in case q is a large prime" |
| [Abramovich, alg-geom/9609012](https://arxiv.org/abs/alg-geom/9609012) | Search snippet only: gonality of X_Γ ≥ (7/800)·index | Card D |
| [Kleinjung–Wesolowski, arXiv:1906.10668](https://arxiv.org/pdf/1906.10668) | Search snippet/abstract only: fixed characteristic, (pn)^{2log₂n+O(1)} | Card C |
| [Mahalanobis, arXiv:2607.09814](https://arxiv.org/abs/2607.09814) | Abstract only | Zero-minor/hyperplane-poset method, already covered by H004/H008 |
| [Hu, ePrint 2024/1923](https://eprint.iacr.org/2024/1923) | Abstract only | Prime-field "pseudo-index calculus"; abstract says no subexponential method is known; no bounds on the page |
| [Tian, arXiv:2012.07173](https://arxiv.org/abs/2012.07173) | Abstract only | Cubic extensions F_{q³} only; does not transfer |
| Feng–Nitaj–Pan, ePrint 2024/1330 | **Fetch failed (HTTP 403)** again | CSR source gap remains open |

Frey's 1994 finiteness theorem, Merel–Oesterlé, Serre's open image and Poitou–Tate are cited from memory, not fetched. These searches do not prove anything is novel.

## Card A: global duality / signature calculus (Huang–Raskind)

- **Mechanism.** Lift E/F_p to E over a real quadratic field K. Pick a principal homogeneous space χ ramified only at places over p and over ℓ=q. For every global point α, reciprocity gives Σ_v ⟨χ_v, α_v⟩ = 0. The term at the place over p is (signature component) × DL(α mod p). The terms over ℓ are computable formal logarithms. Collect relations, index-calculus style, and solve for the signatures.
- **What it changes.** It replaces height-based lifting with local pairings, so small primes might carry relations, as they do in the multiplicative case.
- **Verified from the source.** Theorem 2 (signature computation ≡ ECDL) is a heuristic equivalence: it assumes rank exactly 1 and E(K_v)/ℓ = 0 at bad places. The authors' own §6.2 says index calculus *cannot* be built this way. By Lang's theorem, an unramified principal homogeneous space is trivial at good places. Bad small places contribute only through the component group.
- **My extension (unreviewed).** A small place carries ℓ-information only in three cases:
  - split multiplicative reduction with v(Δ) ≥ ℓ, so the coefficients have Ω(ℓ) digits;
  - residue norm at least (√ℓ−1)², so ℓ can divide #Ẽ(F_w);
  - places over ℓ itself.

  By Poitou–Tate, the χ-relations are exactly orthogonality to the image of the Selmer group. They therefore encode only:
  - DLs of reductions of global points, which is the Xedni information already covered by JKSST; or
  - Selmer/Ш classes, which need ℓ-descent in K(E[ℓ]) ⊇ K(μ_ℓ), a field of degree ≥ ℓ−1.

  Making the reduction at ℓ anomalous makes the local DL there easy. But finding such a reduction costs about √ℓ SEA trials, and with rank 1 the relations still collapse to Xedni.
- **Costs and verdict.** Expected gain: none. The lifted curve has conductor around p⁸, so any modular or Heegner route costs poly(p⁸). Reject as a relation stream.
- **Cheapest falsifier, and its status.** Compute any non-point Selmer element for the lifted curve in o(ℓ) work. No method is known, and the μ_ℓ degree argument blocks direct ℓ-descent.

## Card B: elliptic-surface specialization (function-field Xedni)

- **Mechanism.** Choose an elliptic surface over F_p(t) whose fibre at t₀ is E (or its twist), with r explicit sections. Specialization ψ: MW → E(F_p) is a homomorphism, and relations are short vectors in ker ψ.
- **Why it looked open.** Over F_p(t), heights grow polynomially (sections have degree ~ height), so the archimedean JKSST/Masser obstruction does not apply. For r ≳ log q, short kernel vectors of polynomial size do exist.
- **Obstruction (derived).** Take a rational elliptic surface (r ≤ 8), i.e. the blow-up of the pencil's nine base points p_i on the plane-cubic fibre. A section has class eH − Σm_iE_i. By Abel's theorem on the fibre, s(t₀) = e·h − Σ m_i p_i. So the Mordell–Weil coordinates *are* integer coefficients on fibre points with unknown logs. The kernel search is exactly an 8-point small-coefficient relation problem in E(F_p), which costs about √q by rho.
- **General principle.** Specialization factors through the fibre's Picard group. Shioda's height pairing gives *global* intersection numbers (s·O) as a known quadratic form. The *local* term at t₀ is precisely the DL indicator.
- **Supporting obstructions.**
  - A torsion section of order q forces the base to cover X₁(q), whose genus is about q²/24.
  - Ulmer-style high rank needs d | p^n+1 and χ ~ d/6, with sections over F_{p^{2n}}(t). Because rank ≤ 10χ−2, rank r ≳ log q needs χ ≥ r/10. A non-isotrivial explicit family of that size, hitting a generic j, is unknown for large p. Legendre-type explicit families have rational 2-torsion, so they cannot have a prime-order fibre.
- **Verdict.** Gain: none. The surface adds no information about the specialization logs. Reject.
- **Falsifier.** An algorithm that finds a section meeting O at t₀ on an explicit surface in o(√q). On rational surfaces that is equivalent to an 8-dimensional EC relation solver.

## Card C: transferring the systematic equations behind the quasi-polynomial finite-field DLP (BGJT / Kleinjung–Wesolowski)

- **Mechanism.** Imitate the "free splitting" of X^{p₀}−X and the low-degree Frobenius representation.
- **Obstruction.** That method needs the target group to sit inside a structure over a *small* field, with Frobenius acting as a known non-identity map of low degree. On E(F_p), π acts as the identity. Every endomorphism acts as a known scalar λ, and [λ] already costs only O(log q) group operations. x^p−x splits over all of E(F_p) together with its twist, and gives only the trivial relation.
- **The MOV route also fails.** Moving to F_{p^k} needs embedding degree k ~ q, and that field has large characteristic, which is outside Kleinjung–Wesolowski's fixed-characteristic theorem.
- **Verdict.** No transfer for ordinary prime-field curves.

## Card D: global torsion lift + elliptic logarithm (known prior art, sharper cost)

- **Mechanism.** Find E/K with a K-rational q-torsion point reducing to G. Q then lifts uniquely to kT̂, and k follows in polynomial time from the complex elliptic log (AGM plus lattice reduction).
- **Prior art.** Silverman's slides already cover this; Serre's theorem gives degree ≈ cq⁴ for curves over Q.
- **What I add (from memory, unreviewed).**
  - Merel–Oesterlé alone only forces degree ≳ log q.
  - But a *prescribed residue* (E,G) needs a closed point of X₁(q) of controlled degree. By Frey, if infinitely many points of degree ≤ d exist then the gonality is ≤ 2d. Abramovich gives gonality ≥ 7(q²−1)/1600 (snippet-verified).
  - So below about q²/460 there are only finitely many such points, and they cannot cover generic targets. A map-fibre construction costs Ω(q²) degree.
- **Verdict.** Rejected.

## Card E: Semaev 2015 system (4) over prime q

This duplicates the PKM / auxiliary-variable chain work already recorded in H004. The source itself gives no prime-field method, so it is not a new card.

## Five-item report

1. **Best supported work:** the classical square-root reference with automorphism constants. Nothing here changes it.
2. **Verified improvement:** NONE.
3. **Hypothesis from this lens:** global-lift bridges (duality, function-field, torsion) might give relation streams. All three reduce either to the multidimensional DLP or to an object of degree Ω(ℓ) to Ω(q²).
4. **Evidence:**
   - Against: Huang–Raskind's own §6.2, the Abel/blow-up identity, the Frey/Abramovich bound, and the μ_ℓ degree argument.
   - For: only that function-field heights are polynomial, and that only removes JKSST, not the kernel search.
   - Not supported: no experiments, and the 2024/1330 source is still unread.
5. **Next test that could change the assessment:** no numerical run is justified. Only one result would reopen these cards: a sub-√q algorithm that finds small-coefficient relations among r explicit points of E(F_p). Equivalently, a section of an explicit elliptic surface meeting O at t₀. That would directly be a new ECDLP algorithm, so it is not a cheap gate.

   Two cheap paper steps remain:
   - an independent review of Card A's Poitou–Tate orthogonality claim and Card B's Abel identity;
   - a retry of the ePrint 2024/1330 PDF, which the open CSR m≥3 question depends on.
