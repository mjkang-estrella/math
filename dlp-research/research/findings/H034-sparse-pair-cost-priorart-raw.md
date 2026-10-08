# Unaccepted reviewer report

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h034-sparse-pair-priorart-factory-opus-20261008-r1`.
Provider/model: acpRegistry_factory_droid/claude-opus-5-5. Terminal completed.
Preserved verbatim as evidence, NOT accepted wholesale. See H034-finite-contract.md
and H034-review-qualifications.md for root scope and unresolved objections.

# H034 sparse paired-sum generation: prior-art and full-cost review

**Verdict.** Every ingredient of the mechanism is already published, and the payoff is small:

- If the Poisson bridge holds, the method reaches the known ideal birthday constant for random collisions under negation, about 0.886√q keys. Under that same model, nothing in this class can go below 0.886.
- Against the strongest high-memory comparator (GWZ negated grumpy giants with block computation, about 0.90√q, empirical and unproved), the key-count margin is about 1.5%. The spread of GWZ's own measured results puts it anywhere from about 0.7% to 3.8%.
- That margin is used up by seed preparation for q up to roughly 2^66 under my rough operation model. Synthetic tests at testable sizes therefore cannot measure a complete-work gain.
- The more defensible possible value is mathematical. If the Poisson bridge is proved, this would be a proved high-memory x-only constant below the proved 0.943 of H019. That would be a better proved constant, not a complete-work improvement over the empirical comparator.

I found no source using random-label seeds with sparse or C4-free pair-sum dictionaries for discrete logs. That is the result of a bounded search, not a novelty claim. Verified improvement: NONE. The exponent stays 1/2.

## Primary sources: what I actually accessed

PDFs went into `/tmp/h034-review` only. I made no repository edits and ran no experiments or imports.

| Source | Access | Relevance |
|---|---|---|
| Galbraith–Wang–Zhang (GWZ) 2017, published PDF via the semanticscholar mirror | Read: pp. 454–456 (§§1–2.1), Table 3 (p. 459), Table 5 (p. 462), §§4.1–4.3 (Algorithms 1–2, Lemmas 4.1–4.2), §5 (Algorithm 3, the 0.4 factor, rho+Montgomery 0.47) | Paired x(X±Y) with a shared inverse, block computation, the comparators; rho with negation listed as 0.886(1+o(1)), heuristic |
| Bernstein–Lange, *Two grumpy giants and a baby* (cr.yp.to mirror, 2012-07-09) | Read: §§1–2, pp. 3–5 | Slope and anti-collision framework; "even a truly random walk produces a large number of anti-collisions"; critique of the Chateauneuf–Ling–Stinson cost model |
| Chateauneuf–Ling–Stinson, ePrint 2001/094 | Read: abstract page plus the full PostScript text, §§1–2 and §4 (Prop. 1.2, Props. 2.1–2.4, Thms 4.1–4.4) | Slope packings and coverings built from Sidon sets; random-shift Las Vegas algorithm |
| Wang–Zhang 2013 (IEEE EIDWT) | Abstract only (paywalled) | Applies P±Q to rho iteration functions. GWZ §4.1 calls that use "not effective" because walks go in a single direction. |
| Neamah, arXiv 1607.05901 | Abstract only | Not relevant |
| Bernstein–Lange–Schwabe 2011 (negation map) | Not accessed (Cloudflare block) | The 0.886 constant is taken from GWZ Table 3's citation |
| C4-free extremal theory (Reiman bound; Erdős–Rényi–Sós and Brown polarity graphs; Kővári–Sós–Turán) | From memory, not re-accessed | — |

## Prior art, piece by piece

- **GWZ Algorithm 2 is already pair-sum generation over a graph.** Its centers T_j and offsets uT form a complete bipartite graph K_{k,ℓ}, with structured progression labels and deterministic coverage. H034 swaps this for a C4-free graph, random labels and birthday coverage.
  - The swap is necessary. With random labels, every 4-cycle in K_{k,ℓ} makes the same signed 4-support relation appear twice. Example: X_c+U_u = X_c'+U_u' and X_c−U_u' = X_c'−U_u are the same linear form.
- **The 0.886 constant is known.** GWZ Table 3 gives 0.886(1+o(1)) for rho with negation, heuristic. H034 cannot go below 0.886: it is the random model.
  - BL show that structured anti-collision avoidance can beat truly random coverage.
  - The H024 counting floors (0.816 for f=3, 0.770 for f=4) are the only route below 0.886, and none has been attained.
- **The shared inverse for x(X±Y) is known.** It comes from Wang–Zhang 2013 and GWZ §4.1. H034's actual distinction is narrow: it uses the ± pair outside a walk, so GWZ's "single direction" objection to the rho use does not apply.
- **The Sidon / C4-free link is classical.** Chateauneuf–Ling–Stinson Prop. 2.1: points (i, i²) form a slope packing exactly when T is weak Sidon. H034's condition, that no two edge matchings cover the same four vertices, is the graph analogue for symbolic forms. Their Thm 4.4 (random shift, success |σ(S)|/p) is the deterministic-set counterpart of H034's random labels.

## Full-cost audit

**1. Per-key arithmetic.** Exactly 2.5M + S + (I−3M)/(2k) per key, plus about 3 field additions per key. H034 has no center-advance term, while H019 pays an extra 2.5M/(2ℓ+1) per key.
- At k = ℓ = 8, I = 8M, s = 0.8: H034 costs 3.613M and H019 costs 3.778M, a ratio of 0.956.
- At k = ℓ = 64: 3.339M versus 3.359M, a ratio of 0.994.
- The finite edge is a tuning artifact. A fair comparator raises ℓ, at a cost of O(ℓ) offsets and O(kℓ) overshoot.

**2. Seed preparation.** This is the decisive term.
- Reiman's bound forces n ≳ (2m)^{2/3}. With the biaffine or projective-plane incidence graph sized for a cap of c√q keys, n ≈ 2(c/2)^{2/3} q^{1/3}.
- My rough model: fixed-base combs with window about log₂q/3, roughly 5 additions per seed plus about 6q^{1/3} table additions, at about 5.8M per batched addition. Under this model the seed work is about 32·q^{−1/6} of the main work.
- That is about 31% at q = 2^40, 2.0% at 2^64, 0.3% at 2^80, and negligible at 2^256.
- The net margin against grumpy is negative up to about 2^66 and keeps most of its 1.5% only above about 2^75. Using small b_i lowers the constant somewhat but does not change the picture.

**3. C4-freeness is sufficient, not necessary.** This is my own paper observation and is unverified; it should go to the math critic.
- Duplicate relations come only from 4-cycles. Each 4-cycle repeats all 8 of its forms.
- The fraction of duplicated relations is about 2·#C4/m², which is about t²/n⁴ for random-like graphs.
- So n = K·q^{1/4} with K ≈ 6 loses well under 0.1% in keys, and moves the seed crossover down to about 2^56. Repeated edges must be excluded, and the Poisson dependency argument would need redoing for such graphs.

**4. Lower-order duplicates the proposal does not mention.** Two edges sharing a vertex produce 8 match events but only 6 distinct forms: e_j±e_l each appears twice. These are a fraction of about Δ/m ≈ q^{−1/3}, so they are negligible asymptotically but about 0.4% at q ≈ 2^24.

**5. Tail, cap and memory.** Under the Poisson model, store up to a cap of c√q keys and then switch to query-only fresh keys (new seeds and a new graph). Expected keys are √q·[(√π/2)·erf(c) + e^{−c²}/(2c)]:

| Cap c | Expected keys / √q |
|---|---|
| 1.414 | 0.894 |
| 1.5 | 0.891 |
| 2 | 0.887 |

- At H019's worst-case allocation (√(2q) records), that is 0.894 versus 0.943, about −5.2%.
- No published grumpy result exists at that cap. Grumpy's unconstrained worst case is ≤2.7√q, conjectural.

**6. Lookup, records and labels.** Parity with the comparators:
- One probe and one insert per key in a single table.
- Each record stores a fingerprint, an edge index of about ½·log₂q bits, and a sign bit.
- Labels for n seeds are stored or regenerated with a PRF.
- One cost is still unpriced: per-edge seed reads. Ordering the biaffine graph by (x, slope, y) keeps the working set at about 2h ≈ 2q^{1/6} seeds and makes access streaming. I assign no hardware prices.

**7. Special cases.** Each needs paid dispatch:
- A seed equal to O solves the DLP directly.
- x_i = x_j on an edge makes the Montgomery batch product zero. That case must be located, and it also solves the DLP.
- A null relation (Σc_i·b_i ≡ 0, probability about 1/q) means continue.
- Truncated fingerprints need false-match verification.
- Up to two sign candidates need up to two scalar verifications.
- Edge decoding needs F_h arithmetic.
- 2P = O is impossible except P = O, since the order is an odd prime.

## Exact cost gate

At matched peak memory (records, seeds, combs and scratch) and the same record format:

E_H034(c)·√q·C_key(k) + W_seeds(n) + W_fallback + W_dispatch + W_verify < E_cmp·√q·C_key^GWZ(k,ℓ) + W_setup^GWZ

Use E_cmp = 0.90 for the empirical comparator (GWZ range 0.893–0.921) and 0.943 for the proved one. GWZ must be allowed its optimal ℓ. At leading order the condition becomes W_seeds / (√q·C_key) < about 0.014 against grumpy, or about 0.057 against H019.

## Cheapest decisive falsifiers

1. **Paper first.** Evaluate the gate above with a concrete seed method and a frozen graph. If the q threshold lies above every size the loop can test, a synthetic run can test only the collision law, not complete work.
2. **Exactness note.** z_i = a_i + b_i·k are independent and uniform whatever k is. So a simulation in Z_q of the canonical values ±(z_i ± z_j) reproduces the first-collision law exactly, with no curve arithmetic.
3. **Statistical power.** The coefficient of variation of the stopping time is about 0.52, so resolving 1.5% needs about 10⁴ runs, roughly 4×10⁷ key events at q ≈ 2^24. That is about 40 times the 1M-event cap. Within the cap, only gross failures are detectable: for example the K_n √3 penalty, or a C4 doubling.

## Not accepted or asserted

- No novelty claim from search absence.
- No impossibility claim.
- No hardware prices.
- The operation-count margins above are conditional on the Poisson bridge and are not bit-cost or clock-time gains.

The C4-light alternative and the adjacent-edge duplicate count are my own unreviewed derivations. They should go to the math critic before root integrates them.

---
*Factory usage — local bridge. This turn: 3,398,603 tokens · ≈1,074,266 Factory credits. Saved session total: 3,398,603 tokens · ≈1,074,266 Factory credits (including recorded subagents). Credits are a local estimate, not a dollar charge.*
