# Precise eventual certificate plan; no formal proof claimed

The intended literal Lean endpoint is

    theorem source_conjecture65_refuted :
      (∑' n : ℕ+, ((2 + Real.sin (n : ℝ))/3)^(n : ℕ)/(n : ℝ))
        < ei (Real.log 3)

with `ei t` defined by Euler's constant plus `Real.log t` plus the literal positive power/factorial series at t>0, matching the source. A stronger rational separator endpoint should assert S<21635/10000 and 21635/10000<ei(log3). Use of `tsum` must include a summability proof; positive-prefix upper bounds and the dyadic tail supply it independently of importing Boppana's convergence theorem.

1. Prove Machin identity and the rational directed-arithmetic reflection lemmas, the sine/cosine polynomial inequalities, exp upper polynomial, and gamma harmonic/log squeeze.
2. Reflect prefix-replay and finite sparse residue witnesses with kernel `decide`/`norm_num` and proved modular-inverse bijection/omitted-point lemmas. Do not use `native_decide`, unsafe evaluation or an axiom asserting the Python output.
3. Prove the separated-circle counting and Gaussian-layer-cake integral bound, then the dyadic packing bound. A simpler rational upper for the Gaussian integral is allowed only after a proved integral estimate.
4. Reflect the 1570 rational spacing/tail witnesses. Each requires only a certified rational enclosure of alpha, coprimality and exact arithmetic, not CF correctness or optimality. Avoid reflecting the minimum search: reflect the chosen positive candidate per row.
5. Prove the all-denominator explicit pi approximation inequality, or cite a pre-existing kernel theorem with precisely its global quantifiers and constant. From it derive ||h/(2pi)||>1/(8h^19), the floor-root choice, and the remote geometric sum. **This is the largest unresolved formal burden.** No verified Lean theorem for the global Chudnovsky inequality has been located. Boppana's paper is an ordinary analytic citation, not a permitted Lean axiom. Reproving this deep irrationality estimate may dwarf all finite arithmetic work. A conditional Lean theorem assuming it is not a completed certificate and is not eligible for acceptance.
6. Assemble exact source equality negation, inspect all declaration origins and standard-three axioms, independent adversarial review, paper and extracted replay only after eligibility is adjudicated.

No Lean work was started: full-source ordinary refutation does not establish campaign novelty, and the global pi theorem must not be hidden as a residual bridge.
