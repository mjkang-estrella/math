# Frozen R198 statement: sign recovery for sphere phase-isometries

Fix the stipulated Source322 theorem and all its operative proofs at commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

For EVERY pair of nonzero real Banach spaces X and Y, of arbitrary finite or infinite dimension, and EVERY surjective map f:S_X -> S_Y satisfying, for EVERY x,y in S_X,

    { ||f(x)-f(y)||_Y, ||f(x)+f(y)||_Y }
       = { ||x-y||_X, ||x+y||_X },                       (P)

there exist a surjective real-linear isometry U:X -> Y and an even sign function sigma:S_X -> {-1,1} such that

    f(x)=sigma(x) U(x) for every x in S_X,
    sigma(-x)=sigma(x) for every x in S_X.

The braces in (P) are unordered sets of the two displayed real numbers (equality of the two entries is permitted). No continuity or measurability is assumed of f or sigma. There are no separability, reflexivity, smoothness, strict convexity, local compactness, or dimension restrictions. Distances and norms are the given norm metrics. Completeness is required in the headline invocation of Source322.

The pair (U,sigma) is unique up to simultaneous replacement by (-U,-sigma). Conversely, every such pair gives a surjective map satisfying (P).

The claimed residual is a stronger pre-extension statement: any such f on spheres of nonzero real normed spaces admits exactly two continuous odd bijections h:S_X -> S_Y with h(x) in {f(x),-f(x)}, and each is a metric isometry. This auxiliary statement does not require completeness. Its proof, including dimensions 1 and 2 and arbitrary infinite dimension, is part of the frozen scope. The Banach-space conclusion then uses Source322 exactly once.

No quantitative or approximate version, no nonsurjective version, no arbitrary complex phase, and no complex-linear conclusion is asserted. Complex Banach spaces are covered only after restricting scalars to R, with signs +/-1 and real-linear U. No formalization, manuscript/release, grade, acceptance, campaign increment, or worldwide novelty is asserted.
