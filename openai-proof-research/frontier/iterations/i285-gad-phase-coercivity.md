# I285 — bounded parity rank gives global phase/tree coercivity

**Restricted TP/PH/U proved; unrestricted TP/PH/U unresolved. No counterexample, acceptance claim, or finding-count change.** Twelve findings remain accepted toward twenty. All pinned OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true.

The [complete proof](../experiments/i285_gad_phase_coercivity/analysis.md) proves the stronger I280 tree inequality on a new restricted class. Fix interior γ,ν and an integer k. For every n, every computational probability law q with arbitrary correlations and zeros, and every phase of the form

    f(x)=α+θ0·x+F(Bx) mod 2π on supp(q), rank_GF(2)(B)≤k,

with arbitrary F, one has

    G_q(f)≤C_k(γ,ν)[c_A KL(q||r_n)+max_π Q_π(ψ)]
           ≤C_k(γ,ν)D_n(ψ).

Here c_A, r_n, D_n and Q_π are exactly I280's definitions. The constants are explicit and independent of n, support sizes/intersections, q and phase angles. There is no closeness hypothesis and the entropy excess is absolute, in nats. I280's paid distance conversion gives U on this class with K_k=8C_k+8/c_A.

The main new step selects a parity basis and at most one witness for each reused basis coordinate. This leaves a core of at most 2k sites. A product-phase approximation on its zero-syndrome restriction forces reused basis phases close to signs; it then extends pointwise to a single additive phase on the entire original cube. This pointwise conclusion applies to every q. Fixed-order core trees and a bounded-test/Hellinger change of measure pay the core error with the original noisy tree plus KL. Generic inversion is used only on the at-most-2k-site core, with its size dependence explicit.

This covers arbitrary functions of any fixed number of overlapping, arbitrarily long parity variables. In particular it extends one parity-phase gate to arbitrary correlated amplitudes and includes interactions among multiple parities. I280's flat-amplitude one-parity theorem, amplitude theorem and site-separating theorem are spent predecessors, not new findings. I279's false summed-original-marginal bridge is not used.

The constants grow with k. Taking k=n to represent an arbitrary phase does not finish the original target. The exact remaining gap is a uniform-in-phase-complexity mechanism replacing the finite-core inverse and rare-syndrome costs. No lower bound on the optimal constants and no counterexample to TP alone or to PH/U are established. Worldwide novelty and substantiality are not certified.

[Read boundaries and failed routes](../experiments/i285_gad_phase_coercivity/reading-and-failures.md), [authentication](../experiments/i285_gad_phase_coercivity/input-authentication.json), and [literature scope](../sources/i285_gad_phase_coercivity/literature.md) accompany the proof. The complete 272-line I280 analysis matches the required SHA256. Only assigned I285 paths were written; there were no subagents, live sibling reads, shared edits, staging, commits, publication, numerical scans or giant history replay. Detached hashes are returned without an independent acceptance claim.
