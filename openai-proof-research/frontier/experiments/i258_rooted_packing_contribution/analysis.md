# I258 contribution analysis

2026-10-12. Final contribution judgment: **TECHNICAL**. This completes the initial notes written during primary reading. The exact candidate and hash are unchanged. This file analyzes contribution, not proof validity; the complete report is `frontier/reviews/i258-rooted-packing-contribution.md`.

## New proof burden as a generic functional lift

For a compressed and symmetrized Q, the candidate introduces W_Q=max_M sum_{U∈M}w_Q(U;G), over disjoint d-block collections. The source R-packing gives a lower bound of half its cardinality. For each fixed M, its weighted sum is the conditional expected number of successes after extension. That count cannot exceed the optimum in the extended host. Max E≤E max then compares E W_Q to μ_Q=E ν_Q at density 1−(1−r)². This is a general feasible-optimization inequality. Candidate-block dependence does not require a new structural theorem for that step.

The concentration replacement is similarly natural: an exposed nonroot's coordinate block affects only candidate blocks containing it, and a packing can contain at most one. This gives the usual vertex-Lipschitz bound for both weighted and ordinary packing rank. Compression and test counting then repeat the source method with b rather than s local required coordinates.

The amplification step is the principal additional lemma. A maximum packing selected equivariantly from an exchangeable random host becomes uniform conditional on its size, after averaging the host. Independent layers produce independent uniform trimmed packings. Before the cap, the occupied fraction is small, so most blocks of the next matching avoid it; permutation exposure bounds the loss. This is not a claim that matchings compatible with a fixed graph are uniformly distributed over all matchings. The correct conditioning is worth stating carefully, but its correction alone is not a substantial discovery.

These steps make a genuinely stronger formal theorem than scalar transfer. They are generic for fixed-size disjoint configurations with symmetry, large means and large unused-vertex reserves. No new sparse threshold mechanism, structural classification or global gluing principle is paid by this candidate.

Source dependence is methodological: the finite Bernoulli compression operation is re-proved in the candidate. Its rank argument does not use the deeper graph-decomposition, discrete-convexity or constant-factor rounding conclusions. Their stipulated truth is preserved, but those conclusions are not transformed into a new substantial application here.

## What the uniform quantifiers cost

D and E use deterministic inequalities against the same μ_Q. Once every (Y,Q) test holds, Q can be selected after G,H,R. This is why Cartesian-product and adaptive-family assertions follow without a coupling. The same architecture is already visible in the full 175 transfer proof. The new packing functional must carry the contribution; the quantifiers cannot be credited in isolation.

Root reuse is a real difference from FLN and the Nenadov–Škorić Connecting Lemma. It is not a difference from the arbitrary-overlap compression principle of 175. Measuring actual source rank avoids promising impossible repeated demands; it is a useful formulation of the source-relative method.

## Analytic parameter consequences

With b=ds+binom(d,2), log(1/r)≤log n/(100b). If s=c log n for fixed c>0, then log(1/r)≤1/(100dc)+o(1). If s is fixed, r≥n^(-1/(100b)). These are symbolic deductions, not experiments or scans.

The submitted reference-mean bound μ_Q≥c_d n^.99 already follows from predetermined disjoint d-blocks. Relative concentration has exponent n^.98, whereas the test entropy is only O_d(n^(2/3)log n+n^.01(log n)²). The theorem does not reach supply scales where such coarse concentration is inadequate. Fixed d makes all extra costs constant. Sublinear roots preserve a nearly full nonroot reservoir.

The cap N/(16d²) is asymptotically 1/(16d) of the full d-matching size. The application n/(1000d³) is smaller still. Linear size has value, but in combination with strong density and unrestricted nonroot images this is the slack regime where symmetry plus deletion is standard. Neither nonedge constraints nor candidate lists are supported by the submitted method.

## Verdict calibration and repairs

SUBSTANTIAL would require a nonroutine new mechanism or a demonstrated consequence beyond the existing source and block-embedding architecture. KNOWN would require an actual prior statement or a precise direct implication; the read sources provide neither for this exact theorem. UNRESOLVED would be appropriate if missing primary access prevented the present judgment; the requested primary arguments were accessible and read at the disclosed scope. TECHNICAL is the supported middle disposition: useful formal extension, insufficient contribution under this gate, with exact worldwide priority still unresolved.

A substantive repair could require low-supply/rooted-density control, capacity-governed nonroot restrictions, or an explicit shared-interface application beyond current methods. Such repairs are unproved and require author work. Constants, a different fixed d or the same AH corollary cannot supply them. No candidate edit or author response was made.
