# PARTIAL: actual-law early-block and compression bridges certified

30 October 2026. Counts 9 additional / 39 total / next 40 unchanged. Root alone
accepts/counts. Full finite abundance theorem NOT closed. Full source, novelty,
asymptotic and mixing acceptance remain HOLD. No discovery credit requested.

The five inherited modules Literal, Terminal, Law, Cells, Product are preserved
byte-identically to r4, including the already repaired noncomputable words.
Five new proof modules are Prefix, Marks, Boards, Injection, Abundance.

Certified endpoints (all in namespace LiteralGame):

* actual_prefix_mass: for every executable u from initial N to b, the actual
  completeDomain-filtered prefix cylinder has mass reciprocalProduct(initial N,u).
  cylinder_image and continuation_product_normalized prove this from actual
  normalized finite continuations; there is no postulated Markov law.
* actual_prefix_transition and actual_prefix_continuation: divide those actual
  cylinder masses by the strictly positive parent mass. One legal move has
  conditional mass 1/card(legalTypes b); an executable continuation has its
  actual reciprocal product. N=0 and the empty prefix are included.
* legalTypes_le_two_n and reachable_types_le: for n>=1 and N<F_(n+1),
  every reachable board has at most 2n legal TYPES. The lower F_n<=N assumption
  is unnecessary for this bound, so the requested Fibonacci interval is covered.
  input_ones_le, step_ones, executes_ones prove F1 depletion <=2 per move.
* early_block_six and actual_early_success_lower: if u.length=3j and j<N/6,
  its board has >=6 ones, is live, and admits C1,C1,C2 with actual conditional
  cylinder probability >= blockLower n = ((2n)^(-1))^3 = (2n)^(-3).
  complete_length_blocks proves every complete word has >=3*(N/6) moves.
* successSlots J w filters j<J for exact literal triples at raw positions
  3j,3j+1,3j+2. successIndex w j is length(compress(take(3j+2,w))).
  successIndex_marked proves membership in the globally compressed markedSlots.
  successIndex_strict proves strict order on distinct successful blocks;
  success_count_le_marks is the finite counting injection, including a preceding
  S2 that consumes the first C1. No mark applicability or distinctness premise.
* actual_success_count_le_marks applies the injection to EVERY actual complete
  word with J=N/6. actual_bad_marks_le_bad_success bounds the actual P_N mass of
  too few compressed marks by the actual mass of too few early successes.
  bad_threshold_zero and zero_input_bad_mass state threshold/input zero cases.

Residual, precisely: prove in Lean the finite completeDomain identity/inequality

  sum_w P N w * (1/2)^card(successSlots (N/6) w)
    <= (1 - blockLower n/2)^(N/6),

by summing the conditional lower bound through the partition by length-3j
prefixes; then apply the finite dyadic Markov inequality to obtain, for every
natural t, badMarksMass N t <= 2^t*(1-blockLower n/2)^(N/6).
No theorem here asserts this moment or final tail bound, and no independent
raw Bernoulli trials, concentration within cells, asymptotics or mixing is used.
PROOF.md records the ordinary finite algebraic argument and its provenance;
that prose is not a replacement for the missing formal induction.

Strict actual-origin inventory includes every private/generated declaration in
all ten mathematical modules and traverses both types and bodies transitively.
Every partial/unsafe origin or dependency and every non-Std3 axiom hard-fails.
Audit commands use actual Lean Names. Fresh extracted source-only serial replay
and the separate final guarded verification are recorded in their receipts.
All failed attempts remain with exact source, log and resource records.
