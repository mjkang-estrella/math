# Source/formal component: strict PASS for items 1–3; item 4 partial

No campaign acceptance or novelty clearance. Counts unchanged: 9 additional / 39 total / next 40.

Six mathematical modules compile under Lean 4.34.1, serial -j1 -M2700,
warningAsError=true, autoImplicit=false, with the prescribed fixed dedicated guard.
The deterministic source-only archive is `source-only.zip`; `packet/` contains its inputs.
The fresh-extraction replay and declaration audit are retained in `fresh-replay/`.
See `verification-receipt.json` for the separate final integrity verification.

1. Source.lean defines d(n) as the ZMod2 cast of padicValNat 2 (n+1).
The frozen PadicValNat definition is the first component of Nat.maxPowDvdDiv;
for n+1>0 it is exactly the maximal exponent of 2 dividing n+1.
Casting to ZMod2 is literal parity. D=PowerSeries.mk d; D_constant and D_linear
prove the zero constant and unit linear coefficient. U uses substInvOfIsUnit,
not an automaton-defined surrogate. D_subst_U and U_subst_D prove both
compositions equal X. U_unique proves right inverse uniqueness.
Algebra.lean proves D's published quadratic equation coefficientwise from the
valuation recurrence, substitutes actual U, and derives both Proposition10 equations.
Recurrence.lean proves u_zero/u_one and all three scalar recurrences unconditionally.

2. Automaton.lean has eight finite states S,2,...,8, final states2,6 and the
published Table1 transitions, with initial state's zero transition replaced by S.
leading_zero proves padding invariance. auto_eq_u identifies numeric-state output
with actual inverse coefficients. table1_numeric proves for EVERY Bool list w,
output(run S w)=u(value w); value uses MSB positional evaluation.
No transition-correspondence axiom or hypothesis appears. A kernel-checked
13-pair adjacent-state invariant handles the predecessor in u_(4n+1).

3. b and a are literally Nat.nth of u=0 and u=1. zeros_infinite follows from
even zero positions. ones_infinite uses the actual recurrence at iterated4n+3.
Both enumerations are strictly increasing; b_zero=0. g is literal Nat subtraction
b(n+1)-b(n), and gap_one_or_two proves its alphabet. a_bounds handles all natural
subtractions; c_strictMono proves c(j)=a(j)-j-1 increases strictly.
around_one identifies b(cj)=aj-1 and b(cj+1)=aj+1 by complementary finite ranks.
gap_two_iff proves g(n)=2 iff n=c(j) for some j. enumeration_endpoint packages
these source-backed facts, without extra mathematical premises.

4. Suffix.lean supplies the all-state ordered-block list recurrence, bounds,
additive count recurrence, exact depth3 lists, and suffix_semantics/source linking
these lists to all accepted length-t MSB words and actual u. No assertion that
all-depth ordering/extrema/count-table induction or the Fibonacci threshold is
certified: those remain residual. firstThreshold/recordGap are definitions only.

Audit: 295 actual declarations from six modules; complete expanded types, origins,
safety and transitive axiom reports in audit-02.log and fresh-replay/Audit.log.
The inventory includes private/generated declarations. No unsafe declarations;
only propext, Classical.choice, Quot.sound. Four generated _unsafe_rec definitions
have safety=partial and unsafe=false, state, onesWitness,
suffixValues and valueFrom. The first, second and fourth are axiom-free;
suffixValues uses the three permitted axioms. They are compiler implementation declarations for
terminating definitions, not author-written partial escape routes. Audit command
infrastructure is outside the six mathematical origins.

Not a full all-base nonregularity theorem. The generic k-regular/module and
numeric recognizability infrastructure remains future work, and is not hidden
as a hypothesis in any claimed endpoint. No SourceClaim/PASS object was invented.
