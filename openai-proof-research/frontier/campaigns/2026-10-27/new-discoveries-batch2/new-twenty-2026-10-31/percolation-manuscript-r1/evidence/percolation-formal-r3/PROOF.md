This round adds a general sound RUP rule and a concrete certificate prefix, not
an unconditional counterexample. The inherited semantic bridge is unchanged.

A literal records a forbidden value. The RUP checker starts with the proposed
clause as the list of falsified literals. For each hinted clause it removes
literals already in that list. An empty residual is a contradiction. A singleton
residual forces its literal to hold; its complement is added to the falsified
list. Any other residual causes failure. An empty hint list also causes failure.

remaining_sound proves that a satisfied hint still has a satisfied literal in
its residual, since every removed literal is false. rup_sound_aux inducts on
the hint list: empty residual contradicts satisfaction; singleton residual
justifies the new false literal. rup_sound applies this lemma under the
assumption that every literal of the proposed clause is false. These are
ordinary Lean proofs with no solver or compiler computation trusted.

Each inp_i theorem supplies a concrete clause from inputCNF5. Gate-family
membership is established structurally, then the small local truth table is
checked by kernel reduction. Direct clauses use separately proved family
inclusions. holds_decode transports each conclusion to natural variables.
Each der_i applies rup_sound to its concrete clause and only its named hint
clauses. Its finite check is proved with decide. The evolving certificate
is never searched or reduced by the kernel.

The prefix frontier is an explicit list of the first 2000 retained additions.
The remaining assumption is ReplayFrontierUnsat5, the nonexistence of a valuation
satisfying inputCNF5 and this entire frontier. This is an ordinary explicit Prop,
not a postulated theorem. It remains unproved. The raw suffix has not been
represented as a Lean list or replayed, and the frontier hypothesis must not
be described as a completed formal suffix checker. A subsequent round can
continue mechanically from the exported cl_i, inp_i and der_i declarations.

NoMinimalTwoRound5 and the unconditional endpoint remain unproved. Root alone
decides acceptance; no campaign credit is claimed here.

The metadata audit rejected the first equation-compiler spelling of rup because
Lean generated rup._unsafe_rec. The final spelling is a noncomputable definition
using the explicit List.rec recursor. Noncomputable suppresses unsupported runtime
code generation; the finite checks still reduce in the kernel through decide.
The rejected audit and pilot logs are retained under logs/*before-recursor*.
Only measurements for the final recursor spelling are the current pilot results.
