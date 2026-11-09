# MathDB 342364 — round 2 partial handback

Status: PARTIAL, not accepted. Root decides. All six residual Props remain open; the requested unconditional ¬Conj61 and Conj61Some are not proved.

New sorry-free checked work:

- Faithful product functional equation C(x) = w(x) C(x²), and its m-th power.
- Even/odd series decomposition and the even-section convolution rule; F2 for arbitrary integer series.
- General-j coefficient transfer and difference readout (equation (1)), with full-series transfer numerators.
- Coefficientwise parity C^m ≡ 1 modulo 2 (F4).
- Universal coefficient polynomials through degree four; in particular 3(c_m(4) − c_m(1)) = 2m²(m+1)(m+5).

The polynomial y-basis bridge and Lemma R remain unproved. The checked full-series operator does not yet establish an integral reduced polynomial operator. Chebyshev/Kummer bounds, weight Lemma W, exact valuation readout, reduced low coefficients, and general nonzero differences also remain. See REMAINING.md for all six exact Lean Props and NEXT-ROUND.md for the continuation.

All four round-1 modules are byte-identical to the SHA-bound archive and the original src copies; before/after hashes are recorded. Four new mathematical modules end in UlasFinal2; UlasAudit2 is separate instrumentation. No child agents, git operations, shared edits, network, uploads, messages or browser tabs were used.

Fresh extracted strict serial rebuild and leanchecker passed for all nine modules. The endpoint import closure contains 349,527 kernel declarations across 3,650 modules, exactly matching the exported audited set. LOCAL: 214 declarations; zero unsafe, partial, axiom, _unsafe_rec, implemented_by or extern flags; all transitive axiom sets lie in {propext, Classical.choice, Quot.sound}. Upstream metadata is separately reported in results.json and fresh-replay/logs/audit-summary.json. Compiler IR extra names are inventoried separately from kernel declarations.

The endpoint remains conditional on exactly Ulas.Remaining, definitionally aliased as Ulas.Round2.Remaining. Passing the audit does not supply that Prop or settle the conjecture. Replay logs include failed development attempts, all retained with unique names.

Independent Python regression passed for m = 0..24, series length 256 and 2,800 general-j readout pairs. Both new negative controls failed with the expected type mismatch: the conditional endpoint cannot be used without Remaining, and the functional equation cannot omit w. No background process remains.
