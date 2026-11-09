# Root verification failure

Fresh strict Lean builds and the inherited audit verifier succeeded. The first separate root verification script failed while comparing printed axiom names directly to propext, Classical.choice and Quot.sound. The actual audit prints Classical.choice.{u} and Quot.sound.{u}; the script omitted universe-annotation handling. It failed closed with AssertionError at its axiom-set assertion. The inline command and traceback are retained in this conversation's tool trace; no source or Lean log was changed.

The corrected check accepts only the exact observed spellings of the three permitted axioms (including their printed universe forms) and still requires one axiom report for every one of the 71 actual-origin declarations. It rechecks source hashes, original/copy bindings and package/compiler pins separately. This parser correction supplies no mathematical proof and changes no Lean source.
