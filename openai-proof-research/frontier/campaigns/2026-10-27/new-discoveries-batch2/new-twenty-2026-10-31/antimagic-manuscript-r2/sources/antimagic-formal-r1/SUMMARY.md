# Partial formalization handoff: MathDB 354228

Status: NOT ACCEPTED. No credit claimed. Root decides. This round does not prove the conjecture.

Completed, without proof placeholders:

- Literal finite-simple-graph labellings as edge equivalences into `Fin |E|`, weights with explicit `+ 1`, local properness, the spectrum of attainable colour counts, the infimum definition of `chiLA`, and a theorem turning an `IsLeast` result into the infimum equality.
- A real finite decidable row-index graph on `(h, i)`, with root and unique depth-zero vertex. No data-carrying proof placeholders.
- The reviewer's total piecewise parity formula, including the binary row-two transposition and both depth-two families. Formula correctness for general parameters is not proved.
- Full graph-isomorphism invariance of weights under transported labellings, properness, colour count, spectrum, chiLA, and degree-one leaf count.
- A finite counting lemma that extracts the leaf lower bound once distinct bounded leaf colours and a larger colour are supplied.
- Kernel row-formula checks for t = 2, 4 and n = 1, 2, 3; three negative controls; an independent lane-local Python incidence checker passing 42 cases. The regression checks are NOT yet linked to the literal graph definition.
- Clearly conditional endpoints in AntimagicFinal.lean, with only propext, Classical.choice and Quot.sound as transitive axioms.

Remaining exact Props: `ModelStructure`, `ModelBridge`, `ModelLeaves`, `LowerBound`, `Construction`. Their definitions are in AntimagicModel.lean and AntimagicFinal.lean. None is an axiom, proof, or instance. `even_case` assumes the last two. `mathdb_354228` assumes the last two and ModelBridge and ModelLeaves. ModelStructure is an additional fidelity target, not a hidden premise of either conditional endpoint.

The declaration audit covers all 106 declarations from the six mathematical modules, including generated declarations, and their expanded dependency closure: 5,366 declarations. Local flags are all zero. Upstream metadata separately contains 80 partial/_unsafe_rec declarations, 5 implemented_by attributes and 51 extern attributes; these are pinned upstream declarations, not newly introduced proof devices. The only axioms in the expanded set are the allowed three. See audit.tsv and results.json. This is not a blanket claim that upstream execution metadata is absent.

Next round: prove the lower-endpoint edge equivalence and incidence weight formula first. Establish children and parent equivalences, acyclicity/connectedness, leaf count and ModelStructure. Use the counting lemma for LowerBound. Split Construction into n = 1, n = 2 binary, n = 2 even t >= 4, and the parity-shell case n >= 3, with a separate binary patch. Finally prove ModelBridge by selecting an ordering of each finite child set and induction on depth. Replace conditional endpoints only after all five Props have proofs. Upgrade regressions to the literal edge-equivalence definitions at that point.
