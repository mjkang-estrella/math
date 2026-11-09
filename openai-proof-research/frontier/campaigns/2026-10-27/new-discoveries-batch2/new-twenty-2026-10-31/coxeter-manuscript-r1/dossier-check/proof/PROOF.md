# MathDB330264: formal normal form and endpoint

Source statement: Ciobanu–Kolpakov, arXiv:1504.02774v3, Conjecture 1.3. MathDB330264 asks whether trees with equal adjacency, complement and line-graph characteristic polynomials have equal geodesic growth. Source §2 uses a finite generating set and counts individual shortest words. This lane supplies a counterexample to the universal implication; acceptance, novelty and significance are independent root review gates.

## Genuine normal form

`Movable G a w` means an occurrence of a has only letters adjacent to a before it. `movable_iff` proves its decomposition characterization. `Clean` excludes a movable repeated letter in every suffix; `clean_iff_no_pair` proves exactly the requested forbidden-pair characterization, over arbitrary alphabets and words.

`pluck` deletes a movable first occurrence. Its product is left multiplication by the corresponding canonical generator in the actual CoxeterMatrix.Group. `toggle` deletes when possible and otherwise prepends. The proofs establish preservation of Clean, length change by one, respect for all commuting swaps, involutivity modulo swaps, and commutation of adjacent toggles modulo swaps. None is assumed.

`Trace` is the quotient of Clean lists by commuting swaps alone. Swap equivalence preserves list length, so trace length is well-defined. The toggles induce involutive permutations of Trace. Their Coxeter relations are verified in `action_liftable`, allowing Mathlib's universal property to construct `groupAction` from the actual PresentedGroup. Acting by a word increases trace length by at most its word length. Acting by a Clean word on the empty trace returns the trace of that word. Every representative of the same group element therefore has length at least the Clean word. This proves `clean_implies_reduced`; the r2 shortening direction gives `reduced_iff_clean`.

This is a group lower bound, not a proxy definition of reducedness. The actual group and CoxeterSystem.IsReduced are the r2 definitions, copied without modification.

## Recognition and individual-word counting

`frontState` is proved to equal Movable, and its members form a clique without any Clean hypothesis. `suffixState` applies it to reversal, with the exact source update rule for adjoining one letter. A Machine must prove its transition specification; this is not a recognition hypothesis. `accept_context` proves the state invariant and recognition from that specification and normal form. `accepts_iff_reduced` accounts for reading direction by actual Coxeter reducedness under reversal.

`Machine.Words k s` is a subtype of functions Fin k → V. Its elements distinguish every individual input word. `splitWords` splits off the first letter by a genuine equivalence. `wordCount_succ` is its finite-cardinality sum recurrence, proved using that equivalence. `geodesicGrowth_eq` transfers the cardinality to actual GeodesicWords.

The concrete machines have 38 states and 19 letters. All state meanings and all 722 transitions per machine satisfy the specification by kernel finite decision. A backward recurrence counts possible continuations from each state, avoiding any need to reinterpret the predecessor's forward count vector. Every stage from 0 through 18 has a kernel arithmetic certificate, and the all-length cardinality theorem transfers it to the group. The results agree with the predecessor total discrepancy:

G: 37769749324097905710910; H: 37769749324097905710906.

The new recurrence is independently linked to actual word cardinalities. It does not assume that the old recurrence recognized the group language.

## Spectral reuse and endpoint

`SpectralDefinitions.lean` and `GroupSemantics.lean` are byte-for-byte r2 copies. `SpectralWitness.lean` copies the actual-spectral/tree/line-graph proof block of r2 PartialEndpoint, factoring its initial definitions into the copied SpectralDefinitions import. Matrix computations and tree searches were not redeveloped. `generate_machine.py` reads the frozen predecessor's edge lists and produces the concrete tables and new recurrence certificates. Its output, not the Python generator, is checked by Lean.

`MathDB330264.counterexample` combines actual treehood, actual three characteristic-polynomial equalities (including intrinsic Mathlib line graphs) and distinct actual geodesic-word counts. `conjecture_false` negates the universal finite-tree implication over arbitrary vertex cardinalities. A difference in one strict coefficient precludes equality of growth series, per source Definitions 2.3–2.4. Every finite tree has a finite vertex enumeration; the concrete counterexample already has vertex type Fin 19.

## Limits

No mathematical Lean bridge remains if the final extracted replay passes. This does not establish new-to-literature priority or significant discovery credit. The frozen source comparison remains bounded and explicitly requires independent novelty review. No publication, shared count edit, author contact, denied-route retry or source re-search occurred.
