# AGM063 scoped Lean support

Myeongjin Kang, no affiliation. Original prose CC BY 4.0; original code MIT. This is an implementation packet for a later independent artifact audit, not a proof-review verdict or acceptance.

The clean pinned build proves **29 supporting theorems across 35 public declarations**. All six requested interfaces are covered:

1. Finite degree budgets use actual `Finset.card` / `Fintype.card`, derive `d≤i+1<2i` for `i≥2`, and exclude two positive contributions or a multiple of multiplicity at least two below the strict cutoff.
2. Integer arithmetic proves the supported composition dimension `rn+s−(r−1)n=n+s` and forces `b≤1` from the two support-dimension bounds.
3. Saturation gives the exact two-endpoint inclusion into the quotient fiber relation or the complement square. The quotient map is defined only on the subtype `U`; it is not extended across its boundary.
4. Preservation by generating relations propagates by induction through the actual reflexive-transitive closure. A nonempty proper invariant subset contradicts universal chain connection, and conversely some generator must escape it.
5. Vanishing on a spanning set forces a real linear functional to be zero. Finite spanning representatives and a supplied positive intersection witness therefore give a contradiction.
6. Integer Picard induction and pseudoindex-increase arithmetic include the possible rank-two increase and the actual-to-parameterized exception.

**The full AGM063 classification is not formalized.** No Fano manifold, virtual cycle, quotient-existence theorem, geometric dimension bound, numerical intersection space, Mori contraction or classification axiom is introduced. The support takes the relevant numerical, saturation, spanning and geometric-witness contracts as explicit hypotheses. It proves their finite/relational/algebraic consequences. `coverage.json` maps every declaration and all omissions; exact declaration types and `#print axioms` outputs are in `validation/sealed-build/types-axioms.stdout`.

The human theorem remains the full five-type classification at actual Picard number and pseudoindex, without dimension/rank/contraction/covering restrictions. Its equality case uses stipulated source S1; its bridge also essentially uses the stronger internal independent-correspondence proposition S2, both at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Neither is a new Lean axiom here. Kollár/Fujita supply the quotient and construction; Fujita supplies the final contraction/induction/bundle template; Dedieu–Höring supplies rank one. This support does not claim those paid inputs as new. The Watanabe reading task remains with manuscript preparation; this packet asserts no literature novelty or worldwide priority.

## Validation and reproduction

Use the manifest SHA-256 supplied separately by the parent/release receipt:

```sh
python3 -B verify.py --anchor EXTERNALLY_SUPPLIED_SHA256
```

This read-only verifier requires an external anchor and checks exact files/directories, hashes and source/build/coverage consistency. It rejects changed, missing, extra and symlinked payloads. It does not compile Lean or certify geometry. The isolated pre-seal controls in `validation/integrity-controls.json` include positive and wrong-anchor checks. A digest obtained only from the same untrusted package is not an independent trust anchor.

For a fresh build, first copy the package to a working location, since logs change its sealed inventory:

```sh
python3 -B rebuild.py --lean /path/to/lean-4.34.1/bin/lean \
  --cache /path/to/pinned/.lake/packages --output .replays/independent
```

The defaults use Lean under `dlp-research/.tools/lean-4.34.1-linux/bin/lean` and the sibling `formal/.lake/packages`. The runner checks Lean 4.34.1 commit `5045d0056413266e57c625dcd7c365b10e377c52`, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, all nine locked dependency revisions and tracked cleanliness. Cached dependencies are read-only. Only the four own Lean source/audit files are copied into a fresh compilation directory; own objects are rebuilt and discarded. No prior AGM063 objects or network access are used.

The final build has no warnings and only the standard transitive axioms `propext`, `Classical.choice`, and `Quot.sound`. Eleven proved semantic-control theorems establish actual counterexample premises and failures. Seven deliberately false Lean goals are rejected: missing saturation; weakening the complement-square bound by one dimension; allowing pseudoindex one; replacing the strict degree cutoff by equality; missing span; missing generator preservation; and reversing the base-pseudoindex inequality. The associated true premises are explicit in `Controls.lean`. Four real subprocess-wrapper tests also pass, including rejection of an exit-zero child printing `SOME FAIL`. These are concrete fault controls, not an independent mathematical audit or exhaustive test suite.

`reading-and-provenance.md` records actual reading and helper reuse. The six supplied input anchors match, and read payloads match their anchored manifests. Contribution-review control transcripts are expressly exempt from its manifest and are **not** claimed authenticated. The author's historical 10/20 checkpoint is retained unchanged; the assignment's current count is 11/20, with no change made by this implementation. All third-party source bodies remain private.
