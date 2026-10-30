# MathDB 376980: minimum means counterexample to the literal classification

**Result:** Binary minimum `m(a,b)=min(a,b)` and ternary minimum `M(a,b,c)=min(a,min(b,c))` are continuous symmetric means on the positive orthants. They satisfy both actual source invariance identities. They admit no genuine inverse quasi-arithmetic pair representation, even without imposing monotonicity on the generator. This refutes the source's literal classification of all continuous means.

**Essential qualification:** The witness is not strict. This outcome does not decide an intended or revised classification restricted to strict, strictly isotone, or analytic means. The original Section 1 definition of a mean requires continuity and internality; strictness is explicitly a separate property. The final conjecture does not impose it. Its preceding derivative-based motivation does not alter the stated class in this record.

## Exact source

Alan Horwitz, *Invariant Means*, arXiv:math/0007095v1. The original PDF's statement is **Conjecture 29**, Section 7.4, printed page 26. The arXiv HTML conversion renumbers it as **Conjecture 26**. Both versions' actual wording was read, and the original PDF pages 1, 2 and 26 were rendered and visually inspected. The original PDF defines a mean at Section 1 / printed pp.1–2. Its abstract and introduction give the two identities:

`M(m(a,c),m(a,b),m(b,c)) = M(a,b,c)` for positive `a,b,c`;

`M(a,b,m(a,b)) = m(a,b)` for positive `a,b`.

The conjectured simultaneous inverse formulas use arithmetic denominators 2 and 3 respectively. All argument order and normalization choices match the formal source. The source's strict-isotone assumption in Section 3 is expressly local to that section. Section 7.4's classification itself says only “pairs of means.”

The exact retrieved MathDB post is in `sources/376980.json` (post UUID `216d4eb0-50a2-4fcb-9a13-67c3ac855a4b`). It has no posted solution. This absence supports no novelty or priority claim. The construction and minimum identities are elementary standard facts; the present output claims source-level verification, not a new-to-literature theorem.

## Complete mathematical proof

Both minimum functions are globally continuous and therefore continuous on the required positive domains. Their values equal the minimum of the arguments and hence lie between the minimum and maximum. Positivity of all inputs gives positive outputs. Permuting the arguments leaves a finite minimum unchanged, so they are symmetric under every permutation.

Type 1 reduces to

`min(min(a,c),min(a,b),min(b,c))=min(a,b,c)`,

because repetitions in a nested minimum do not matter. Type 2 reduces to

`min(a,b,min(a,b))=min(a,b)`.

These identities hold for all real inputs, so in particular on the source positive domains.

To exclude a genuine inverse representation rather than an arbitrary proposed generator, the formal predicate `InverseArithmeticPair` has these explicit requirements for functions `h, inv`:

- `inv(h(a))=a` for every `a>0`;
- each binary/ternary arithmetic average of generator values belongs to `h '' (0,∞)`, where an ordinary inverse is defined;
- the witness means equal `inv((h(a)+h(b))/2)` and `inv((h(a)+h(b)+h(c))/3)` respectively.

No monotonicity requirement is imposed, making this a larger class than the source conclusion. The inverse identity makes `h` injective on positive inputs. The average range requirements imply that `h(inv(u))=u` for each used average. Thus `inverse_pair_implies_generator` derives both necessary conjugacy equations with their correct denominators. In the binary equation at `(a,b)=(1,2)`, minimum is 1, so `h(1)=(h(1)+h(2))/2` and therefore `h(1)=h(2)`. Injectivity contradicts `1≠2`. This proves nonrepresentation for the pair without any missing inverse/generator bridge assumption.

## Formal coverage

`formal/InvariantMinimum.lean` is a self-contained module over pinned mathlib. Its principal declarations are:

- `IsMean2`, `IsMean3`: exact positive-domain continuity and internality conditions;
- `Symmetric2`, `Symmetric3`: symmetry under every finite-coordinate permutation;
- `Type1`, `Type2`: exact source identities;
- `m_isMean`, `M_isMean`, `m_symmetric`, `M_symmetric`, `type1`, `type2`: full witness membership and invariance;
- `witness_positive`: all substitutions remain positive;
- `inverse_pair_implies_generator`: derives the actual injective arithmetic-conjugacy conditions from the inverse formulas and inverse domain conditions;
- `no_arithmetic_generator`, `no_inverse_arithmetic_pair`: the `(1,2)` obstruction;
- `witness_not_strict`: makes the scope limitation explicit;
- `source_counterexample`: hypothesis-free bundled main result.

No positive-domain hypothesis, continuum symmetry claim, source-class bridge, or nonrepresentation bridge is supplied as an assumption to the main result.

## Validation and limits

Run the pinned verifier from the workspace root:

```bash
python openai-proof-research/frontier/campaigns/2026-10-25/twenty-proof-campaign/verify_outcome.py openai-proof-research/frontier/campaigns/2026-10-25/extension-discrete-second
```

The fresh audit passed with warnings treated as errors: 24 declarations, Lean 4.34.1, only `propext`, `Classical.choice`, and `Quot.sound`. See `build/audit.json` for the final Lean hash. No proof placeholders, additional postulates, or prohibited evaluation mechanism occur. The paper source is `main.tex`; authored PDF compilation/visual QA belongs to the parent.

The meaningful limitation is the source class: the result is a complete counterexample to its unrestricted continuous-mean wording and does not purport to settle any strengthened strict/smooth classification. No new mathematical priority is claimed. No external posting was made.


Production note: third-party full source snapshots remain in the separate local source audit extension-discrete-second/sources; the standalone package supplies provenance URLs and content hashes.
