# Statement correspondence

The inherited graph definitions, FullTree predicate and labelling formula remain unchanged. Source Definitions 1.1–1.4 and published Conjecture 6.1 are interpreted exactly as in round 1. The current scope remains all t >= 2 even, n >= 1, and all finite FullTree structures.

| Source obligation | New certificate | Status |
| --- | --- | --- |
| Concrete finite rooted complete full tree | modelStructure | Proved, exact inherited root/depth/child |
| Unordered edge / lower endpoint correspondence | incomingEquiv | Proved for positive t |
| Literal incidence weights with labels shifted by one | weight_children, weight_row | Proved |
| Degree-one leaves number t^n | modelLeaves | Proved for t >= 2, n >= 1 |
| At least t^n + 1 colours | lowerBound | Proved for all such t and n |
| Explicit star construction | star_construction | Proved for every t >= 2 |
| Source Figure 5 | binary_construction | Proved for t = 2, n = 2 |
| Remaining explicit constructions | Round2.RemainingConstruction | Open Prop, no proof or instance |
| Every finite source tree is isomorphic to model | ModelBridge | Open inherited Prop |
| Even-case least spectrum | Round2.even_case | Conditional on RemainingConstruction |
| Arbitrary full-tree least spectrum and chiLA | Round2.mathdb_354228 | Conditional on RemainingConstruction and ModelBridge |
| Depth-one least spectrum | Round2.depth_one | Unconditional |

The isomorphism invariance proof is inherited. Evenness is unnecessary in the structural, lower-bound and star results. It remains required in the open construction and final even-case statements. No inherited endpoint is shadowed or renamed; Round2 is a distinct namespace. No acceptance or novelty conclusion is drawn from formal progress.
