# Literal source functions and elementary interfaces

Root component, 29 October 2026. Import `MeanSourceDefs`, namespace
`LogArctangentSource`. This defines the diagonal-extended logarithm–arctangent
mean, the real power mean including p=0, the literal resultant, and the two-branch
published Conjecture 37 proposition. **SourceClaim is not proved here.**

Sixteen helper theorems prove symmetry, positivity, diagonal values,
positive homogeneity, strict coordinate monotonicity of the power mean for
every nonzero exponent, strict internality of that power mean, and the
corresponding symmetry/positivity/homogeneity of the resultant. The negative
exponent branch is proved by reversing order twice, not assuming p>0.

The log difference used in the definition equals the source's log ratio for
positive inputs. This component does not yet claim a formal source-log-ratio
rewrite, the Stolarsky identity, centered gap monotonicity, the strict
between-means sandwich, or any full conjecture endpoint.

Fresh isolated source-only replay passed with warningAsError and autoImplicit
false. Root read all 20 type and axiom reports (four definitions, sixteen
theorems): only propext, Classical.choice, Quot.sound. No forbidden proof
constructs. Actual Lean binary SHA and mathlib revision verified. Peak sampled
process-group RSS below 2.64 GB, ceiling 3 GiB. The receipt binds all source
bytes and fresh logs; upstream pinned oleans are used, no prebuilt local
module was copied to the replay directory.

Development encountered deprecated if_pos/if_neg names and two mistaken
library lemma names/orientations; these were corrected, not suppressed.
Initial invocation before the monitor was installed was not RSS-audited;
all final compile and fresh replay claims refer to compile.py receipts.
Formal helpers are uncredited. Candidate credit 0; accepted total 33/60.
