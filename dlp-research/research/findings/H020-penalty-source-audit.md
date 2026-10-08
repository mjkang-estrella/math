# H020: literal AND-penalty equivalence fails

2026-10-08. Candidate-specific negative finding, not an ECDLP improvement.
Native Sol located the defect; root and native Astra independently confirmed
the printed expression visually. Root implemented a narrowly scoped Lean proof.
No numerical ECDLP experiment or hardware access was performed.

## Primary-source mapping

Lin et al., DOI10.23919/ICN.2026.0017, published September21,2026:
[full publisher PDF](https://www.sciopen.com/local/article_pdf/10.23919/ICN.2026.0017.pdf).
Printed p278 Eq.(22), p279 Table1 and Eq.(24) use the same Boolean polynomial

    P(a,b,c)=ab-ac-bc+c

for the claimed exact constraint c=ab. The variables are Boolean, not Ising
spins. The truth table itself includes the invalid assignments below as minima.
Root fetched the PDF and rendered its seventh/eighth pages to rule out OCR
ambiguity. Sol's wider source/cost review remains separate. This record evaluates
the literal published construction; it does not assume access to its actual code.

## Independent counterexample and scope

P(0,1,1)=0 but 1!=0*1. Symmetrically P(1,0,1)=0. Algebraically,

    P(a,b,c)=ab(1-c)+(1-a)(1-b)c.

Thus P is nonnegative on Boolean inputs; it is one only at 001 and110, and
zero at the other six inputs. The actual zero set permits either output when
the two inputs differ. In particular these invalid zeros are genuine GLOBAL
minima of the LOCAL penalty. Any positive rescaling, or squaring, preserves
them. Increasing a penalty weight cannot restore this local equivalence.

Other terms could exclude these assignments in a particular assembled objective.
No theorem here says every complete instance has a false ground state, that
reported experimental outputs are wrong, or that all correct QUBO encodings
fail. The implementation could differ from the printed formula. These are
unresolved limitations, not reasons to accept the stated local equivalence.
Replacing the penalty by a different correct construction would require new
coefficient and full-work accounting; no such speedup follows automatically.

## Lean implementation and independent review

`Research/AndPenaltyAudit.lean` uses Int-valued 0/1 embeddings of Bool, avoiding
truncated natural subtraction. `nonnegative` and `not_exact` use kernel-checked
finite decisions; `weighted_false_zero` proves the explicit false zero survives
every integer weight. Its positive-weight interpretation uses nonnegativity;
negative weights are not claimed to preserve minima. Research.lean imports the
module, and Audit.lean prints dependencies of all three claims. This is focused
verification of a proposed algorithm component, not new general cost machinery.

Independent Astra mathematical/source review COMPLETED: the two counterexamples,
nonnegativity identity, intended domain and limited scope were confirmed.
Independent Astra Lean statement/source review also COMPLETED: Int subtraction,
quantifiers, local scope, import and all dependency-audit entries checked; no
issue found. Reviewer did not rerun the build. Root's targeted build passed:

    ./scripts/lake.sh build Research.AndPenaltyAudit

Source acquisition/visual check (temporary files outside the repository):

    curl -L --fail --max-time 30 -o /tmp/ecdlp-icn-2026-0017.pdf https://www.sciopen.com/local/article_pdf/10.23919/ICN.2026.0017.pdf
    pdftoppm -f 7 -l 8 -scale-to 1500 -png /tmp/ecdlp-icn-2026-0017.pdf /tmp/ecdlp-icn-page

No PDF/build products are committed. Earlier patch application failed on an
incorrect Audit.lean anchor before changing files; corrected anchor applied.
No failed proof is hidden. Root's full repository check passed after review:

    ./scripts/check.sh > /tmp/ecdlp-h020-penalty-check.log 2>&1

## Complete-work relevance

Sol read primary sections2–5; root cross-checked experimental parameters and
base construction. The paper reports field prime32887, group order32647, one
target, a16-point signed factor base, and labels alpha,beta in0..200. It reports
4000 reads at20 microseconds per anneal; a complete end-to-end cost comparison
against classical methods is absent. Coefficient magnitude is its compression
metric, not total solver work. These reported parameters were not independently
recomputed here and are not a full-range success benchmark.

Our elementary matched comparator: a fixed signed base of16 points has at most
16*17/2=136 unordered pairs including repetition. Enumerate their group sums
once, retaining witnesses; each subsequent two-base-point relation query is
a dictionary lookup. This charges finite preprocessing and says nothing about
an asymptotic attack on arbitrary growing bases. There is no evidence here that
annealing improves complete work over this comparator.

For any repaired auxiliary penalty, the residual matters too. Flipping u4 in
(a*u1+b*u2+c*u3+d*u4-v*p)² changes it by
2*d*(a*u1+b*u2+c*u3-v*p)+d². A domination proof must account for the allowed
residue range and this term. This identity is independent paper algebra, not
part of the Lean claims above. No proof that the published coefficient rule
handles every such term was found; the false zero already decides the literal
local claim without relying on this second concern.

## Decision

Do not admit the literal penalty's coefficient reduction as a semantics-preserving
ECDLP optimization. A repaired encoding would need exact constraint equivalence,
public coefficient bounds, and matched complete solving costs before testing.
Verified improvement remains **NONE**; square-root reference unchanged.
