# W030 root-table audit: parent disposition

Accepted within the scope of the [independent report](W030-uncarried-root-review.md).
**Verified complete factoring improvement: NONE.** Symbolic audit only;
no experiment, shared solver edit or new Lean theorem accompanied acceptance.
The report was read in full (274 lines). All 17 delivery payloads and 12
frozen input copies match; the manifest also matches the SHA-256 supplied
in the task's terminal result. [Intake](W030-root-parent-intake-hashes.json).

The two square-class tables cover exactly the rooted unit-weight pairs.
Each coordinate requires only one root lift in its assigned class. The
uncarried representative is congruent to the ordinary product and lies
below L*(ell-1)*Q. Its signed padded carries preserve every covered root.
Low-digit block filtering retains the actual W024 witness on an eligible
base and makes every retained integer exponent nonzero. The valuation
strata have geometric total coordinate size. Localization must preserve
the newly frozen padded product and all its occurrence tags, not silently
switch back to an old representation with different padding.

Adopt the review's concrete setup accounting: small-ell square table,
digit Hensel lifting, O(k*ell^2) bucket labels, shared bucket references,
and actual operand widths. The original cover needs p prime but does
not require q=N/p prime. Its strict rectangle and nonzero unit-weight
hypotheses remain in force after valuation stripping.

Adopt the column recurrence. With D_i=ell^i*(B_v mod ell^(L-i)),
D_(i+1)=ell*D_i-Q*b_(v,L-1-i), so R=sum_i a_(u,i)*D_i. Column powers
X_i=alpha^(-sign*D_i) are constructed in O(L*log ell) modular
multiplications per column, with checked unit alpha and paid tables.
A supplied pair now costs O(L) arithmetic operations, not the original
O(L^2) direct convolution. Caching every feature costs O(V*L) words;
this is distinct from storing the coordinate-root input. It does not
eliminate the UV pair count of the existing consumer.

The polynomial identity is correct. Correct the parent's subset wording:
the 2^b objection prices literal subset enumeration, not all merged
support or circuit algorithms. Likewise the dense box is an allocation
choice, and full rank over Q only obstructs constant many linear digit
features for arbitrary vectors. None is a general product lower bound.

The [digit-cut continuation](W030-digit-cut-consumer.md) has its own live
Grok review after two retained Opus provider failures; this disposition
does not pre-accept that audit. The new
[unbalanced frontier](W030-unbalanced-cost-frontier.md) is parent work
outside the root review's frozen input. It explains why even the
conditional balanced one-sixth estimate cannot yet support a complete
exponent improvement.
