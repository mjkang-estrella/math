# Family083: maximal truncation remains unpaid

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Pre-freeze screen, not a candidate or acceptance. Upstream truth is stipulated at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

The source's main theorem bounds sup_epsilon ||H_epsilon f||_2 for Lipschitz unit fields, with a sufficiently small fixed outer endpoint. It does not state ||sup_epsilon |H_epsilon f|||_2. Its pointwise principal-value assertion is on Schwartz inputs; the bounded extension to L2 does not by itself assert pointwise convergence for every L2 input. Uniform bounds and dense-class convergence do give strong L2 convergence, which is a routine deduction and is not nominated.

The possible stronger target screened here was an L2 maximal hard-inner-truncation bound, hence almost-everywhere principal values for all L2 inputs. No complete mechanism was obtained, and this target is not frozen.

## The specific reassembly obstacle

The pinned reductions section writes H_epsilon = integral C_t S_t^x dt/t, where C_t h(x,y)=h(x,y-tu(x,y)). For every randomized vertical Littlewood–Paley multiplier T, red:composition-commutator proves ||[T,C_t]|| <= C|t|. Integration cancels the singular measure, giving red:integrated-commutator and then the square-function estimate red:reassembly. The scalar inner endpoint is essential to this displayed operation.

For a measurable choice epsilon=epsilon(x,y), let m_t=1_{epsilon(x,y)<|t|<a}. The exact identity is

    [T,H_epsilon] = integral (m_t[T,C_t] + [T,m_t]C_t) S_t^x dt/t.

The first summand retains the source estimate. The second is new. Its coefficient is merely measurable, not Lipschitz; the source commutator estimate for a Lipschitz coefficient cannot be applied to it. Bounding it separately in norm and integrating dt/|t| loses uniformity in the smallest endpoint.

This lack of a pointwise-in-time gain is literal. Take u=0 and epsilon(y)=delta for y>0, epsilon(y)=a for y<0. For delta<|t|<a, m_t is the fixed half-line indicator. For the vertical Hilbert multiplier T, [T,m_t] is a fixed nonzero bounded operator, independent of t and delta. It therefore cannot obey a uniform O(|t|) estimate as delta tends to zero. The Hilbert multiplier meets the source's smooth-away-from-zero multiplier seminorm condition. This is only an obstruction to that absolute commutator argument: the actual maximal transform for the constant field is bounded, and cancellation in the integrated expression can still matter. No counterexample to the desired theorem is asserted.

Likewise, allowing measurable endpoint changes within a constant multiple of one fixed radius in the source's preliminary annular error estimate does not provide a bound simultaneously over arbitrarily many radii.

## Actual primary proof comparison

Di Plinio–Guo–Thiele–Zorin-Kranich, arXiv:1706.07111v1, Corollaries1.3–1.4 and their proofs in Section2.5, control off-diagonal frequency leakage for the fixed truncated operator. The p=2 diagonal estimate follows from single-band bounds and Fubini. Their proof first moves a frequency projection past the fixed integral and integrates the Lipschitz composition error. It does not supply the rough-mask commutator above. The localized vector-valued theorem and its interpolation argument do not independently establish this missing maximal reduction.

Guo, arXiv:1610.05233v1, Theorem1.2 gives weak L2 and strong Lp, p>2, single-annulus bounds for its frequency-decomposed variation operator. Its definition is not silently identified with every hard spatial truncation. The complete displayed tree proof (Lemma4.5, Section5 through Lemma5.3) compares variable-direction packets with reference-direction packets, uses one-dimensional variation estimates, and controls horizontal slices by Lipschitz density. This is an antecedent for a band-level variation mechanism, not an all-frequency strong L2 maximal theorem. The need to reassemble frequencies remains. No new full-band variation estimate or hard-truncation comparison has been proved in this screen.

## Reading limits and disposition

Read the full pinned introduction; reductions lines1–240 and259–625, including the complete displayed commutator and square-function arguments. Other section files were acquired and authenticated, not read in full. DGTZK text lines1–240 and732–1017 read, including the complete Corollaries1.3–1.4 proofs. Guo text lines1–230 and401–835 read, including the full displayed Section5 tree argument (some steps there are delegated by its author to cited work, not independently re-proved here). PDF/text inputs remain private, with source and primary receipts. No layout claim, comprehensive literature search, or positive eligibility clearance is made. A focused old-ledger search found no hit, which is not a semantic clearance.

Status: PRE_FREEZE_SCREEN_UNPAID. No nominee, no independent PASS, no count. A successful continuation would need a new all-frequency maximal mechanism, rather than moving the supremum inside the source's norm or assuming its fixed-cutoff reassembly unchanged.
