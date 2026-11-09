# I342 independent contribution review of frozen I341

Date: 2026-10-13. Reviewer: GPT-6.1 Sol (`gpt-6.1-sol`), high reasoning, through the Codex harness in T3 Code. The brief requests Standard speed; the harness does not independently attest a speed setting. No subagents were used.

**Contribution verdict: TECHNICAL. Proof verdict: PASS within the exact finite model and record-preserving trace-norm closure stated below, conditional on the stipulated pinned OpenAI source. No rigorous flaw was found in the frozen proof.** This is not a claim that the full adaptive theorem was already published verbatim, so KNOWN/DUPLICATE is not the verdict.

The full candidate was authenticated before review: `frontier/iterations/i341-adaptive-ppt-square-key-obstruction.md`, SHA256 `1e66ba9bc7c98ced6deb292c960e9e5eb731b24aefd0e0884e5647d718078e91`. The parent's newly supplied `frontier/iterations/i341-parent-postselection-objection.md` was read separately; it does not replace or modify that candidate.

## Scope assessed

The initial shared state is any normalized C state represented by two arbitrary rectangular PPT CP maps on an arbitrary, possibly unnormalized, bipartite vector. Local private memories and dimensions are arbitrary finite ones, without a bound uniform over protocols. Each available transmission is a channel Phi=Q P; both factors are PPT but need not be trace preserving, while Phi is trace preserving. Factors are inaccessible separately. Channel and direction choices depend on public history. Finite local instruments and two-way public communication are allowed. Eve holds the initial purification, all composite-channel environments and the complete public record. Private dilation systems remain with the parties. The conclusions audited are branchwise C closure, unhalved distance at least 1/10 from every nonempty fixed-length ideal key, 1/5 when the comparison has the actual transcript marginal, zero two-way assisted key capacity, adaptive switching, and trace-norm closure on fixed finite output spaces retaining the specified information.

The non-entanglement-breaking example is **Theta squared**, where the source's Theta is a PPT channel on Mat(21). This review makes no zero-key assertion about Theta alone. All ingredients and consequences comprise one connected candidate; the nomination total has no role in the verdict.

## Affirmative mathematical reason for TECHNICAL

For every TP channel with input dimension d, its normalized Choi state j_Phi=J(Phi)/d simulates it under a single selected normalized Bell effect at the sender:

    (bra beta_d tensor id) [X tensor j_Phi] (ket beta_d tensor id)
        = Phi(X)/d^2,       beta_d=Omega_d/sqrt(d).

The identity holds with an arbitrary entangled spectator. Source `lem:choi-transfer` puts j_(QP) in C. Source tensor closure and PPT stability then put the normalized selected output of **any** C input in C: tensor with j_(QP), apply the sender's local Bell filter, and divide by its nonzero success weight 1/d^2. Reversing which party owns the reference and output handles the opposite direction. This gives the entire cross-party closure operation without the candidate's new reshuffling map. Ordinary induction at each public branch preserves correlated memories and adaptive channel choices.

The physical purification calculation is equally exact: if V is the actual composite-channel Stinespring isometry, use the Choi purification (id tensor V)ket beta_d. Bell contraction sends ket psi to V ket psi/d, also with any reference. Thus the successful normalized simulation supplies the same channel environment to Eve. This is not merely equality of AB marginals.

Whole-run success weighting needs care. Along terminal public record r the multiplier is w_r=product d_v^(-2), so naive all-success conditioning generally biases transcript probabilities. The parent's repair is correct: for a finite public decision tree, let a=min_r w_r>0, and publicly accept a successful terminal branch with probability a/w_r. The resulting accepted original transcript probability is p_r, because the unnormalized accepted block is a p_r tau_r. A completed simulation produces fixed bits on failures and retains every success, rejection and original public record. Source `prop:operational-extensions`, item 1, explicitly preserves the 1/5 gap under conditioning on **any** positive-probability public event; no efficiency or lower bound on a is needed. Unused Choi purifiers add only a state determined by r, independent of the keys conditional on r. An Eve-only channel appends these states and embeds the used physical environments, so every physical ideal comparison lifts to a simulated ideal comparison. Hence a gap for the accepted simulated output implies a gap for the original physical output. The detailed construction is in the assigned analysis file.

Alternatively, the one-use C closure and the candidate's valid branchwise p-versus-q argument give precisely the claimed 1/10 bound without equalizing weights. Either route preserves all the requested quantifiers. Ordinary zero distillable key of a Choi state would not justify this conclusion: the decisive upstream input is the uniform, filter-compatible C obstruction, explicitly strengthened to arbitrary public postselection. Therefore no additional substantial operation is needed beyond established channel-state contraction and the supplied source interfaces.

## Frozen proof audit

1. Local CP postcomposition, normalization on a positive branch, private dilation retention and the separable-state representation all check out.
2. For F=(id_A tensor P)L, the identity `(T_A tensor id_D)F=[id_A tensor (P T_C)] [(T_A tensor T_C)L]` is dimensionally correct and a composition of CP maps. The identity does not use complete positivity of a bare partial transpose.
3. J(R) really is J(F) permuted from I,A,D to I,D,A on both ket and bra indices. Its A-output partial transpose is the corresponding permutation of J((T_A tensor id_D)F), so R is PPT. This is not a general realignment operation.
4. The vector chi tensor unnormalized Omega_D contracts the D indices in the correct order and introduces no dimension multiplier. R tensor (M tensor Q) exactly reproduces the transmitted state. Composite TP, not TP of either factor, gives normalization.
5. A public CP branch can be dilated into retained local memory with a single branch operator. Conditioned on a fixed public record, initial purification and channel isometries leave a pure state of the enlarged laboratories and Eve. Final discarded local systems are part of local readout, not extra Eve information.
6. Source `thm:zero-key` applies at n=1 to this normalized C marginal and arbitrary Eve purification. The public-weight inequality yields D>=1/5-sum|p-q|>=1/5-D, hence D>=1/10; equal weights yield 1/5. Dephasing handles coherent comparison records. First-bit contraction, the capacity conclusion and continuity on the stated output space are valid.

The equalized simulation plus source public-conditioning proposition in fact yields 1/5 against every ideal comparison for finite trees. This is an optional stronger consequence, not an objection to the frozen candidate's weaker 1/10 claim or a second nomination.

## Credit and limitations

OpenAI, *Entanglement with zero distillable secret key in local dimension ten*, at commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, supplies C, its uniform operational obstruction, tensor/Choi interfaces, public-conditioning extension and the dimension-21 non-EB square. Upstream truth was stipulated and not re-audited. Christandl–Müller-Hermes–Wolf (2019), Lemma I.1(2) and Section IV.B, supplies the old transpose-adjoint/local-product machinery. The postselected channel-state identity is explicitly recorded by [Wang–Wilde, Appendix A.2](https://arxiv.org/html/1905.11629v3#A1.SS2), equations (69)–(70) in the HTML rendering. The parent supplied the postselection objection and dimension-dependent acceptance repair; this reviewer independently verified them.

[CMHW Section IV.B](https://arxiv.org/html/1807.01266v2) alone is not an adaptive secret-key theorem. [Kaur–Wilde](https://arxiv.org/html/1707.07721v3) provides an adaptive amortization/simulation comparison, but deterministic simulation and a vanishing key-relevant entanglement bound have not been established for these channels. [Bäuml–Christandl–Horodecki–Winter](https://arxiv.org/html/1402.5927v2) studies a different three-party repeater resource model; its PPT rate bounds do not by themselves prove this uniform obstruction. No world-priority certificate, exhaustive literature search, infinite-memory extension or theorem about arbitrary PPT channels is asserted. Read scopes, source digests and failures are preserved in the other four assigned files. An initial filename inventory exceeded the project boundary; no other-project body was read or written, and this deviation is expressly recorded.
