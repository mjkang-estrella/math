# I329 — A qutrit obstruction to importing a PPT Bell example

2026-10-13. **Terminal research result: the requested bipartite Bell-nonlocal member of the represented class has not been constructed, and Bell locality of the whole class has not been proved. No substantial finding is nominated or accepted.** The one main contribution here is an exact, dimension-specific obstruction: a partial-transpose-invariant member of the represented class on `C^3 ⊗ C^b`, `b ≤ 3`, is separable. In particular, the analytic Vértesi–Brunner two-qutrit Bell state cannot belong to that class, even with arbitrary rectangular, non-trace-preserving representing maps. Its membership is impossible, rather than merely an unpaid certificate.

## Premises and scope

The pinned premise is `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, manuscript `Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026`. Actual source statements were read: `foundations.tex`, Definition `def:represented-class`, Lemmas `lem:ppt-stability`, `lem:tensor-closure`, and `lem:choi-transfer`; `transcripts.tex`, the entire Definition `def:protocol`; and `secret-key.tex`, Definition `def:distillable-key`, Theorem `thm:zero-key`, and Proposition `prop:operational-extensions`. Input hashes, exact read ranges, and immutable URLs are in [input-authentication.json](../experiments/i329_zero_key_bell/input-authentication.json).

Thus `ω ∈ C` means

\[
\omega=(L\otimes M)(\chi\chi^*),\qquad
L,L\circ T_r,M,M\circ T_s\text{ CP},
\]

for arbitrary finite input dimensions `r,s`; only the output has trace one. The maps are PPT in the output convention as well. The representing vector is algebraic proof data, not an additional physical resource supplied to a Bell experiment or key protocol.

The source proves `K_D(ω)=0` for its admitted completed protocols. These allow joint processing of all copies, local memories and private randomness, authenticated two-way public communication, finite or countable standard Borel histories, and the specified reference-compatible complete laws and terminal readouts. The supplied state is the only shared private resource. Initial shared randomness is public and recorded. Eve retains a purification and the complete public record, including public control and stopping data. The unhalved trace-norm distance of every completed bit output from every ideal bit law is at least `1/5`; this includes the source's expressly stated conditioning and completed-output-limit extensions. No larger, unspecified model of infinite-time quantum readouts is asserted.

One standard external theorem is used: PPT positive matrices on `C^2 ⊗ C^b`, `b ≤ 3`, are separable. This is [Horodecki–Horodecki–Horodecki, Theorem 3](https://arxiv.org/html/quant-ph/9605038); its statement and proof were read. Its proof invokes the established low-dimensional positive-map classification, which is not independently reclassified here. The Schmidt-number ingredient used below is independently derived in [analysis.md](../experiments/i329_zero_key_bell/analysis.md), with its existing literature provenance identified.

## The main obstruction

**Theorem Q329.** Let `1 ≤ b ≤ 3`. If a density operator `ω` on `C^3 ⊗ C^b` belongs to the source's class `C` and

\[
(T_3\otimes\mathrm{id}_b)(\omega)=\omega,
\]

then `ω` is separable. There is no restriction on the representing input dimensions, ranks, trace conditions, or normalization of `χ`. Consequently, no entangled state with these output dimensions and this invariance can be obtained by a nonzero product CP filter from any finite tensor product of members of `C`.

**Proof.** Choose a representation and replace `L` by

\[
\widetilde L=\tfrac12(L+T_3\circ L).
\]

The output is still `ω`. Both summands are CP. Moreover, `L∘T_r` is CP, and `T_3∘L∘T_r` is CP by simultaneous transposition of the CP map `L`. Thus `\widetilde L` is an allowed representing map and `T_3∘\widetilde L=\widetilde L`.

Its Choi matrix, with the two factors interchanged, is positive on `C^3 ⊗ C^r` and invariant under transposition of the first factor. Lemma S329 in the analysis shows that its Schmidt number is at most two. The Choi–Kraus correspondence therefore gives Kraus matrices `A_k:C^r→C^3` of rank at most two. Put `v_k=(A_k⊗I_s)χ`. Each `v_k` has Schmidt rank at most two, and

\[
\omega=\sum_k(\mathrm{id}_3\otimes M)(v_kv_k^*).
\]

Each summand is positive and has positive partial transpose on Bob, because `T_b∘M` is CP. Its support on Alice is contained in `ran A_k`, of dimension at most two. Compressing to an orthonormal basis of this support gives a PPT positive matrix on `C^{d_k} ⊗ C^b`, `d_k ≤ 2`. For `d_k=1` it is a product; otherwise the cited `2×b` theorem makes it separable. Reembedding and summing preserve separability.

For the operational consequence, finite tensor products remain in `C`. If `F,G` are local CP maps and the output has trace `p>0`, it has the representation

\[
\frac{(F\otimes G)(\omega)}p
=((F\circ L)\otimes(G\circ M))
  ((\chi/\sqrt p)(\chi/\sqrt p)^*).
\]

Both input-transpose CP conditions persist. Apply the proved assertion to any filtered output with the stated dimensions and invariance. This argument includes local unitary changes of basis by undoing them before applying the assertion. ∎

This is a separability obstruction on a specified subclass, hence also a Bell-locality obstruction there: a separable decomposition supplies setting-independent hidden weights and the two local Born response probabilities for every finite family of POVMs. It is **not** a theorem about all two-qutrit PPT states, all two-qutrit members of `C`, or all PT-invariant members of `C`.

## Exclusion of the analytic Bell predecessor

The explicit [Vértesi–Brunner state, Eqs. (1)–(8)](https://arxiv.org/html/1405.4502v2) is real and invariant under both partial transposes. Its eigenvector normalization, trace one, both invariances, the local bound over all 48 deterministic strategies, and the algebraic Bell evaluation were checked independently with exact rational/radical arithmetic. The evaluation is

\[
I=\frac{-3386+18\sqrt{42}-5\sqrt{131}+45\sqrt{5502}}{43025}
>\frac{28249}{107562500}>0.
\]

The exact Bell certificate and replay code are in the analysis. This independently establishes entanglement, while Q329 excludes membership in `C`. It also excludes an exact local-filter construction of this state, or a locally unitary equivalent copy, from finite tensor products of `C` inputs. No conclusion about this predecessor's unrestricted `K_D` follows from nonmembership.

## Audit against the source's entangled PT-invariant construction

The parent's later caution is correct. In `projection.tex`, Eqs. `eq:projection-block-symmetry` and `eq:projection-composite-entries` give

\[
H_{ij}=H_{ji}=H_{ij}^*,\qquad
C_{(i,a),(j,b)}=\operatorname{tr}(H_{ab}^*H_{ij}).
\]

Swapping `a,b`, or swapping `i,j`, leaves these entries fixed. Thus `C` is invariant under **both** partial transposes. Under the projection criterion the source proves that `C/(Q²D)` is nevertheless entangled and belongs to `C`. The actual combinatorial construction has much larger outputs. There is no conflict with Q329: its critical output bound `3×b`, `b≤3`, is absent. In larger dimensions, the rank trimming need not reach two, and PPT on `2×b`, `b>3`, is not a separability criterion. PT invariance plus represented-class membership alone never appears as a separability claim here.

The parent's natural block-filter local model was independently verified, including every failure outcome. An exact one-sided context-pinching calculation in the analysis explains why block-incoherent measurements cannot repair that proposal. It is a diagnostic of the proposed measurements, not a second nominated finding or a proof of general Bell locality.

## Remaining operation and contribution assessment

The full target remains **unproved and unrefuted**. For the explicit dimension-ten state, the missing operation is an exact finite Bell operator with a proved local bound, valid local POVMs, and a strictly positive evaluation. Its product-free range and entanglement witness do not pay that operation. For a direct POVM test of the projection family, or a product-filter test satisfying the pulled-back-effect description in the analysis, a successful experiment must access coherence between different context blocks on both sides; setting-dependent selection followed by conditional KS correlations fails the audited local model. No coherent POVMs with a positive unconditional Bell gap have been certified. No analytical factorization of a higher-dimensional Yu–Oh Bell state into two allowed PPT maps has been established.

Correctness, substantiality, and priority are separate. Q329 has a complete independent deduction and an exact excluded-candidate certificate; its low-dimensional tools are published machinery, and the exclusion is a technical application, not a demonstrated new-to-literature theorem or a resolution of the research question. The pinned catalogue/tree contain one manuscript in this zero-key family; its internal parallel constructions and relevant earlier project records were inspected. Later primary literature was checked as documented in [literature.md](../sources/i329_zero_key_bell/literature.md), without claiming exhaustive priority coverage.

Only the five assigned artifacts were written. No subagents, git, numerical searches, publication, shared-index changes, live I325/I327 outputs, or retained new full external source bodies were used. No acceptance or finding-count change is made.
