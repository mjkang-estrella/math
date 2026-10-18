# Author candidate: nonnegative-bisectional uniformization

Conditional on the pinned source338 main theorem and its explicitly mapped proof operations, the proposed full statement is:

**For every connected simply connected complete noncompact smooth Kähler manifold M of finite complex dimension n>=1 with nonnegative holomorphic bisectional curvature, there are k>=1 and finitely many irreducible compact Hermitian symmetric spaces S_j such that M is biholomorphic to C^k × product_j S_j.** The empty compact product is allowed. There are no upper curvature, volume-growth, curvature-decay, pinching, or other assumptions at infinity. The original metric on the complex Euclidean factor is not claimed flat.

The exact scope was recorded prospectively in scope-status.json before the proof modules were assembled. This is author research, not an independent proof/contribution verdict, acceptance, or publication. All review gates remain pending. No result from frozen r85/r87 is used or counted.

## Proof assembly

1. Apply Ni–Tam Theorem4.2(i) (arXiv:math/0304096v1) to M. This yields a holomorphic isometric product N × X, with N compact simply connected Kähler of nonnegative bisectional curvature and X complete noncompact simply connected Kähler of nonnegative bisectional curvature admitting a smooth strictly psh function with bounded gradient. The simply connectedness of X follows from the product and simply connectedness of M. Since M is noncompact and N compact, dim_C X>=1.
2. The compact generalized Frankel theorem, stated in Gu Theorem1.1 and credited there to Mok with the Howard–Smyth–Wu reduction, makes N biholomorphic to a finite product of irreducible compact Hermitian symmetric spaces (including complex projective spaces). Its Euclidean factor is absent because N is compact and simply connected.
3. If X is flat, completeness and simple connectedness identify it holomorphically isometrically with C^k. Otherwise apply nonnegative-flow-bridge.md. That proof checks source338's entire initial-data → localized flow → scalar comparison → cotangent-disc/deformation → joint positivity chain under the Ni–Tam inputs and obtains complete positive-time slices. It does not use source338's shrinking-chart strict-curvature estimates on X.
4. Apply fixed-time-factorization.md to one positive-time slice. The local null propagation is justified in local-null-propagation.md directly from the primary Brendle–Schoen Proposition1, with compact-path localization. The fixed-time factorization excludes compact factors using the strictly psh function, handles special holonomy using nonnegative Ricci, and proves full bisectional positivity on every nonflat irreducible factor, explicitly including nonorthogonal vector pairs.
5. Every such factor now satisfies the ORIGINAL positive-curvature main theorem of source338 with all its hypotheses, including completeness and noncompactness. It is therefore biholomorphic to complex Euclidean space. Their finite product with the flat factor gives X biholomorphic to C^k, and Step2 completes the displayed claim.

The proof uses a fixed-time factorization, not backward uniqueness or a persistent product splitting for an unbounded-curvature flow. Completeness is proved before de Rham is invoked. The strong maximum/null propagation arguments are used only after nonnegative curvature is established by the source-derived joint-positivity chain.

## What is already paid

Cao–Chen–Zhu Theorem2.8 already proves the reduction from bounded nonnegative bisectional curvature to complete positive factors, flat factors, and compact symmetric factors. Its combination with source338 pays the entire bounded-curvature subclass. Liu Theorem1.1 already pays nonnegative curvature with maximal volume growth, without curvature bounds. Ni–Tam already pays the initial compact splitting and strict psh function. None is nominated separately.

The new author integration is the generalization of the source's unbounded, possibly collapsed localized-flow construction to the Ni–Tam factor and its completion/fixed-time factorization under those inputs. Whether this amounts to substantial new mathematical contribution, as opposed to a technical consequence of source proof operations, is an independent-review question; no favorable contribution verdict is self-awarded.

## Modules and limits

- nonnegative-flow-bridge.md: complete source-operation use-site proof.
- local-null-propagation.md: localized strong maximum argument, a supporting lemma only.
- fixed-time-factorization.md: holonomy, all-pair algebra, and source application.
- mechanism-checkpoint.md: live chronological findings, including the failed direct psh metric deformation; later entries supersede earlier unresolved-reading descriptions.
- reading-limits.md and comparison.md: exact reading and literature limits.

No numerical test certifies any infinite-dimensional flow, tensor maximum principle, or global uniformization. The finite checker only checks simple rotation/cofactor, scalar comparison shell exponents, and fourth-jet bookkeeping. The full theorem is not formalized.
