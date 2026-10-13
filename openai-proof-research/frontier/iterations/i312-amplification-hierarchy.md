# I312 — independent review of the amplification hierarchy

**Proof verdict: PASS unchanged.** The complete 102-line parent proposal `frontier/iterations/i312-parent-amplification-construction.md`, SHA256 `da83fdf48779e56c2c8c694973282ecf61ea14c1134e86b9f48bfed12cc89070`, proves its exact conclusion for every integer r>=2:

    C_d(A_r)<2 for every integer 1<=d<r,    C_r(A_r)=2.

Here A_r is the stated finite, unitarily irreducible, nilpotent matrix with w(A_r)<=1; evaluation is base first. No added hypothesis, replacement construction, or necessary repair was used. [The analysis](../experiments/i312_amplification_hierarchy/analysis.md) independently expands every section and the sensitive equality steps. This is a mathematical review, not contribution acceptance or a worldwide priority certificate.

For r=3 the model has dimension 13 and A_3^7=0. With omega=exp(2 pi i/3), its explicit size-three polynomial is

    P_3(z)=(1/sqrt(3)) [ z     z^2           z^3        ]
                       [ z^2   omega z^3     omega^2 z^4 ]
                       [ z^4   omega^2 z^5   omega z^6   ].

It has disk norm one and ||P_3[A_3]||=2, whereas the supremum over **every** disk-bounded size-two polynomial is strictly below two. Thus the requested third-level obstruction is proved, not replaced by a scalar conclusion.

The compressed shift is a partial isometry with ker C*=E, ker C=F, C*C=I-P_F, and CC*=I-P_E. These identities give the proposed Ando factorization directly. They do not follow merely from the dimensions of the kernels. The polynomial transpose agrees with the base-first vectorization. The inverse-inner polynomial proves finite dimension and nilpotence, and the inner-product decomposition proves the stated dimension formula.

The decisive universal operation is equality forcing. Any norm-two matrix Schur evaluation at coefficient size d yields constant matrices V,W in M_(r,d), both of Hilbert–Schmidt norm one, satisfying

    V Q(z)^T=Phi(z)W.

Equality in the multiplier/compression norm chain removes the entire uncompressed orthogonal remainder. Disk contractivity then implies Phi WW* Phi*<=VV*, including its boundary limit without assuming continuity of Q. On the circle both traces are one, so equality holds. The all-r Fourier/difference argument forces WW*=VV*=I_r/r. Thus d>=r for every possible equality witness. This argument does not depend on the rank of one selected witness or its constant compressions. Compactness of the first L Schur coefficients turns this universal nonattainment into the strict supremum gap; normalized polynomial approximation preserves the same supremum.

For irreducibility, a reducing projection for A_r preserves E and F, hence commutes with X and with C,C*. Pairing C^k e with Phi v gives V0 Phi_k=Phi_k W0 with exactly the orientation in the proposal. Circle unitarity and the same rigidity make the two endpoint projections simultaneously zero or identity. Joint cyclicity of the constants finishes the proof.

Necessary fixes: **none**. The explicit orthonormal basis and expanded equalities in the analysis are audit details, not repairs. No unpaid operation remains for the stated mathematical theorem. No numerical scan, optimization, subagent, sibling read, git operation, publication, or shared-index edit was used. I309 and I311 were not read. The old graded rank-defect lead was superseded and was not a premise.

The credited scalar model antecedent is [Gau–Wu (2009), Theorems 5 and 8](https://ir.lib.nycu.edu.tw/server/api/core/bitstreams/761cc49b-4b82-4fd4-8748-960e6473e874/content). Its necessity proof was inspected beyond the parent's bounded read. The primary comparisons and their exact limits are in [literature.md](../sources/i312_amplification_hierarchy/literature.md). They establish a real distinction between general amplification operations and this constrained one-matrix theorem, but they do not complete a contribution gate. All r constitute **one** potential finding; R019 and I306/I307 are not counted again. No acceptance or count change is made. All pinned OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` remain stipulated true.

Exact input identities, semantic extents, and retrieval limitations are in [input-authentication.json](../experiments/i312_amplification_hierarchy/input-authentication.json) and [reading-and-failures.md](../experiments/i312_amplification_hierarchy/reading-and-failures.md). Output hashes are returned detached after finalization.
