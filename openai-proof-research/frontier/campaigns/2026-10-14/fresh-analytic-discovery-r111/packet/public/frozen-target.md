# T085E111 — frozen full research target

Source premise: all pinned OpenAI theorem statements and operative proof operations at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true under their exact contracts. Every new deduction requires independent validation.

For each finite real E>=1, let S_E be the set of real symmetric positive-definite 2x2 matrices A with det(A)=1 and lambda_max(A)/lambda_min(A)<=E. Let B be the open Euclidean unit disk in R^2. For every real f in W^{1,1}(R^2), define

    M_E f(x) = sup_{r>0, A in S_E} [1/(pi r^2)] integral_{x+r A B} |f(y)| dy.

The ratio in S_E is exactly the ratio of the two semiaxes; orientations are unrestricted. The target is:

    For every finite E>=1 there exists a finite C(E), depending only on E,
    such that for every real f in W^{1,1}(R^2),
        M_E f belongs to W^{1,1}_loc(R^2),
        integral_R^2 |gradient M_E f| <= C(E) integral_R^2 |gradient f|.

The gradient is the distributional weak gradient and its norm is Euclidean. No global L1 integrability of the output is asserted. There is no restriction on support, sign, symmetry, scale, maximizing orientation, aspect ratio, uniqueness or separation of maximizers. All radii r>0 and all allowed shapes participate in the same supremum. No explicit rate of growth of C(E), nor a constant uniform as E tends to infinity, is required. The entire endpoint claim, including absolute continuity of the derivative, is retained.

E=1 and a single fixed A are credited source/affine cases, not nominations. A finite-net theorem with a cardinality-dependent bound, a local radius-band estimate, an interior-aspect theorem, or a sequence/subsequence of shape families is not a replacement. If the full claim is not established, retain this file byte-for-byte and archive the precise missing operation with no nominee. No acceptance, count, gate or substantiality rating is assigned by this file.
