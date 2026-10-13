# Parent local endpoint coercivity route

2026-10-13. Unreviewed input to active I325, not a proved theorem or accepted finding. This records the in-flight argument and its remaining obligations.

Write u=v+l+h, where v=m+bX_i, l is the remaining first Walsh chaos, and h has levels at least two. Suppose a tends to zero, m tends to zero, l/a tends to zero, and ||h||_2=O(a²). The proposed local conclusion is Delta >= c(m²a4+a²||l||²+||h||²), with no artificial ||u-v||_2 <= a^M hypothesis.

Keep the one-coordinate baseline and the entropy-profile concavity comparison exact, as in I321. Replace the input entropy only in a neighborhood of the perturbation argument by a smooth globally defined convex function psi_tilde <= psi on [-1,1], agreeing with psi on [-1/2,1/2], with bounded relevant derivatives and a positive Hessian lower bound. This allows evaluating psi_tilde at v+l even if an exceptional first-chaos tail leaves [-1,1]. First-chaos moments are uniformly controlled by hypercontractivity; however a purely additive exponentially small tail error is not automatically adequate when the target deficit is arbitrarily small. A full proof must make errors vanish relative to the perturbation, and must construct and verify the extension.

The level-at-least-two h term is expected to have an order-one spectral gap near m=0: input strong convexity and output contraction r^4 are compared against entropy-profile slope approximately r². Thus the output q>2 remainder O(||h||_2^q) can be absorbed against ||h||², without paying against a²||h||². The linear coupling with h should be bounded by

 C[|m|a||l|| + (|m|+a)||l||² + ||l||³] ||h||.

This comes from projecting the input/output first derivative difference onto Walsh levels at least two; constant and singleton terms vanish by orthogonality. Completing squares would cost O(m²a²||l||²+(m²+a²)||l||4+||l||6), which is absorbable by a²||l||² as m,l/a tend to zero. The pure-l Hessian must be computed with the exact baseline to retain its positive a² coefficient, rather than bounded by a coarse isotropic estimate. These are proposed operations, not estimates already established here.

A separate exact inequality sent earlier is B_psi(x+w,x) >= w²/2 + x²w²/2 + x w³/3 + w4/12 for |x|<1, |x+w|<=1. It follows because psi(t)-t²/2-t4/12 is convex: its second derivative is t4/(1-t²). Using only this lower polynomial loses higher powers of the baseline mean and can therefore destroy the cancellations required for sharp stability.

Even a complete local argument of this form would not settle global entrance, nor means approaching ±1. The full I325 target retains those regimes. No acceptance is implied.
