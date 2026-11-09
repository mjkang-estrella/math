# Final bridge

The 23 r12 modules establish the literal finite law and all-N coefficient bound without mathematical assumptions beyond the three standard Lean axioms. They are replayed from source, not replaced by axioms or supplied ordinary-proof hypotheses.

For any admissible full-sigma events A,B, complementing A changes the covariance to its negative, by P(A^c)=1-P(A) and P(A^c intersect B)=P(B)-P(A intersect B). The prefix sigma-algebra is closed under complements. Consequently the supremum of signed covariances equals the supremum of absolute covariances at every cut and lag. Endpoint.lean proves this at the supremum level for every N,k.

All split coordinates after the maximum complete-word duration are zero. Adding them to a generated suffix sigma-algebra has no effect. The empty finite index interval generates bottom. A bottom-measurable event is empty or universal and has covariance zero. This also checks the source's infinity notation, its constant coordinate zero, and unrestricted natural cuts. In particular alpha_N(k)=0 for k>d_N.

Fix arbitrary real delta>0 and put r=delta/(4+delta)>0. Each term (k+1)^2 alpha_N(k)^r is nonnegative, and is zero for k>d_N because 0^r=0. The real series is therefore summable. Only after proving this do we use the single-term lower bound for its tsum.

Set n=fibIndex N and k=n^6. For all sufficiently large N the inherited all_N_uniform_alpha_ninth gives alpha_N(k)>=1/9 (n>=1 always). Thus the weighted series is at least (k+1)^2*c, where c=(1/9)^r>0. Since n tends to infinity, so does this lower bound. The Lean proof fixes arbitrary real M, chooses a natural b>M/c and eventually has n>=b and k>=n; then (k+1)^2>=b and the series exceeds M. The proof is uniform in all sufficiently large N for the fixed delta,M, without selecting a subsequence.

If the source claim held for delta,C, divergence would eventually give series>=C, contradicting its strict series<C for every N. Source coefficient equivalence transports this unconditional contradiction to both versions. No assertion about a Gaussian limit or realization-only event restriction follows.
