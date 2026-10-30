# Root adoption of preliminary review — 28 October 2026

Credit 0. Original six-file freeze root-cauchy-strict-r1@721c6d4700 is untouched.
Root read the completed review report and thread through position 63.
The review confirms the prefactor, Vandermonde, tail-domination and analyticity
errors; it adds an incorrect integrability-rate sentence. These must all be
fixed in a working copy before any new mathematical PASS is claimed.

Root prefers a cleaner replacement for the delicate tail estimate: write
G(z)=sum_(k>=1)c_k z^k, an entire function by the stable-series coefficient
bound. With t=exp(alpha U), the shifted stable determinant equals
exp(mU)*product(z_i)*product(w_j)*det[G(t*z_i^alpha*w_j^alpha)].
The last determinant is entire in t. Its Taylor coefficients below
S=m(m+1)/2 vanish because repeated column powers give zero; its coefficient
at S is product(c_1,...,c_m) times the two Vandermonde determinants with the
correct extra powers. Thus an ordinary Taylor expansion at zero proves
nonvanishing without the frozen false k-uniform bound or a circular tail
constant. This repair has not yet been integrated into the full draft.

The review recommends substantive eligibility with bounded novelty limits.
Root retains one sharper generic-theorem question: analytic weak Markov / weak
Chebyshev systems can become strict after removing common zeros. The review's
counterexample exp(-abs(x)) is nonanalytic and only refutes the weaker Fourier-
nonvanishing shortcut; it does not settle this analytic-specific question.
The newly located Zwick 1984 paper *Degeneracy in WT-spaces* is a primary lead,
not a body-level subsumption finding. No further review launched for it yet.

No Lean exists. Reproving the stable-density TP theorem and the source bridges
is a major unresolved formal dependency. Published JAT/Constr. Approx. bodies
and Karlin/Pinkus books remain unread. No new packet, count or acceptance.
