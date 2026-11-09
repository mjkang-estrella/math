# W028: accept the circuit identities; reject a broad extraction barrier

The independent [parity review](W028-parity-circuit-review.md) was read in
full (130 lines). Accept the residual and prefix identities, logarithmic
derivative and trace identities, four-state parity circuit, Chebyshev pole
polynomial, and the exact reduced section degree over Q. The positive-real
pole argument is not exported to finite fields. **Verified complete
factoring improvement: NONE.**

The review strengthens one degree statement correctly: for k>=1 the leading
coefficients of P_k and Q_k are units modulo every odd N, so their individual
polynomial degrees are exactly n/2 and n/2-1 there too. This says nothing
about cancellation in the reduced rational function after later sections.
For the least power n of two strictly exceeding m>=1, use m<n<=2m; the
review's strict n<2m misses power-of-two m.

The accepted result is a representation and its paid generic implementations.
Do not adopt the review's opening assertion that no consumer can be faster
than a length-m product, or its blanket sentence that the scalar hope fails
on this circuit. No general single-coefficient or circuit lower bound was
proved. Its own narrower representation qualifications are the valid scope.

The [explicit composite-ring baseline](W028-composite-coefficient-baseline.md)
uses monic product/remainder trees to return either the central coefficient
or a proper factor in O~(sqrt(m)) ring work plus gcds. Its unit-denominator
branch really does compute the residue, while its failure branch is a paid
factor extraction. This is standard Strassen-style work, not a new transfer
of a prime-field automaton theorem and not an improvement in factoring.
The primary Bostan–Gaudry–Schost paper explicitly works over rings with zero
divisors in its factoring application. Its known-prime, precomputed automaton
counterpart must still not be used at unknown p for free.

Repair the source locator: Bostan–Mori's effective-ring setup is footnote 0
on printed page 1 and its unit-constant algorithm is Algorithm 1 in section
2.1. Text-extraction line numbers are not portable. The parent's earlier
line-range phrase incorrectly included the setup in the algorithm window;
the hypotheses themselves were correctly stated.

All 14 delivery payloads match the local manifest; no external manifest
anchor was supplied. See [intake](W028-parent-intake-hashes.json). No
experiment ran. The frozen parent files remain preserved in child evidence;
no shared solver or Lean changes are made by this intake.

Next computation: finding a genuinely smaller state for the requested
functional is still open; writing a resultant or trace does not supply it.
The separate W029 probe changes the invariant to a factor-bearing formal
degree and computes a divided derivative explicitly. Its first scalar test
has an order-condition comparator and is independently under audit. None
of these checks warrants a claim that factoring or coefficient extraction
is intrinsically hard.
