# Mathematical routes and source controls

This is an uncredited investigation. None of the following is a new qualified endpoint.

## 319274: normalized last-increment location

Read arXiv:0911.5478, Conjecture 4 and Sections 1, 4, 5. The symbol rho is an ARGUMENT of the last nontrivial increment strictly before a fundamental point, not the largest increment size. The preceding main-increment argument is m_prev+3. The conjecture starts at fundamental index i=6. In particular the large initial ratios at i=4,5 are not counterexamples.

For a processed index n, let d=c(n)-n. As long as subsequent increments are 1, c(k-1)=k-1+d. The next nontrivial even increment must occur at an even k with gcd(k,d-1)>1; the next odd one occurs at odd k with gcd(k-2,d+1)>1. For each prime divisor of the two fixed offsets, the first index in the appropriate parity class can be computed exactly. The minimum is the next event. The zero-offset case is separately handled. A fundamental point inside the intervening run can only be k=d. This yields an exact skipping algorithm, not a random selection of indices.

The implementation compares its fundamental points AND last-increment locations against the direct ten-million-step recurrence, then continues to 10^12. Only completed fundamental intervals are assessed. The final unfinished interval is not called a pass. No violation for i>=6 occurs. Initial review caught an endpoint bookkeeping issue at m=6 (rho must be 5, not 6); both implementations were corrected to strict-before semantics and rerun. This did not affect any in-scope i>=6 entry.

An induction would have to control the divisors of changing offsets d-1 and d+1 sufficiently to bound the LAST event of every interval by 5(m_prev+3)/4. The event identity itself supplies no such bound. No inference from finite evidence to infinitely many twin primes is made. A full Lean endpoint would require the unbounded inequality, fundamental-point indexing, and recurrence bridges; none exists here.

## 321201: prime-index Stern irreducibility

Original arXiv and 2011 journal definitions agree: B0=0, B1=1, B(2n)=t Bn and B(2n+1)=Bn+B(n+1). All prime indices <=10000 were tested over Q[t], with no reducible example. This repeats a tiny subset of the original million-prime computation and is not novel.

A tempting structural argument is Bn(2)=n, which follows immediately by induction. For prime p a factorization of Bp would therefore have an integer factor evaluating to +/-1 at 2. This does not rule out a factorization: a nonconstant signed polynomial can evaluate to 1. Also, coefficients of Bp need not be binary, so a base-two digit irreducibility shortcut is invalid.

Read the published 2017 Dilcher-Kidwai-Tomkins body. Their Theorem 1.3 is the applicable Cohn criterion. Corollary 1.4 reduces the problem to Re(alpha)<3/2 for every root of Bp. Their stronger Conjecture 3.1 asks Re(alpha)<1 for all Stern polynomials. The zero restriction is the missing substance, not a proved generic fact about nonnegative-coefficient polynomials. Their explicit half-plane families and the 2019 Ulas followup do not establish the universal statement. No new zero-control lemma was obtained.

The reducible polynomial at prime 17 appearing in a different Dilcher-Ericksen paper is a DIFFERENT Stern (0,1)-polynomial family. Its recurrence substitutes t^2 instead of multiplying by t. It is unusable here. The author institutional catalogue was inspected in search results; direct HTTPS retrieval failed certificate hostname validation and was not bypassed.

## 322943: algebraic asymptotics and prior framework

The source defines P(z,u)=1/(1-u p(z)) and D_n=sum_k P_(n,k)^m. Its Theorem 5.3 supplies a Gaussian local-limit constant, algebraic apart from pi^(-(m-1)/2), when the rational part-generating function and nondegeneracy hypotheses apply. For odd m>2 the negative integer coefficient exponent is incompatible with an algebraic singularity. For even m>2 the exponent is compatible, but the CONSTANT is not: an algebraic function over Qbar has algebraic Puiseux coefficients, and transfer at the relevant half-integer exponent supplies algebraic/sqrt(pi). Equating constants would make a positive integer power of pi algebraic.

Before formalization, search located the same author's later paper, Banderier-Drmota, Formulae and asymptotics for coefficients of algebraic functions. Read Proposition 7 and its proof (PDF printed page 17). It explicitly applies the above constant argument to Franel numbers and composition tuples, citing the original Banderier-Hitczenko paper. Thus this route is already public/classical. The exact blanket wording for arbitrary N-rational p needs periodic and nondegenerate support hypotheses; no claim that every possible defective paraphrase is covered, and no credit for correcting such a defect.

## Other decisive source findings

* 321986: Definition 5.8 and Addendum 5.12 of the SAME primary manuscript settle exceptional Coxeter types using the gradient Gram matrix and Euler identity. The revised source includes the proof, despite the corpus open label.
* 323647: Daisey 2610.17441 Theorem 1.2 proves every linear LP algebra finite over any UFD. Read the minor-divisibility argument, prime factor count in the initial Laurent UFD, and compatible normalization. The generic-to-specialized coefficient issue is addressed there; generic graph finite type alone was not enough.
* 316143 and 318237: fetched pinned OpenAI primary bodies at the live HEAD, read the exact theorems and closing proofs. Under the inherited rule accepting upstream theorems, they respectively refute Borel in dimension four and provide a finite aspherical PD4 complex without a manifold model. They cannot be rediscovered here.
* 319785: Karolyi 2014 has an explicit prior-proof abstract. The publisher returned 403; its proof body remains unread. This is a novelty blocker, not a fabricated body-level review.
* 316154: the actual current Gao-Gu primary work is geometric/function-field and conditional over number fields. Secondary text implying a general unconditional number-field theorem is not reliable evidence.

## Unfinished obligations

The requested several-hour sustained pass was not fulfilled by this packet. No exact class-group sweep for 316077 was completed. Many high-dimensional geometric/topological/algebraic entries have only primary statement/context and bounded later-work screening, not a full proof-body/citation-chain investigation. Author catalogues were not exhaustively checked for all 40 entries. These are explicit incompleteness boundaries, not claims that the reservation is technically exhausted. No Lean certificate should be produced for these bounded diagnostics.
