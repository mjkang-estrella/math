# Rational definite summation: two mechanisms, unresolved

No discovery, no full proof, no counterexample. This is a research hold, with a significant tractability objection. It must not enter formalization or receive credit. The initial rhombus candidate was retired after reading its full-scope public successor; the one pivot was to rational definite summation.

## Literal target

Mark van Hoeij, arXiv:math/0210158v1, pp1–2, unnumbered Conjecture. Let C be any characteristic-zero field. Write a nonzero F in C(n,k) as its polynomial part Q in C(n)[k] plus partial fractions A_j/B_j^{d_j}, with B_j irreducible over C(n), deg_k A_j < deg_k B_j and d_j positive integers. Two terms are equivalent exactly when their d_j agree and B_i(ak+bn+c)=s(n)B_j(k) for some a,b,c in Q, a nonzero, and s in C(n) nonzero. Let G_i be the sum of the terms in one equivalence class. Assume F(n,k) has no singularity at k=0,...,n for all sufficiently large nonnegative integers n. If S_F(n)=sum_{k=0}^n F(n,k) agrees with a rational function of n wherever both are defined, must every S_{G_i} do so?

The field, the equality of pole multiplicities, and the restricted rational affine changes are essential. Changing to arbitrary n-dependent affine transformations would change the question. Partial fractions may introduce exceptional n; after discarding finitely many n, this creates no new ambiguity about rational-sequence equality.

Closest actual proof read: Tsarev, arXiv:cs/0407059v1 (24 July 2004), all seven pages. Its interval is 0,...,n-1; shifting the upper endpoint changes the source sum by F(n,n), a rational function and similarly for each block, so this convention is harmless. The paper's §4 gives a complex-variable pole argument; §5 applies Carlson uniqueness to roots alpha(n) with growth n^epsilon, epsilon<1. §6 discusses extending this to epsilon<=1 by rearrangements, but explicitly says the general case is untreated. This is not a full resolution. The two bounded current arXiv queries found this successor and no later same-title/topic resolution. They do not establish complete citation coverage or current registry clearance.

## Mechanism A: meromorphic identities and uniqueness from integers

For a pole alpha(n) and integer d>=1, define the normalized polygamma P_{d-1}(z)=(-1)^{d-1}/(d-1)! times the (d-1)st derivative of the ordinary digamma. Its shift identity is P_{d-1}(z+1)-P_{d-1}(z)=z^{-d}. Thus, as a meromorphic identity,

sum_{k=0}^n (k-alpha(n))^{-d}=P_{d-1}(n+1-alpha(n))-P_{d-1}(-alpha(n)).

Over an algebraic splitting field, this expresses every source block in finitely many polygamma terms with algebraic arguments and coefficients. It is a representation, not proof of independence between the original irreducible blocks. Descent back from split roots must preserve the original C(n)-irreducible classes; simply grouping individual algebraic roots would be insufficient.

The known affine identities respect d. Reflection gives S_d(alpha)=(-1)^d S_d(n-alpha). For the dilation identity, partition the integer interval [0,2n+1] into the two consecutive intervals [0,n], [n+1,2n+1], and independently into its even and odd indices. For every denominator polynomial B for which the expressions exist,

sum_{k=0}^n [1/B(n,k)^d + 1/B(n,k+n+1)^d - 1/B(n,2k)^d - 1/B(n,2k+1)^d]=0.

This is an exact all-n identity by two partitions of the same index set. All four denominators are in one source equivalence class, and all four powers are d. It cannot generate cancellation between different source classes. This recovers the source's generic example without treating a known identity as a discovery.

The obstacle is conversion of a rational identity only on integer n to one on complex n. Tsarev removes poles using products of sine factors, then obtains subexponential growth in the slow-root regime. A root alpha(n)=-n^2-1 already lies outside that regime although its denominator k+n^2+1 is perfectly nonsingular on the source summation domain. Clearing its continued polygamma poles with sin(pi alpha(z)) has order two: on z=re^{i*pi/4}, |sin(pi(-z^2-1))| grows as exp(pi*r^2)/2. No Carlson bound exp(tau|z|), tau<pi, follows from this construction. The nonzero entire function sin(pi z), vanishing on every integer, demonstrates why integer equality alone cannot replace the growth hypothesis.

Taking a dth derivative or rearranging finitely many affine blocks does not reduce n^2 growth to sublinear growth: alpha transforms to A*alpha+B*n+D with nonzero constant A. Its quadratic leading term remains. An unproved assumption that such poles can be ignored is precisely an omitted general case, not a solution.

Decisive missing analytic lemma: for the finite polygamma combinations arising from rational F, integer rationality forces a complex meromorphic identity after class-preserving affine reflection/multiplication/shift reductions, even when algebraic pole functions have arbitrary growth. Such a lemma needs a replacement uniqueness theorem or an additional rigidity constraint. It is stronger than the body-read slow-denominator theorem; it is not asserted here.

## Mechanism B: arithmetic denominator isolation

Work first over Q, so integer specializations have exact valuations. The source's own §3 proves that the reciprocal sum over the disjoint triangular intervals [n(n+1)/2,n(n+1)/2+n] is not P-recursive by isolating prime denominators, then using the prime number theorem. This already-known result is evidence for the arithmetic route, not new credit. Its intervals partition the positive integers. General source denominator values do not have this property.

Here is the exact local calculation needed before any prime search. Suppose p is a prime, all coefficients are p-integral at n=N, and among all evaluated denominator factors in all summands there is exactly one pair (j,k0) for which p divides B_j(N,k0). Suppose also that p does not divide A_j(N,k0), and let e=v_p(B_j(N,k0))>0. The corresponding summand has valuation -d_j*e; every other summand and Q(N,k) is p-integral. The ultrametric inequality, with a unique least valuation, gives v_p(S_F(N))=-d_j*e. This calculation is exact and permits arbitrary multiplicity. It fails if a second summand has the same least valuation; same-class cancellation is often designed to do exactly that.

If S_F=P(n)/H(n) were rational, a prime isolated this way but not dividing H(N) would contradict integrality. Therefore the proposed global strategy must isolate denominators outside all candidate rational denominators, modulo the legitimate internal cancellations of a class. Mere existence of infinitely many prime factors of polynomial values is inadequate: those primes may divide another class, the proposed H(N), or several k-values whose leading residues cancel. Pairwise non-equivalence under rational affine changes does not by itself prove such an isolation statement.

There is also a full-source field obstruction to this route. C is not restricted to Q or a number field. Only finitely many coefficients occur, so one may reduce to a finitely generated coefficient subfield K; but uniform specialization of integer rationality and nonrationality of a block is not automatic. A proof confined to integral coefficients would resolve a strict subdomain unless a descent/specialization theorem is supplied. No such theorem has been proved here.

Decisive missing arithmetic lemma: after quotienting by the explicitly allowed internal affine cancellations, any nonrational block in a putative rational total admits a valuation/specialization isolating a nonzero principal part from the other blocks and from the candidate rational total. This is a sufficient mechanism, not an established theorem. Already for superlinear linear-in-k denominators, the source's disjoint-interval prime-density proof does not supply it.

## Exact unresolved endpoint and research disposition

Let Seq_C be eventual C-valued sequences and Rat_C its subspace of rational-function sequences. The source polynomial part maps into Rat_C by Faulhaber. The precise remaining universal lemma is that the images in Seq_C/Rat_C of the distinct partial-fraction classes have a direct sum: if a finite sum of class images is zero, each class image is zero. This is an equivalent reformulation of the source conjecture, deliberately identified as such; it is not a reduction of its difficulty. Neither analytic continuation nor prime isolation establishes it in full scope.

The two mechanisms expose different missing information: analytic uniqueness beyond slow algebraic poles versus arithmetic isolation after internal cancellation. Fifty exact rational checks of reflection (d=1..4) and block splitting (a quadratic pole) validate implementation and signs only. They cannot decide the universal endpoint. No expensive finite search was substituted for mathematics.

Rank 1 only as an incomplete research hold. Novelty and substantive gates remain closed: no full proof/refutation, no live public-registry head, no exhaustive historical citation coverage, no demonstrated nonroutine resolution. Given the breadth of the missing lemma and lack of a new rigidity mechanism, park this question after this two-route analysis rather than turn it into a long finite-testing project. A future assignment should reopen it only with a specific new uniqueness or valuation theorem.
