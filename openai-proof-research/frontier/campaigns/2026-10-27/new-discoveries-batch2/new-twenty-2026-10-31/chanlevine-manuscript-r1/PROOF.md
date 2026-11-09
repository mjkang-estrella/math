# Gcd symmetry of recurrent-component sizes on a bidirected cycle

DRAFT manuscript - 3 November 2026. Prepared with AI assistance (OpenAI Codex); no human authorship or affiliation is asserted. This draft and its formal dossier are submitted for root review with zero accepted credit.



## 2. Level, weight, and the main theorem

The network level is the total chip count L(x,q)=sum_k x(k). Indeed the source level formula is cap(N)-cap(q)+s^T x (Definition 5.17); for an agent network cap(N)=0 and s=1, while Lemma 5.18(iii) gives cap(q)=0. The rotor network is an agent network and is irreducible ([CL], Section 3.6, not Section 3.5).

Assign weight 1 to a left edge and 0 to a right edge. The configuration weight in V is

    wt(x,q) = sum_k k x(k) + #{k : q(k) is left}  (mod n).

Both L and wt are invariant under firing. A move left decreases positional weight by 1 and increases rotor weight by 1; a move right does the reverse. The wrap around changes this calculation only by a multiple of n. Hence these invariants are constant on legal components. For m>=1 and i in V, write C_{n,m,i} for the unique recurrent component of level m and weight i, whose existence and uniqueness we prove in Section 3. Let r(C) denote the number of recurrent configurations in C.

Theorem 1 (network form; Conjecture 8.3 of [CL]). For every n>=3, m>=1 and i,j in Z/nZ, the components C_{n,m,i} exist uniquely, and

    gcd(n,m,i) = gcd(n,m,j)  implies  r(C_{n,m,i}) = r(C_{n,m,j}).

Here uniqueness means uniqueness of the whole component, not of its recurrent representative. The gcd is independent of the integer representative of i because gcd(n,m) divides n.

For a natural-chip configuration write q(k)=+ for right and q(k)=- for left. A facing pair is an edge (k,k+1) with q(k)=+ and q(k+1)=-. Define R_{n,m} to be the set of configurations with x(k)>=0, sum x=m, and every facing pair containing a chip. In addition, when all rotors are constant their Hamiltonian cycle must contain a chip. At positive m this last condition is automatic. Set N_{n,m}(i)=#{a in R_{n,m}:wt(a)=i}.

Theorem 2 (count form). With these definitions, r(C_{n,m,i})=N_{n,m}(i), and N_{n,m} is constant on equal-gcd fibres. No division by n or quotient by rotation enters this definition. Finiteness follows because 0<=x(k)<=m and there are only 2^n rotor states.

The source's Table 8.1 gives r(C_{n,n,i}) for 3<=n<=8 and observes near equality of the entries. Rotational symmetry already explains equality when i-j is divisible by gcd(n,m); it does not by itself prove Theorem 1. The trace calculation below supplies the additional symmetry. A worked subset of that table, together with other levels, appears in Section 7.




## 3. Recurrence, component uniqueness, and the reduction

We use the source cycle test (Theorem 7.4, equivalently its rotor special case Theorem 1.3): on a finite, locally irreducible, strongly connected agent network, recurrence is equivalent to nonnegative chips, local recurrence of q, and a chip on every directed rotor cycle. All rotor states here are locally recurrent by Section 3.6 of [CL]. The hypotheses hold for the bidirected cycle. Its directed rotor cycles are precisely facing pairs and, for constant rotors, the two Hamiltonian cycles. A directed walk that reverses direction immediately closes a two-cycle; without a reversal it traverses the entire cycle. This proves the asserted list, including n=3.

Thus the literal Definition 5.2 recurrence is exactly the test in Section 2. In particular all signed recurrent configurations are nonnegative. Their total level is positive, since a recurrent configuration has a legal first step. Their counts at fixed level are finite by the coordinate bound. The natural-chip model therefore neither loses nor duplicates any signed recurrent configuration.

For completeness, we prove uniqueness using stated source theorems, rather than citing the source's unproved phrase "one can check". Proposition 7.9 gives exactly |Tor(N)| recurrent components at each positive level. Its hypotheses are the finite, locally irreducible, strongly connected agent hypotheses already checked. By Theorem 5.25(i), and the rotor kernel K=2 Z^V and production matrix P=A/2 of Example 3.11,

    Tor(N) = Z^V_0 / (2I-A) Z^V,

where Z^V_0 consists of vectors with coordinate sum zero. This quotient has order n, as the following elementary calculation verifies without a spanning-tree enumeration. Let e_k be the standard basis and let g_k be the class of e_k-e_0. The Laplacian relations say 2g_k-g_{k-1}-g_{k+1}=0, cyclically. Starting from g_0=0, these give g_k=k g_1, and the wrap relation gives n g_1=0. The map z -> sum k z(k) modulo n annihilates every Laplacian column and sends g_1 to 1. It follows that the quotient is exactly Z/nZ, not a smaller cyclic quotient. Hence there are exactly n recurrent components at level m.

All n weights occur. For i represented by 0<=i<n, put m chips at 0 and choose left rotors at positions 1 through i, with right rotors elsewhere. The weight is i. If i=0 the rotors are constant and their Hamiltonian cycle contains 0. Otherwise the only facing pair is (0,1), which also contains 0. The cycle test proves recurrence. Lemma 5.19 makes each corresponding component recurrent. Since distinct weights cannot share a component, these n examples exhaust the n components. Each weight therefore has exactly one recurrent component.

Every recurrent state of level m and weight i lies in that component, and every recurrent state in that component has those invariants. This proves r(C_{n,m,i})=N_{n,m}(i) and completes the semantic reduction. The Lean packet proves uniqueness by a different, direct sink-normalization argument, described in Section 8.




## 4. Weighted matching expansion and transfer trace

Fix an n-th root z of unity. For m>=1 define W_m(z)=sum_{a in R_{n,m}} z^{wt(a)}, with W_0(z)=0. Exponents can use any integer lift of wt. Rotation of all chips and rotors by one vertex preserves the cycle test and adds m to the weight. Thus W_m(z)=z^m W_m(z). In particular W_m(z)=0 unless z^m=1.

Work with formal power series over C. Write g_k=1-t z^k and f_k=1/g_k. Temporarily impose only the facing-pair conditions, allowing every nonnegative chip total, and let G'(t) be the resulting weighted generating series. At level zero, a nonconstant rotor word has a right-to-left transition and hence an empty facing pair. Exactly the two constant rotor words survive; their weights are 0 and n, so each contributes 1. At positive level the facing-pair test is the complete cycle test. Therefore

    G(t) := sum_{m>=0} W_m(z)t^m = G'(t)-2.

For a fixed rotor word, its facing pairs are disjoint: a vertex cannot be both the left and the right end of facing pairs. Inclusion-exclusion over facing pairs forced to be empty gives a sum indexed by matchings M of the n-cycle. For each selected edge (k,k+1), the rotors are forced to be (+,-); their rotor weight contributes z. Every uncovered vertex has two free rotor choices, whose weighted sum is 1+z, and a free chip series f_k. Consequently

    G'(t) = sum_M (-z)^|M| (1+z)^(n-2|M|) product_{k outside V(M)} f_k.

The factor z per forced facing pair is essential. The sum includes the wrap edge (n-1,0) and both alternating perfect matchings when n is even. Multiply by D(t)=product_{k=0}^{n-1} g_k to obtain the polynomial

    H(t) = sum_M (-z)^|M| (1+z)^(n-2|M|) product_{k in V(M)} g_k.

Define the ordered two-state matrices

    X_k(t) = [[1+z, -z g_k], [g_k, 0]].

Then H(t)=Tr(X_0 X_1 ... X_{n-1}). To see this, expand the trace over all closed state words s_0,...,s_n=s_0 in {1,2}. A nonzero term has no consecutive state 2. Each transition 1->2 at k must be followed by 2->1 at k+1 and selects the matching edge (k,k+1), with weight -z g_k g_{k+1}. Every remaining transition is 1->1, with weight 1+z. Conversely each matching uniquely determines such a state word: state 2 occurs at the right endpoints of selected edges. This includes wrap excursions and the two perfect matchings. We have proved the generating identity

    G(t) = Tr(product_{k=0}^{n-1} X_k(t)) / D(t) - 2.

All denominators have constant term 1, so every division here is legitimate in formal power series. The source's master determinant (Theorem 7.11) gives a related weighted generating function, but this derivation does not require it.




## 5. The one-period trace collapse

Suppose z is primitive of order e, where e divides n, and put r=n/e. The matrices are e-periodic. With P=X_0 ... X_{e-1} the full product is P^r. The primitive-root factorization gives

    D(t)=(1-t^e)^r,       det(P)=(1-t^e)^2.

Indeed product_{k<e}(1-t z^k)=1-t^e, and det(X_k)=z g_k^2, so the product determinant has the additional factor z^e=1.

Lemma 3 (trace collapse). The period trace is

    Tr(P)=2+q_e t^e,
    q_e=0 if e is odd;   q_e=2(-1)^(e/2) if e is even.

Proof. Write p(t)=Tr(P). Each matrix entry has degree at most one, so deg p<=e. Since X_k(zt)=X_{k+1}(t), with the indices read modulo e, cyclicity of trace gives p(zt)=p(t). Its coefficient p_j therefore satisfies (z^j-1)p_j=0. Primitivity implies p_j=0 for 0<j<e.

At t=0 all matrices equal B=[[1+z,-z],[1,0]], whose characteristic polynomial is (lambda-1)(lambda-z). Thus Tr(B^e)=1+z^e=2. This remains true when z=1: triangularization, or the Cayley-Hamilton trace recurrence, counts eigenvalues with multiplicity, with no diagonalizability assumption.

The coefficient of t in X_k is z^k J, where J=[[0,z],[-1,0]] and J^2=-z I. The top coefficient of p is therefore

    p_e = z^(e(e-1)/2) Tr(J^e).

For odd e, J^e is a scalar multiple of J and has trace zero. For e=2s, the expression is 2(-1)^s z^(s(2s-1)+s)=2(-1)^s z^(2s^2)=2(-1)^s, since z^(2s)=1. This proves the formula also for e=1 and e=2. No asymptotic or numerical argument is used.

By Cayley-Hamilton, V_j=Tr(P^j) satisfies

    V_0=2, V_1=2+q_e t^e,
    V_j=(2+q_e t^e)V_{j-1}-(1-t^e)^2 V_{j-2}  (j>=2).

In particular V_r is an integer polynomial in t^e determined solely by e and r. Section 4 now yields

    sum_{m>=0} W_m(z)t^m = V_r(t)/(1-t^e)^r - 2.

Hence W_m(z) is an integer depending on z only through its order e. Denote this integer by w_{n,m}(e). It vanishes unless e divides m. This order-only property, supplied by the trace collapse, is the extra symmetry needed beyond rotation.




## 6. Fourier inversion and the arithmetic orbit

Finite Fourier inversion gives, for all residues i,

    N_{n,m}(i) = (1/n) sum_{z^n=1} z^(-i) W_m(z).

This follows by expanding W_m and using sum_{z^n=1} z^(a-i)=n when a=i in Z/nZ and zero otherwise. Order-only dependence implies invariance under multiplication of i by any unit u modulo n: substitute z -> z^u in this sum. It permutes n-th roots and preserves their orders. Rotation separately gives N(i+m)=N(i). These two invariances agree with the route used in Lean.

We give the full arithmetic orbit argument. Put d=gcd(n,m). The subgroup m(Z/nZ) consists precisely of residues divisible by d, by Bezout's identity. Thus shifts by m connect exactly residues equal modulo d. If gcd(d,i)=gcd(d,j)=g, there is a unit v modulo d with vi=j modulo d. To prove this assertion, work prime by prime. For p^a dividing d exactly, equal truncated p-valuations mean either i=j=0 modulo p^a, when take v=1, or i=p^b I and j=p^b J with b<a and I,J units modulo p^(a-b). Choose v=J/I modulo p^(a-b) and lift to a unit modulo p^a. The Chinese remainder theorem combines these choices.

Any unit v modulo d lifts to a unit u modulo n. Start with an integer representative of v and require u=v modulo d. At primes dividing n but not d choose u=1 modulo their full prime powers; these conditions are compatible by the Chinese remainder theorem. At primes dividing d any lift of v remains nonzero modulo that prime. The resulting u is coprime to n. Thus j-ui is divisible by d and is b m in Z/nZ for some integer b, which may be replaced by a nonnegative representative. Hence

    j = u i + b m  in Z/nZ.

Both operations preserve gcd(n,m,i); conversely the argument just given connects every pair with the same gcd. The count is therefore constant precisely on the required arithmetic orbits (without asserting that different orbits always have different counts). This proves Theorems 1 and 2.

An explicit alternative expression follows by grouping roots by order. Define c_e(i)=sum_{z primitive of order e} z^(-i), the Ramanujan sum. Then

    r(C_{n,m,i})=(1/n) sum_{e | gcd(n,m)} w_{n,m}(e)c_e(i).

The weights w are obtained by coefficient extraction from Section 5. The prime-power unit argument above, applied with d=e, shows c_e(i) depends only on gcd(e,i). For e|d we have gcd(e,i)=gcd(e,gcd(d,i)), giving another direct proof of the gcd conclusion. This Ramanujan-sum formula is an ordinary exposition of the result; the formal endpoint instead uses finite Fourier injectivity and the unit-plus-shift orbit. The two routes use the same order-only Fourier statement.

