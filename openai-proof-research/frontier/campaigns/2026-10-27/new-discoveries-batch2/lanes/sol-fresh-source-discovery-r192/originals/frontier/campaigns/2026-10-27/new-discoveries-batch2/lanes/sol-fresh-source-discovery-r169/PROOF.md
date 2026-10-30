# Full ordinary proof of the literal row-width conjecture

Scope: Conjecture 5, printed p.17, Blanco–Golubyatnikov–Konstantinova–Maslova–Nikiforov, *Generating the symmetric group by three prefix reversals*, DMTCS 28:1 (2026), DOI 10.46298/dmtcs.16975; journal-linked arXiv:2511.16959v3. For every integer k>=2, put

    F_k(n)={m : k<m<n, <r_n,r_m,r_k>=S_n}.

Here r_q reverses the first q elements of {1,...,n} and fixes the others. We prove

    max_{n>k+1}|F_k(n)| = k+1       (k even),
                          (k+1)/2   (k odd).

There is no bound on the attaining degree n. We in fact obtain infinitely many attaining prime degrees for each k. This does not classify all triples or settle the different asymptotic counting conjecture.

Classical dependencies, credited rather than claimed as new: the Chinese remainder theorem; Dirichlet's theorem that every reduced arithmetic progression contains arbitrarily large primes; and the minimal-degree bound for a primitive permutation group H of degree n not containing A_n:

    mu(H) >= (sqrt(n)-1)/2.

The last is Babai's classical bound, explicitly stated and used in Kempe–Pyber–Shalev, arXiv:quant-ph/0607204v1, pp.2 and 11, equation (3). It is used as an established theorem, not reproved here. The original 1981 body has not been obtained; the journal bibliographic page and the later actual research body are retained. This is an ordinary mathematical proof using named classical theorems, not a self-contained derivation of those theorems or a formal certificate. Eligibility and prior-art clearance remain HOLD.

## 1. Upper bound at every degree

Let X be the simple undirected graph on {1,...,n} joining x to r_q(x) whenever different, for q in {n,m,k}. Its components are exactly the orbits of the generated group: each edge is a generator move, and every generator move stays in a component. There are at most floor(n/2)+floor(m/2)+floor(k/2) edges. Edges from distinct q cannot coincide, since their endpoint sum is q+1.

If n is odd and m+k<n-1, this edge count is at most n-2. Thus X is disconnected and the group is not S_n. Hence generation requires m>=n-k-1, leaving at most k+1 possible m.

If n is even and m+k<n, the edge count is at most n-1. If X is disconnected we are done. If it is connected, it must have exactly n-1 edges and be a tree. Color a vertex by the parity of the number of r_n-labeled edges on the unique path from a fixed root. Across an r_m- or r_k-edge the color stays the same, and across an r_n-edge it changes. Each of r_m,r_k therefore preserves the two color classes (including its fixed vertices). Since r_n has no fixed vertices, it interchanges them. Both classes are nonempty and have equal size n/2. Since n>k+1>=3, they give a nontrivial invariant block system. Thus the group is not S_n. Consequently generation at even n requires m>=n-k, leaving at most k possible m. This proves the desired upper bound when k is even.

Now let k be odd. If n is odd and m is odd, every generator preserves the parity of every position. The action is intransitive. Thus m must be even. Among the at most k+1 candidates n-k-1,...,n-1, exactly (k+1)/2 are even. If n is even and m is odd, r_m,r_k each preserve position parity while r_n interchanges the odd and even position sets. Again these two sets form a nontrivial block system. Thus m must be even here also. Among n-k,...,n-1 exactly (k-1)/2 are even. The asserted bound (k+1)/2 follows for every n.

## 2. A transitivity criterion

Write a=n-m and b=n-k. Suppose n>2k+2, 1<=a<=k+1, and gcd(a,b)=1. We prove that <r_n,r_{n-a},r_k> is transitive.

Use composition from right to left and set T=r_n r_{n-a}. For 1<=x<=n-a, T(x)=x+a. Thus all positions in each residue class modulo a are in the same group orbit. For n-a<x<=n, T(x)=n+1-x; these last a positions represent every residue modulo a, so on residue classes the orbit relation contains the reflection

    R(s)=n+1-s (mod a).

For a<=k, the positions 1,...,a lie in the support interval of r_k, so the orbit relation also contains the residue reflection S(s)=k+1-s. If a=k+1, positions 1,...,a-1 give all nonzero residues for this reflection; the missing residue 0 is fixed by S, so this conclusion still holds. For a=1 it holds trivially. These statements concern the orbit equivalence relation; T need not induce a permutation on residue classes globally.

The composite R S is translation by n-k=b modulo a. Since gcd(a,b)=1, its iterates connect all residue classes. Each class was already internally connected, so there is just one orbit.

## 3. Simultaneous attainment

Fix k. Let A={1,...,k+1} if k is even, and A={1,3,...,k} if k is odd. Its size is the desired maximum.

For each odd prime ell<=k+1 choose a residue c_ell neither 0 nor k modulo ell. This is possible because at most two of at least three residues are excluded. The Chinese remainder theorem gives a residue c modulo

    M=4 product_{odd primes ell<=k+1} ell

with c=3 mod 4 and c=c_ell mod ell. In particular gcd(c,M)=1. Dirichlet's theorem gives arbitrarily large primes p=c mod M. Choose such a p with

    p > (2k+1)^2.

For every a in A we have gcd(a,p-k)=1. Indeed every odd prime divisor ell of a is at most k+1, and p-k is nonzero modulo ell by construction. If k is even, p-k is odd, so 2 causes no obstruction either; if k is odd all members of A are odd.

For each a in A set m=p-a. Then k<m<p, and the criterion in Section 2 makes G=<r_p,r_m,r_k> transitive. A transitive group of prime degree is primitive: translates of any block partition the p points into equal-sized blocks, so a block has size 1 or p. The nonidentity element r_k moves exactly 2 floor(k/2)<=k points. If G did not contain A_p, Babai's bound would give

    k >= mu(G) >= (sqrt(p)-1)/2 > k,

a contradiction. Finally p=3 mod 4, so r_p is a product of (p-1)/2 odd-numbered transpositions and is an odd permutation. A subgroup containing A_p and an odd permutation is S_p. Thus every m=p-a with a in A belongs to F_k(p). Together with the upper bound this proves the full stated maximum. The same argument works for every sufficiently large prime in this progression, proving infinite attainment.

## Strongest objection and falsifiers

The substantive objection is that the residue-orbit criterion plus CRT/Dirichlet and the classical primitive-group bound may constitute a routine classical adaptation. This proof does not settle that eligibility judgment. Matching public prefix-reversal registry paths were found but their bodies were not available in the reused current-body packet; they are an explicit prior-art HOLD, not negative evidence. A body proving this same maximum or this simultaneous prime-attainment construction would be a decisive public-proof falsifier of novelty. A counterexample to the transitivity criterion, or a mismatch in the quoted primitive-group theorem, would falsify the mathematics. Exact bounded checks test the former, never replace its proof. No credit, acceptance, Lean or manuscript is requested by this file.
