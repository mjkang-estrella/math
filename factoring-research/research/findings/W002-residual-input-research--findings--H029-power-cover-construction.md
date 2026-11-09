# H029 — Power covers, actual leaves, and an input-dependent alternative

2026-10-08. **Mathematical core accepted after independent review and local specification repairs. Verified full factoring complexity improvement: NONE.**

See [independent review](H029-independent-review.md) and [coordinator disposition](H029-disposition.md). The unchanged 300-line submission remains in H029-submitted-draft.md.

The parent capacity calculation passes the checks below. The cross-base construction in Card A has an executable leaf routine, but its proposed high-order coverage/leaf tradeoff fails a restricted counting screen. Card B gives a concrete N-only divisor-hitting construction with proved coverage and cheap visited leaves, using Lehman's known theorem. Its currently specified product algorithm costs N^(1/3) times polynomial logarithms. A particular faster product primitive would suffice for N^(1/6), but no such algorithm is supplied or assumed. Thus **neither card is a surviving improved factoring algorithm**.

The independent review accepted the restricted capacity/menu deductions and Card B's padded cover, visited-leaf invariant and conditional implication. The coordinator adopted the parameter-width, pair-order, root-initialization and index-cost repairs below. Nothing here is a factoring lower bound, a heuristic GNFS improvement, or a resolution of the Umans–Wang conjectures.

## 1. Scope, inputs, and evidence

Read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md, RESEARCH_TEAM.md, research/STATE.md, all of H004-disposition.md and H004-reduction-review.md, the failed H004-prime-cover-construction.md, the deterministic portions of W001-baselines.md, and W001-dynamics.md Card 1. H027/H028 were left alone. The ownership and analytic-only restrictions in the current brief take precedence over the general loop's implementation/delegation instructions.

The two supplied hashes match the project files exactly:

- Original brief, `research/hypotheses/H029.md`: `e94f714ce7520822e8ddfb7d4431d0b3ef4159301c3cc1088682154176b3e533`.
- Parent intake, `research/findings/H029-intake.md`: `220db361b0921244d787e4b3875d63024f3e74d06aba1a91866966c9892da154`.

Exact local input snapshots and retrieved primary documents are in [H029-cover-sources](H029-cover-sources/). [H029-cover-inputs.sha256](H029-cover-inputs.sha256) identifies every snapshot byte-for-byte; [H029-cover-source-notes.md](H029-cover-source-notes.md) records URLs, provenance, and retrieval limitations. These are sources, not solver advice. No factoring calculation, finite experiment, benchmark, sweep, candidate implementation, shared check/build, package installation, Lean edit, recursive delegation, commit, publication, or scheduler was performed.

## 2. Per-claim check of the parent intake

**P1 — Domain and quantifiers: correct.** R is real with R >= 2; L is real with L >= ln 2; B is any finite set of integer bases a >= 2 satisfying ln a <= L. For each a, H_a=floor(L/ln a) >= 1. Every selected leaf must be nonzero and use distinct integer exponents in [0,H_a] with the *same* base on its two sides. Selecting fewer pairs, using a multiset, repeating leaves, or adapting the selection to N cannot increase the union of prime supports beyond all permitted pairs. The capacity conclusion applies whenever the selected union covers **every prime <= R**, even if B itself was selected using N. An empty B cannot cover these primes. There is no assertion about multiplicity in a leaf.

**P2 — Support container: correct.** After swapping x,y and discarding a sign,

    a^x-a^y = a^y(a^(x-y)-1),  1 <= x-y <= H_a.

Every prime in this integer divides

    P_a = a product_(h=1)^H_a (a^h-1).

P_a is a positive integer, including when a=2 and the h=1 factor is 1. The factor a is deliberately redundant when y=0 for every selected leaf. It is not claimed that a^y, or the complete leaf, divides P_a.

**P3 — Primorial and constants: correct.** Universal prime coverage gives the squarefree divisibility statement

    product_(p<=R) p | product_(a in B) P_a.

For t=ln a, using ln(a^h-1) <= ht,

    ln P_a <= t + t H_a(H_a+1)/2
            <= t + L^2/(2t) + L/2
            <= L^2/(2 ln 2) + 3L/2.

The last inequality uses both t >= ln 2 and t <= L. Summation proves the displayed intake inequality with exactly its constants. Duplicate bases in a hypothetical list would only weaken the bound; the stated set formulation is fine. No order estimate or prime-factor independence was used.

**P4 — The Omega conclusion: correct, with an explicit absorption.** Since L >= ln 2,

    L^2/(2 ln 2) + 3L/2 <= (2/ln 2)L^2.

Thus |B|L^2 >= (ln 2/2) theta(R). Chebyshev's accepted theta(R)=Omega(R) suffices; no prime number theorem is needed.

**P5 — Rosser–Schoenfeld alternative: correct, and valid already for R >= 17 as an inequality.** Their Corollary 1, (3.5)–(3.6), gives pi(x)>x/ln x for x>=17 and pi(x)<1.25506 x/ln x for x>1. Therefore

    theta(R) >= (ln R)/2 [pi(R)-pi(sqrt R)]
             > R/2 - 1.25506 sqrt R                 (R >= 17).

The first step counts only primes in (sqrt R,R]. The lower bound need only be positive and linear eventually; for example R>=101 makes its right side exceed R/4. The constants are not asymptotic estimates of equality. The primary PDF used in H026 was independently read at these equations and frozen here. [Rosser–Schoenfeld (1962), Corollary 1](https://doi.org/10.1215/ijm/1255631807).

**P6 — Exponent formulation: correct.** For a claimed family along unbounded R, fixed alpha,kappa>=0 and upper bounds L<=R^(alpha+o(1)), |B|<=R^(kappa+o(1)) imply |B|L^2<=R^(kappa+2alpha+o(1)). If kappa+2alpha<1 there is a fixed positive exponent gap, contradicting P4 for every sufficiently large covered scale. This also excludes an unbounded successful subsequence with those uniform bounds. Equality kappa+2alpha=1 is not ruled out. For |B|=R^o(1), height R^(1/3+o(1)) fails. The necessary inequality is kappa+2alpha>=1, not a sufficient construction law.

**P7 — Scope boundaries: correct.** This is a support capacity bound, not a runtime lower bound or an obstruction for all covers. It does not cover differences of independently based powers. It imposes no condition on a family that only hits prime divisors of its particular N. The example a=N+1, x=1,y=0 gives N, which hits those divisors and resolves none of them. Signed/rational bases, unrestricted circuits, and products of independently based powers were not analyzed. Some could admit separate extensions; none follows from this proof.

**P8 — Source and reduction qualifications: correct.** The following primary-source check is deliberately separate from P1–P7. Umans–Wang §3 has existential, infinitely-many-scale structured-cover conjectures; §5 adds prefactoring and gives its conditional integer theorem. Theorem 5.2 requires interval products for d<=N; Lemmas 5.3–5.4 print d<=R (their n). Section 6's prime progression criterion is a CRT characterization, not a cheap small-coefficient construction. Section 7 already mentions short addition sequences. None supplies an N-only constructor, dense usable scales, or the missing H004 leaf routine. The conditional 1/6 aspiration is not an established deterministic bound. [Umans–Wang v1, §§3,5–7 and Appendix A.2](https://arxiv.org/html/2511.10851v1).

## 3. The cost contract used for both cards

Write n=bitlength(N), R=floor(sqrt N). Elementary O(n)-bit arithmetic, integer square/cube roots, gcd, and exact division have a conservative O(n^3) bound using finite classical algorithms. Let Pr(n) denote the polynomial bit bound of a fixed deterministic primality algorithm. We keep that term visible. Fast monic polynomial multiplication/product/remainder trees over Z/dZ have soft-O(s M(n+log s)) bounds at degree s; no inversion of an arbitrary nonunit is permitted. Packed multiplication temporaries have O(s(n+log s)) bits, not n bits. Tree traffic and storage are included in soft-O bounds.

H004's actual recurrence is used, not independent gcds against the unchanged N at all leaves. For input D and interval I, first compute g=gcd(D,Prod(I,D)) and call Visit(g,I) only when g>1. Its invariant is d|D and d divides the ordinary integer product of its assigned interval. A support cover need not contain enough valuations to start with d=D directly. In each split, u=gcd(d,Q_left) and d/u divides Q_right by the invariant:

    T(d,I) <= Prod(d,I_left) + gcd/division/control
              + [u>1]T(u,I_left) + [d/u>1]T(d/u,I_right),
    u = gcd(d, product_(i in I_left) A_i).

At a singleton use a real Leaf. Equality u=d shortens the interval and does not certify a prime. At most n nontrivial nodes occur at a depth, and at most n nontrivial leaves occur overall, even with repeated prime support. With k leaves, uniform primitive bounds P_*,L_* give the safe envelope

    C_gen + O(n log(k+1)(P_*+n^3))
          + O(n L_* + n Pr(n) + n^4).                (C)

Envelope (C) assumes log(k+1)=O(n), as in both cards with Card A's corrected parameter range. For general lambda=ceil(log2(k+1)), retain the safe bound C_gen+O(n lambda(P_*+n^3+lambda))+O(n L_*+n Pr(n)+n^4+n lambda), and stack O(n lambda+lambda²) besides live workspaces.

Strip every recovered prime's multiplicity from **original N**. A support cover does not promise enough valuations in its product. Memory includes descriptor, live primitive workspaces, output, and O(n log(k+1)+log^2(k+1)) traversal storage. All failed branches and root products are included in (C).

A smaller power than N^(1/5) requires all dominant R-exponents below 2/5. N^(1/6) corresponds to R^(1/3), still exponential in n. The matched established full deterministic bound is Harvey–Hittmeir's N^(1/5) times logarithmic factors. [Theorem 1.1](https://arxiv.org/html/2105.11105). No heuristic GNFS comparison is inferred.

## 4. Mechanism card A — Cross-base prime exponents with order-certified leaves

**Proposed benefit.** Use genuinely different bases u,v, and the algebraic identity

    u^q-v^q = (u-v) Phi_q(u,v),
    Phi_q(u,v) = sum_(i=0)^(q-1) u^(q-1-i)v^i,

for prime q. A large q makes most prime divisors of the cyclotomic part lie in a sparse, explicitly searchable progression. This is an attempt to pay for Leaf, not to call Phi_q prime. Independent integer bases are allowed; the construction is not restricted to powers of one common base.

### A1. Finite proposed Gen and Prod

Restrict parameters to 3<=m<=R and a nonempty explicitly generated, primality-certified menu Q of s distinct primes q in [Q_0,R]. This keeps base and index bit lengths O(n); arbitrary larger m would require carrying log m through every arithmetic and index cost. The descriptor lists those q and the rule 2<=v<u<=m. Its leaves are the nonzero positive u^q-v^q. No zero filtering or hidden-factor input is needed. Parameter selection must be a specified finite N-only procedure with its cost included in C_gen, not free advice. For the chosen computable m,Q_0, a fully finite default menu constructor scans the desired integer interval and applies deterministic primality tests, at cost O(R(Pr(n)+n^3)) and O(sn) retained bits if the full interval is scanned. A shorter scan has its actual length charged. No favorable prime gap or gratis prime menu is assumed; even a hypothetical improved constructor must write/read its explicit s exponents.

Order the menu by increasing q. For each q define Tri(I) on a consecutive base interval I: split at the integer midpoint into I_0<I_1 and concatenate Tri(I_0), Tri(I_1), Rect(I_1,I_0); intervals of fewer than two bases give an empty list. Rect(U,V) is row-major, increasing u in the outer loop and v in the inner. A row-major subinterval is one partial row when its endpoints share a row; otherwise it is the first-row suffix, complete intervening rows and last-row prefix. Each is a rectangle. Cardinalities binomial(|I|,2) and |U||V| permit charged O(n)-bit index descent.

For residues r_a=a^q mod d, form F_V(X)=product_(v in V)(X-r_v) and evaluate it at r_u for u in U. Their product has the correct u^q-v^q signs. Complete triangles use recursive cross rectangles; a contiguous interval has at most two partial children per depth. Summing complete pieces and boundary rectangles over O(log m) depths costs soft-O(m) coefficient work per exponent. This uses only monic multiplication/remainder tools valid over arbitrary composite rings. Multiple exponent blocks add their costs; all decoding and residue generation are charged.

Repeated squaring costs O(log q) modular multiplications per base. Thus an available bound, for every 2<=d<=N, is

    P_* = soft-O(s m (1+log q_max) M(n+log m)).        (A-P)

The exact q-th powers have Theta(q log m) bits at the largest bases. Their exponents have only O(log q) bits. They are never expanded in this product algorithm. Residue arrays and polynomial trees use soft-O(m(n+log m)) bits per streamed exponent, plus the menu. The menu costs at least its explicit output length; writing all leaves would be vastly more expensive.

### A2. A real Leaf, including the exceptional primes

At a visited leaf d|u^q-v^q, first factor gcd(u,v) and |u-v| by ordinary trial division of integers <=m. Strip all occurrences from d of the discovered primes, and also strip the certified prime q. This costs O((sqrt m+n)n^3), safely including successful divisions and validation. It is harmless to strip listed primes not present in d.

For a remaining prime p|d, p divides neither uv nor u-v nor q. In F_p the ratio u/v has q-th power 1 but is not 1. Because q is prime it has order exactly q, so q|p-1. The exceptional p=q has already been removed.

Now test successive integers 1+jq, j>=1, up to the square root of the changing remainder, dividing out all powers when a divisor is found. All remaining prime factors occur in that list. A successful composite test would have a smaller prime factor in the same list, already stripped, so found divisors are prime. A final remainder above 1 is prime by the usual trial-division argument. Optional deterministic primality validation is covered by (C). This is a genuine complete leaf algorithm; equality gcd(d,A)=d is allowed.

A conservative uniform bound is

    L_* = O((sqrt m+n+R/q) n^3),                    (A-L)

with polynomial scratch bits and output. For a general query d not known to divide the leaf, first compute gcd(d,u^q-v^q) by modular exponentiation; its O(log q) arithmetic is added. No modular root, order oracle, cyclotomic factorization oracle, or factor database occurs.

### A3. Coverage requirement and decisive restricted screen

For every p>m dividing a leaf, necessarily

    p=q, or q | p-1, for some q in Q.                (A-hit)

Indeed p cannot divide a base or u-v. Equivalently, when q does not divide p-1 and p!=q, the q-th power map is injective on F_p and distinct bases below p cannot collide. Increasing the number of such bases without reaching p cannot change this fact.

Consider the proposed implementation regime m<R/2 and q>=Q_0 for every listed exponent, with 2<=Q_0<=R. Even granting that the small base set realizes **every** collision permitted by (A-hit), each exponent can hit at most

    1 + floor((R-1)/q) <= 1+R/Q_0

primes in (R/2,R]. The 1 allows p=q. Consequently a universal cover requires

    pi(R)-pi(R/2) <= s(1+R/Q_0),
    s = Omega(Q_0/log R).                           (A-supply)

The last estimate follows directly from Rosser–Schoenfeld Corollary 3, (3.8): pi(2x)-pi(x)>3x/(5 ln x) for real x>=20.5. Thus R>=41 gives s>3Q_0/(20 ln(R/2))>3Q_0/(20 ln R). It requires no conjecture about safe primes or progressions. This bound counts potential primes, so multiple hits and unrealizable collisions only make the actual coverage worse.

To **certify** Leaf<=R^(gamma+o(1)) via the displayed progression-search envelope, with gamma<2/5, the proposal takes Q_0>=R^(1-gamma-o(1)), besides requiring sqrt m<=R^(gamma+o(1)). But its explicit menu then needs at least

    s >= R^(1-gamma-o(1))

entries, already beyond R^gamma. This contradicts the targeted *Gen envelope* before using the slower default prime search or (A-P). It rejects this particular high-order, explicit-menu construction/leaf certificate even with free realization of all allowed collisions. It is not a lower bound on every execution of trial division, an implicit exponent-menu representation, a lower-order leaf algorithm, or cross-base covers generally.

Allowing q around R^(2/3) also raises logarithmic power height to roughly R^(2/3) log m. We allowed that larger height in this attempt because modular evaluation remains cheap; even this concession does not fix (A-supply). If instead height is forced near R^(1/3), this progression leaf certificate becomes still less favorable.

### A4. Comparison and disposition

The underlying order condition is exactly the known power-image compression condition: the q-th power map has image size (p-1)/gcd(q,p-1). The algebraic leaf routine adds honest factor recovery for this narrow construction; it does not create a new general coverage mechanism. W001-dynamics Card 1 already charges exponent menus, image generation, and simultaneous CRT collisions. Replacing prime q by lcm(1,...,B) does not fix that accounting: its bit length is Theta(B), its production is charged, and low-order components of p-1 still need a paid leaf routine. General cyclotomic decomposition only labels these components.

**Disposition:** reject the above explicit large-prime-exponent menu as an improved universal cover. A possible escape would need a different coverage law plus an algorithm for the low-order composite leaves, or an implicit menu with genuinely cheap products and generation. Neither was obtained. No further experiment is selected for this card.

## 5. Mechanism card B — N-dependent square-difference cover with small linear leaves

**Proposed benefit.** Change the coverage obligation to the actual input, and split a square-difference identity into its two linear factors before invoking H004. Unlike A_1=N, the resulting leaves are all smaller than the remaining semiprime. That size guarantee really pays for visited Leaf. Coverage comes from a known deterministic approximation theorem, rather than a power-order or smoothness assumption. The hoped-for new primitive is a product of explicitly defined integer-root expressions, computed without enumerating them.

### B1. Paid reduction of arbitrary inputs to the relevant semiprime

Use N_0 for the original input in this card, and n=bitlength(N_0). Put K_0=ceil(N_0^(1/3)). Obtain all prime divisors of N_0 at most K_0 with the simple cover A_i=i, 2<=i<=K_0. Initialize g_0=gcd(N_0,Prod(2,...,K_0;modulus N_0)) and descend only on g_0>1, preserving the divisibility invariant; do not initialize with all of N_0 at this reduced cutoff. Its interval products are computed by the standard baby-step/giant-step monic-polynomial factorial method described in H004 §5B, costing soft-O(sqrt(K_0) M(n+log K_0)) per query. Its actual leaf gcd is at most K_0 and is fully factored by trial division in O((sqrt(K_0)+n)n^3). Use only the descent and stripping parts of H004, with cost (C), then strip **all** multiplicities from N_0. Its final-prime assertion at cutoff sqrt(N_0) is not used at this smaller cutoff. This costs

    N_0^(1/6) poly(n)

bit operations, with soft-O(N_0^(1/6)n) polynomial-arithmetic workspace plus polynomial bookkeeping. It does not enumerate primes through K_0 or through R, and it is not an uncharged factor oracle. It is a known preprocessing component, not the proposed improvement.

The remainder M has no prime factor <=K_0. Since K_0^3>=N_0, it has at most two prime factors counted with multiplicity. If M=1, stop. Deterministic primality testing handles prime M; an integer square root handles M=p^2, with multiplicities recorded. Otherwise M=pq with distinct odd primes

    K_0 < p < q,  p <= sqrt M.

For bounded M<4096, ordinary trial division is a constant-size exception. In what follows M>=4096. Set K=ceil(M^(1/3)); then K<=K_0, K<sqrt M and

    p > K >= M^(1/3) > sqrt(M/(K+1)).                (B-pre)

All these choices use only the input and recovered factors. Nothing assumes the original N_0 was balanced, squarefree, or a semiprime.

### B2. Primary coverage input, with attribution

Lehman's theorem, as stated and used in Hittmeir's Theorem 2.1, assumes M is a positive odd integer, K is an integer with 1<=K<sqrt M, and M=pq for primes satisfying sqrt(M/(K+1))<p<=sqrt M. The preprocessing and (B-pre) verify every hypothesis. It supplies integers 1<=k<=K and x,y>=0 with

    x^2-y^2 = 4kM,
    0 <= x-2sqrt(kM) <= sqrt M/[4sqrt k(K+1)].       (B-Lehman)

Moreover x=ap+bq, y=|ap-bq| and k=ab for positive integers a,b. This is existing coverage, not an H029 discovery. [Hittmeir (2021), Theorem 2.1 and its attribution to Lehman (1974)](https://publications.sba-research.org/publications/042021_Hittmeir_A%20time-space%20tradeoff%20for%20Lehman%27s%20deterministic%20integer%20factorization%20method.pdf). The original Lehman publisher PDF returned HTTP 403; the retrieved primary Hittmeir paper is the checked source for the exact statement. No original-proof audit is claimed.

### B3. Explicit compressed Gen: remove irregular indexing by dyadic padding

For j=0,...,floor(log2 K), let

    l_j = 2^j,    h_j = min(2^(j+1)-1,K),
    T_j = 1 + ceil(sqrt(M/[16(K+1)^2 l_j])).

The last ceiling is computed by integer comparisons: find the smallest z with 16(K+1)^2 l_j z^2>=M, then add 1. Thus neither a floating-point boundary decision nor a modular square-root oracle is involved.

For every k in [l_j,h_j] and t in [0,T_j], define actual integers

    x_(k,t) = ceil(sqrt(4kM)) + t,
    z_(k,t) = x_(k,t)^2 - 4kM >= 0,
    y_(k,t) = floor(sqrt(z_(k,t))),
    A_(k,t,-) = x_(k,t)-y_(k,t),
    A_(k,t,+) = x_(k,t)+y_(k,t).                    (B-leaf)

Keep both signs, even if y=0 gives a duplicate. The leaves are nonzero: y<x since 4kM>0. Order by j, then k, then t, then minus/plus. The descriptor consists of M,K and O(log M) band endpoints, widths and prefix counts. A global index decodes with polynomially many n-bit operations; it does **not** require computing a table of all the floor roots.

Because T_j >= sqrt M/[4(K+1)sqrt k] for every k in that band, the x supplied by (B-Lehman) occurs among these x_(k,t). For that row, z=y^2 exactly, and its two leaves are 2ap and 2bq in some order. Consequently the cover hits **both actual prime divisors of M**. It is not asserted to cover other primes <=sqrt M.

Let V be the number of (k,t) rows; there are k_cover=2V leaves. Since T_j+1<=3+sqrt M/[4(K+1)sqrt(l_j)],

    K <= V
       <= 3K + sqrt M/[4(K+1)] sum_j (h_j-l_j+1)/sqrt(l_j)
       = O(K + sqrt(M/K))
       = O(M^(1/3)).                                (B-volume)

The geometric sum is O(sqrt K). The padding thus costs only a constant factor in this exponent and makes indexing explicit at every input size. No favorable subsequence or scale-density conjecture is used. Gen costs O(n^4) bit operations and O(n^2) descriptor bits; expanding all leaves would cost Omega(K) writes and is not Gen.

### B4. Size bounds and genuine factor recovery at every visited leaf

We have K<=2M^(1/3) and

    T_0 <= 2 + M^(1/6)/4,
    x_(k,t) <= 2sqrt(KM)+1+T_0
              <= 2sqrt(2) M^(2/3)+3+M^(1/6)/4.

Therefore, for M>=4096, every leaf satisfies

    1 <= A_(k,t,-) <= A_(k,t,+) < 8M^(2/3) < M.    (B-small)

The strict final inequality is immediate from M^(1/3)>=16. All numerators, products kM, squares, root arguments and leaf values have O(n) bits; their numerical magnitudes are not unit-cost objects. Integer square roots can be evaluated by finite binary search or Newton iteration with charged exact arithmetic.

Initialize the second descent with g_1=gcd(M,RootProduct(M,full interval,M)); the proved coverage and squarefree M imply g_1=M, with this root query still charged. In H004 descent a nontrivial visited d divides both M and its assigned leaf. Since M=pq is squarefree and the leaf is less than M, d cannot be M. It must be p or q. **Leaf computes the specified integer leaf, checks d divides it, validates d by deterministic primality testing, and returns [d].** Its cost on every possible visited leaf is O(n^3+Pr(n)), with polynomial scratch space. This is an algorithm and a proved invariant, not an assumption that an arbitrary cyclotomic or norm value is prime.

For completeness, a total version of Leaf on arbitrary d<=M first computes gcd(d,A), then uses the prime shortcut when applicable and otherwise trial-divides that gcd. This always terminates and costs O((M^(1/3)+n)n^3+Pr(n)) using (B-small). That slower fallback cannot occur on the actual descent for the preprocessed semiprime. H004 §2 explicitly permits a cost proof restricted to its visited domain. Prod below, in contrast, is supplied for **every** modulus d<=M, not merely divisors of M.

It is possible for an internal gcd to equal its whole current d, including d=M. Recursion still shortens the interval. Eventually (B-small) excludes that equality at a singleton carrying M; hence a proper split occurs. Overlaps and duplicate leaves are allowed, do not create extra prime multiplicities, and do not invalidate the H004 valuation partition. Restoring all multiplicities from N_0 and validating the complete output remain charged.

### B5. The present Prod algorithm and full unconditional cost

For any interval of leaf indices and **any integer 2<=d<=M**, decode each index, compute its two ordinary integer roots, form A exactly, reduce it modulo d, and multiply. With a conservative O(n^3) per decoded leaf, the full-interval bound is

    P_* = O((K+sqrt(M/K)) n^3) = O(M^(1/3)n^3).

It includes rows whose root argument is nonsquare, both signs, duplicate values, and all branches. It needs polynomial workspace when streamed. The program never assumes that reduction modulo d commutes with taking an integer floor root.

Together with (C), preprocessing and final checks, this gives a finite complete factoring method with

    T(N_0) <= N_0^(1/6) poly(n)
              + O(n log(k_cover+1) M^(1/3)n^3)
              + O(n Pr(n)+n^4)
            = N_0^(1/3) poly(n).                   (B-current)

The current maximum workspace is soft-O(N_0^(1/6)n)+poly(n), coming from the known preprocessing product tree; the streamed new part is polynomial-space. There is no implementation or timing evidence. This construction is slower than the matched N_0^(1/5) deterministic baseline. It is retained only because Gen, coverage and visited Leaf are concrete and the missing product has a precise output specification.

### B6. Exact missing primitive and sufficient full inequality

The unsupported primitive is:

    RootProduct(M, left, right, d)
      = product of the explicitly ordered B-leaf values
        with indices left through right, modulo d,

for all M>=4096, every valid interval, and every 2<=d<=M. M need not be semiprime for the product to be defined. Its descriptor is constructed as in B3, with no factor information. Let its proved worst-case time be P(M,n), its workspace S_P(M,n), and let all shared preparation cost C_P(M,n). Any generated floor-root table, polynomial coefficient array, parameter search and failed branch belongs in those bounds.

The sufficient full factoring inequality is

    T(N_0) <= N_0^(1/6) poly(n) + poly(n)
             + C_P(M,n)
             + O(n log(k_cover+1)(P(M,n)+n^3))
             + O(n Pr(n)).                         (B-target)

In particular, C_P+P <= M^(tau+o(1)) poly(n), uniformly at all M and d, would give the **conditional** complete bound

    T(N_0) <= N_0^(max(1/6,tau)+o(1)) poly(n).

It would improve the fixed deterministic power for tau<1/5; tau=1/6 would reach the aspiration. In R_0=floor(sqrt N_0) units the same condition is maximum exponent max(1/3,2tau)<2/5. Peak space would be bounded by soft-O(N_0^(1/6)n)+O(n^2)+S_P plus any retained preparation data. A time bound on a finite bit machine must pay for allocating and accessing that data.

**No algorithm with this product bound has been found.** The displayed implication is a research target, not an accepted new exponent or a heuristic yield law. It is stronger than merely detecting a square among the rows, because it specifies every interval and arbitrary modulus.

### B7. Why familiar shortcuts do not instantiate RootProduct

1. A compact formula for x and y computes one row in poly(n), but there are Theta(M^(1/3)) rows. A scalar product tree on those computed rows still pays for all rows. Materializing them as coefficients also pays that count. Neither supplies the required square-root saving.
2. Monic multipoint evaluation helps when a low-degree polynomial or a small pair of coordinate lists already exists. The nested floor-root expressions above have not been represented that way. Interpolating all outputs explicitly buys no gain. Short addition-sequence language is already in Umans–Wang and does not furnish a circuit for these products.
3. For a paired row, write e=z-y^2, so 0<=e<=2y. Then

       A_minus A_plus = x^2-y^2 = 4kM+e.

   For d|M that pair product can be replaced by e modulo d. More exactly, this replacement is valid when d|4kM; it is not valid for an arbitrary d<=M. A square row gives e=0. Replacing its two linear leaves by an indivisible zero with no retained decomposition lets the gcd remain M and loses the present cheap-leaf proof. Pairing is possible only with a retained row and a separately justified, paid recovery of its two factors; such a changed interface needs its own product and cost proof. The present extraction proof keeps both nonzero leaves. Small numerical e alone is not a fast all-row evaluator.
4. Searching (B-Lehman) for a square is Lehman's known task. Harvey explicitly discusses the possibility of a full square-root speedup for its N^(1/3) search. His existing N^(1/5) construction uses exponent collisions and paid target generation; replacing the missing product by that known pipeline does not lower its exponent. [Harvey, §3, Remark 3.4](https://arxiv.org/html/2010.05450). This report's distinct proposal is the particular floor-root leaf product interface with every leaf already smaller than M, not a novelty claim for square differences or the 1/6 ambition.

**Disposition:** retain as an explicitly specified, unimplemented product problem; reject any present claim of faster factoring. Compared with Card A, this route supplies actual input-dependent coverage and factor separation and has no p-1/order menu. It remains unresolved at Prod rather than at a presumed leaf oracle.

## 6. One selected followup, and the stopping boundary

Select **one proof-only followup on Card B's RootProduct**. The padded-cover and size calculations have now passed independent review, with the specification repairs recorded above. Do not select an experiment for either card.

The bounded scope is to attempt one algebraic construction for the exact RootProduct interface in B6 using the stated dyadic descriptor. A proposed result must give a finite N-only circuit/product algorithm and prove, uniformly for every 2<=d<=M, including composite moduli, and both partial and full intervals,

    C_P(M,n)+P(M,n) <= M^(1/6+o(1)) poly(n),

with its workspace and indexing charged. A fixed exponent below 1/5 would also change the deterministic baseline. A full list of Theta(M^(1/3)) roots or coefficients, a modular-root oracle, an order oracle, a prime factor lookup, or a promise applying only to d|M rejects that proposed realization immediately. In particular, a resultant formula must exhibit and charge the degree and coefficient generation; naming a resultant is insufficient. Check coverage and leaf invariants separately before promoting any product result. Failure of one realization closes only that realization.

This is a precise requested *missing proof/algorithm*, not a preregistered finite test and not an asserted construction. This round stops without executing it, running a sample, or changing a registry. An experiment is not the current next step: finite product timings cannot supply the required identity or all-modulus bound.

The narrow primitive that would change the present conclusion is therefore an inexpensive, uniform interval product for the floor-root leaves in (B-leaf). The decisive surviving limitation is that the only supplied evaluator enumerates Theta(M^(1/3)) rows. The cross-base order-menu screen is retained with its restricted quantifiers. Verified full factoring improvement remains **NONE**.
