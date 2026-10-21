# Full-theorem contribution disposition: TECHNICAL, conditional on correctness

This disposition covers the WHOLE unchanged frozen theorem, not its free case or one support lemma. Independent correctness remains UNREVIEWED, not PASS. It is conditional on correctness of all frozen clauses together. No independent correctness gate, acceptance, or count is assigned. Parent alone integrates and counts. There are no prior independent contribution findings or author responses in this first round.

The authoritative statement is the preserved incoming notes/03-frozen-scope.md, SHA256 98d8a82c64798cfeeb033fe73f708b1cea643159b8b334b4174528269d15882f, frozen 2026-10-21T00:30:13.653780+00:00. The proof is notes/04-author-proof.md, SHA256 9a40c540418cb946d941e2764d03e5d89e50df126eada2953ac05024199a23f2. Neither was altered. All references to the source below use fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, with source statements AND operative proofs stipulated available and true.

## Scope assessed

For ANY countably infinite E, ANY finitary matroid M on E, ANY infinite M-independent T with M/T of infinite rank, and ANY increasing finite exhaustion E_n, set c_n=r_M(E_n|T), q_n(X)=c_n-r_M(E_n|X), and ell(X)=liminf q_n(X) in the extended integers. The assertion is that I_N={X in I_M:ell(X)<=0} is a matroid independence family, its bases are EXACTLY B_N={X in I_M:ell(X)=0}, and N satisfies the full generalized-truncation condition: every M-independent one-element extension of an N-independent nonbasis remains N-independent. All finite M-independent sets survive; N^fin=M; EVERY N-basis is infinite and has infinite M-relative corank; T is a basis; N differs from M and every integer truncation. I_N is Pi^0_3 and B_N is Borel in Cantor space. Maximal extension holds in EVERY ambient subset, including M-dependent ones. Splitting a countable basis gives the existence consequence for every countable finitary infinite-rank M. These are simultaneous conclusions in ZFC, without representability, local finiteness, MA or CH.

The assessment does not impose self-duality, Borel selection of interpolants, packing/covering, uncountable grounds, exhaustion independence, arbitrary simultaneous class prescription, optimal Borel rank or priority. It leaves the old r114/r118 pair obligations and other frozen/completed scopes unchanged. Source210/I198 and the author's ultrafilter/cardinality calculations are not nominees.

## Strongest actual integrated antecedents

The canonical Source185 family is preprints/A-Counterexample-to-the-Infinite-Matroid-Packing-Covering-Conjecture-September-24-2026/. The relevant proof is more than its headline. Section04, lem:probe-properties, lem:block-continuity, lem:local-antichain and lem:local-interpolation supply monotone probes with unit one-element changes, eventual finite-change shifts, finite stopping by interval continuity, a decreasing sequence, persistent tail witnesses, and control of earlier tests. Its proof explicitly treats finite endpoints and the opposite-infinite-endpoint case. Section05, prop:basis-family and thm:local-matroid, supplies full interval assembly and maximality inside arbitrary subsets. No missing stopping/limit idea is charged to the author.

The classical general-matroid interface is Gollin–Joó v1, Lemma3.1, read with its proof. Its four conditions are nonempty M-independent candidate bases, balanced finite-change invariance, no proper subset of one candidate spanning another in M, and a compatible basis alternative for independent intervals. Its sufficiency proof first maximizes in M inside an arbitrary dependent ambient set. Thus that restriction step is explicitly antecedent-paid. Their relative-rank preparation supplies the rank chain rule and strong-equivalence calculus.

Gollin–Joó Theorem4.1 has a stronger prescription: a union of fewer than continuum pairwise almost-spanning-incomparable strong-equivalence classes, on a ground set smaller than the continuum. Its actual five-claim proof schedules intervals, uses finite binary conditions and dense rank-separation demands, invokes MA to obtain a separating filter, and retains whole strong-equivalence classes. Corollary4.2 concerns many nonisomorphic truncations. The frozen theorem neither reproduces nor removes MA from that full prescription. Countability of E alone does not reduce their continuum-long history of class-separation demands to a countable MA instance.

Bowler–Geschke's author version dated 6 October 2014 supplies Theorem6's uniform criterion and Lemmas11–14/Theorem15's actual MA partition recursion. Its Theorems20/22 and Corollary24 use complement symmetry to derive a flutter and the nonanalyticity of self-dual uniform bases. This does not obstruct the frozen nonselfdual family. It also does not supply a general pullback of a free-matroid construction through circuits of M. The reduction below uses actual conditional rank instead.

Basic infinite-matroid operations were checked against Bruhn–Diestel–Kriesell–Pendavingh–Wollan, arXiv:1003.3919v3: the independent-set/closure/rank axioms; restriction/contraction and basis extension; fundamental circuits, finitarity and finite circuits; closure idempotence; and relative-rank additivity. This is the classical input to the support calculation, not a claim that a primary printed the whole frozen formula.

## Positive routine derivation of the whole theorem

The following is the reason for TECHNICAL. An absent identical printed statement, a different headline, or the failure of an arbitrary basis-coordinate pullback would not suffice.

### 1. The simultaneous support is a finite-rank calculation

Fix a finite A and an independent upper endpoint Y. Extend Y to an M-basis D. For each a in A outside D take its fundamental circuit in D+a. Finitarity makes these circuits finite. Let R be the union of their D-parts and A intersect D. Then R is finite and A is contained in cl_M(R).

For K subset R and finite S subset D minus R, independence of D gives r(S|R)=|S|. Since K union A is contained in cl(R), rank monotonicity gives r(S|K union A)=|S|=r(S|K). The finite rank chain rule, applied to A union K union S, cancels these equal terms and gives

    r(A|K union S)=r(A|K).

For arbitrary X subset Y, finite character gives

    r(A|X)=min{r(A|F): F finite subset X}.

To see attainment, take a finite basis C of the contraction restricted to A; A is spanned by X union C. Finitely many finite circuit witnesses retain a finite F subset X already spanning A together with C. Applying the preceding cancellation to each finite F subset X yields

    r(A|X)=r(A|X intersect R), simultaneously for ALL X subset Y.

This is a single finite union, not separate supports chosen at different X. The upgrade from pointwise witnesses to a common support is explicitly accounted for by independence of the ambient basis and rank cancellation. It uses no representation, local-finiteness bound, infinite elimination, compactness beyond finite character, or new separation construction. Its finite size is not required to be uniform in Y or A. This is a routine use of fundamental circuits plus finite rank additivity; it is not an unpaid theorem merely because it was not a named Source185 lemma.

Consequently q_n restricted to 2^Y is an integer-valued finite-coordinate function. A finite union of supports protects every specified initial list exactly. This supplies a stronger, simpler continuity/protection input than Source185's real-probe continuity and summable losses.

### 2. Source185 interpolation specializes with loss zero

Contraction-rank monotonicity makes q_n increasing under independent inclusion. Adding an element changes q_n by zero or one; once the element belongs to E_n the change is exactly one. A finite modification therefore eventually shifts q_n by its net cardinality, even between independent endpoints whose union is dependent (pass through their common intersection).

For independent I subset Y with ell(I)<0<ell(Y), a finite negative lower endpoint is corrected by finitely many additions; a finite positive upper endpoint by finitely many deletions. The finite-change formula guarantees enough gap elements. These are exactly the finite-endpoint rounding cases of Source185; integer probes remove its rounding interval.

For ell(I)=-infinity and ell(Y)=+infinity, use the existing source decreasing-stage algorithm. At stage j protect the union H_j of the supports of tests1 through j. If there is already a nonpositive tail test, leave the set unchanged. Otherwise delete eligible points outside I union H_j until a tail test becomes nonpositive. Removing all eligible points leaves only finitely many points above I, hence has lower limit minus infinity. A fixed negative tail test then witnesses finite stopping, because it has finite support. At the first crossing, all tail tests are nonnegative and one is zero: they are integers and each deletion decreases them by at most one.

After the first deleting stage, every later stage either does nothing or restores nonnegativity in its tail; stages past a test's index protect that test exactly. Thus the decreasing limit has an eventually nonnegative profile. Each stage leaves a nonpositive witness arbitrarily far out. Later deletions preserve its nonpositivity, while finite-coordinate continuity passes it to the limit. The preceding nonnegative bound makes these limiting witnesses zero. Hence the limit has ell=0.

The source already pays finite stopping, the first-active-stage argument, tail resetting, later-test protection, persistence of witnesses and passage to the decreasing limit. Substituting H_j for its far-block cutoff makes the error budget identically zero. Integrality turns its limiting strip into the exact zero level. This is a direct specialization of its proof architecture with the classical support calculation as input, not a new independently designed interpolation method.

### 3. The general criterion pays the global compatibility

Endpoint ranks give ell(empty)=-infinity, ell(D)=+infinity for every M-basis D, and q_n(T)=0 identically. The first follows from q_n(empty)<=-|T intersect E_n|; the second from c_n increasing to infinity. Thus T belongs to the nonempty candidate basis family F={independent B:ell(B)=0}. Every independent X with ell(X)<0 extends to F by crossing to an M-basis. If ell(X)=0 it already belongs to F. Conversely, a subset of a member of F has ell<=0. Consequently the proposed I_N equals the downward closure of F; this equality is global, not a choice made anew in each restriction.

Here is an explicit verification of all four Gollin–Joó conditions for this same F. Nonemptiness and M-independence were just established. Balanced finite changes preserve ell by the eventual net-shift identity. If K is a proper subset of B in F, choose e in B minus K. Monotonicity gives ell(K)<=ell(B-e)=-1. If K spanned another B' in F, contraction monotonicity under spanning containment would give q_n(B')<=q_n(K) for every n, contradicting ell(B')=0. This supplies the necessary spanning version of antichainness, beyond an inclusion-only free-case argument.

Finally suppose independent I subset J and I lies below an F-basis, so ell(I)<=0. If ell(J)<=0, extend J to an F-basis using the already-established global extension. If ell(J)>0 and ell(I)=0, use I. If ell(J)>0 and ell(I)<0, crossing gives an F-basis between I and J. These are exactly the alternatives in Lemma3.1(4). Its sufficiency proof therefore constructs a generalized truncation with bases precisely F, including Definition1.1(III) and maximal extension in arbitrary dependent ambient sets.

Equivalently, maximize I in M|Z to J for any I subset Z; if ell(J)<=0 use J, otherwise use I when ell(I)=0 or a crossed basis when ell(I)<0. Augmentation follows from the same spanning comparison and the unit shift. The author writes these checks directly; the actual criterion already supplies their structural organization. There is no extra requirement to synchronize independently selected interval bases. All intervals use the same fixed q_n and global F; supports and interpolants are proof witnesses only. No Borel selector or coherent family of such witnesses is claimed. This is why global compatibility adds no unpaid gluing operation in this exact scope.

### 4. Every remaining frozen clause follows routinely

Finite independent sets have ell=-infinity by finite shifts of empty. Thus the finite independent sets of N and M coincide, and finitarity gives N^fin=M. A zero-level basis cannot be finite. If its M-relative corank were finite k, r(E_n|B)<=k while c_n tends to infinity, forcing ell(B)=+infinity. Hence EVERY N-basis has infinite corank. The same endpoint calculation separates N from M. Infinite bases exclude all nonnegative finite-rank truncations; infinite relative corank excludes negative integer truncations. T is a prescribed basis because all its probes vanish. Splitting any countably infinite M-basis into two infinite parts gives the claimed universal existence consequence in ZFC.

For descriptive complexity, finite character gives r(A|X)=min over finite F subset X for arbitrary, even dependent, X. Therefore {X:r(A|X)>=k} is closed. With C_n={X:r(E_n|X)>=c_n}, integrality yields

    I_N=I_M intersect intersection_m union_(n>=m) C_n.

I_M is closed, so this is Pi^0_3. Set O_n={X:r(E_n|X)<=c_n}, which is open by the same finite witnesses. Exact bases satisfy

    B_N=I_N intersect union_m intersection_(n>=m) O_n.

An integer sequence has lower limit zero precisely when it has infinitely many nonpositive terms and is eventually nonnegative. Hence this family is Borel. Interval supports need not be chosen globally or Borelly for either formula. Every exhaustion works because only finiteness, monotonicity, and union E enter the arguments. These checks retain every descriptive assertion and universal quantifier.

## Residual operation and assessment

The residual after the strongest integration is selecting the conditional finite-rank probes and verifying their finite supports, unit shifts and spanning comparison, then plugging them into the paid interpolation/criterion framework. The finite-support calculation above explains positively why these verifications are routine. The global compatibility calculation checks the full general-matroid conditions rather than appealing to a naive free-case transfer. The Borel and wildness assertions add direct finite-character/endpoint calculations. I find no remaining genuinely nonroutine mathematical operation supporting SUBSTANTIAL for this WHOLE frozen theorem relative to the stipulated source operations and classical inputs actually read.

This does not assert that the exact formula was previously printed, that every result of Gollin–Joó follows, or that the theorem lacks interest. MA removal or stronger descriptive regularity can be consequential; those properties do not decide this contribution standard when a concrete paid derivation is available. Nor is TECHNICAL inferred from the proof being unreviewed. It is the conditional mathematical contribution assessment of the explicit integrated derivation above.

No material suspected correctness gap is identified in this contribution reading. In particular the support is simultaneous, the crossing limit retains its witnesses, the spanning inequality has the required direction, dependent restrictions enter through M-maximal extension, and the integer Borel formulas have their stated quantifiers. This is not a correctness PASS or exhaustive independent correctness audit. A later correctness gate may find an issue; this review neither repairs nor weakens frozen bytes. The disposition remains conditional on correctness of every clause together.

## Comparison and search limits

Actual source and primary versions, hashes, canonical paths, Git blobs and read extents are in 02-evidence.md and private receipts. The bounded local/web searches establish neither worldwide priority nor latest-version coverage. Original r15, r21, r114, r118 and additional genuine Source185 screens were followed. Their old uniform/connected/regular-pair targets are distinct and immutable; absence of an earlier identical construction in the searched authored originals is not used to prove substantiality or technicality. Circuit-game proofs for the old covering-pair interface, Bowler's whole habilitation, unrelated Foulkes lower proofs, and broad unrelated history were not read here. None supplies a missing premise for the positive reduction above. Read and isolation limitations remain explicit; artifact controls are byte checks, not mathematical gates or historical OS certificates.
