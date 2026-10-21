# First independent correctness disposition: PASS

This is a full-scope PASS for the exact unchanged frozen theorem, not an acceptance, contribution regrade, priority certificate, formal verification, or count assignment. No material mathematical gap or needed repair was found. Every quantified input and every conclusion below is checked jointly. The separate TECHNICAL contribution disposition remains conditional until parent adoption of this review and remains TECHNICAL thereafter.

The authoritative scope has SHA256 98d8a82c64798cfeeb033fe73f708b1cea643159b8b334b4174528269d15882f; the author proof has SHA256 9a40c540418cb946d941e2764d03e5d89e50df126eada2953ac05024199a23f2. No author response, proof patch, narrowed replacement statement or added hypothesis is used. The pinned source proofs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true. I check the new composition independently rather than truth-auditing those proofs or importing the contribution review's reasoning.

## 1. Exact scope and basic rank interface

Fix ANY countably infinite ground set E, ANY finitary matroid M on E, ANY infinite M-independent T with r(M/T)=infinity, and ANY increasing finite exhaustion E_n of E. Set c_n=r_M(E_n|T), q_n(X)=c_n-r_M(E_n|X), and ell(X)=liminf q_n(X) in the extended integers. All displayed probe differences have finite summands. No subtraction of infinite ranks is used. The review concerns the particular global family I_N={X in I_M:ell(X)<=0}, not independent choices of unrelated interval families.

The actual primary interface is BDKPW v3: independence axioms in section1.1, extension/restriction and contraction proofs in section3, closure and circuit equivalence in Theorems4.2/4.3, rank existence/minor compatibility in Lemmas3.12/3.13 and finite/infinite chain rule in Theorem4.5. Gollin–Joó v1 Definition1.1 and section2.1 use the same contraction-rank convention. These justify using arbitrary restrictions, independent extensions, closure idempotence, and finite rank cancellation here.

There is no inapplicable assumption that only finite contractions of a finitary matroid are available. For arbitrary X choose a basis J of M|X. Corollary3.6 says S disjoint from X is independent in M/X exactly when J union S is M-independent (equivalently test every independent subset of X). If all finite subsets H of S are independent in M/X, then J union H is independent for each finite H. Every finite subset of J union S is therefore independent in M. Finitarity of M gives independence of J union S, and hence of S in M/X. Thus the contractions used here are indeed finitary. The usual closure lifting identity follows from the same basis-extension description: a basis C of the contraction restricted to A\X makes J union C maximal independent in X union A; Lemma3.10 then gives A subset cl_M(X union C). No representability is involved.

## 2. Finite witnesses and simultaneous supports: verified

For finite A and arbitrary, possibly dependent X, choose a basis C of (M/X)|(A\X). It has k=r(A|X) finite elements, and A subset cl(X union C). Closure has finite character: for a outside a given set, an independent witness for closure together with a contains a circuit through a, which is finite by finitarity; for a already in the set use its singleton. For each a in A retain the finite portion F_a of X in such a witness inside X union C. The union F of these F_a is finite and A subset cl(F union C). Consequently r(A|F)<=|C|=r(A|X), while contraction monotonicity gives the reverse inequality. This proves minimum attainment

    r(A|X)=min_{F finite subset X} r(A|F).

This includes X dependent, A meeting X, loops, k=0 and A empty. It is not only an infimum assertion.

Separate finite witnesses do not by themselves give one support valid on an interval. To check that stronger step, let Y be independent and extend it to a basis D. The fundamental circuit C_a of each a in A\D exists and is unique (circuit existence and elimination in the primary); it is finite. Put R=(A intersect D) union union_{a in A\D}(C_a\{a}). This is finite, lies in D, and spans A. For X subset Y, K=X intersect R is finite. For finite S subset D\R, independence of D implies r(S|R)=|S|. Since K union A subset cl(R), monotonicity forces

    r(S|K union A)=r(S|K)=|S|.

The two expansions of the finite rank r(A union S|K) give

    r(A|K)+|S|=|S|+r(A|K union S).

All terms being finite, cancellation is valid. For any finite F subset X, apply this with K'=F intersect R and S=F\R, obtaining r(A|F)=r(A|F intersect R)>=r(A|K). Minimum attainment and K subset X then give equality

    r(A|X)=r(A|X intersect R) for EVERY X subset Y.

This is the exact common-support assertion needed by the proof. It holds on every independent interval, even when A has elements outside Y and M has arbitrary finite circuits. For A=E_n write its support R_n. Each q_n on 2^Y is determined by finitely many coordinates. In a pointwise convergent sequence in 2^Y it is eventually exactly equal to the limiting probe; avoiding a finite union of supports protects all the corresponding probes exactly.

## 3. Probe calculus and all endpoint limits: verified

Contraction monotonicity gives q_n(X)<=q_n(Y) for independent X subset Y. If F is a finite subset of (Y\X) intersect E_n, the chain rule in M/X gives

    r(E_n|X)=|F|+r(E_n|X union F)>=|F|+r(E_n|Y).

Thus q_n(Y)-q_n(X)>=|F|. In particular any proper independent extension raises all sufficiently late probes by at least one; infinite extensions do not require an infinite-rank subtraction.

For an independent X+e, r(e|X)=1 and r(e|X union E_n) is zero or one. Expanding r(E_n union {e}|X) in the two orders shows that contracting e lowers r(E_n|X) by zero or one. Once e belongs to E_n the drop is exactly one. Hence q_n(X+e)=q_n(X)+1 eventually, and ell(X+e)=ell(X)+1, with the standard extended-integer conventions. Deletion reverses this. For two independent sets with finite symmetric difference, pass from their common intersection separately to each set by independent finite additions. No independence of their union is assumed. The eventual shift is number added minus number removed, so balanced changes preserve ell.

For the lower endpoint, the finite-rank chain rule through T intersect E_n and contraction monotonicity give

    r(E_n)>=|T intersect E_n|+c_n.

Thus q_n(empty)<=-|T intersect E_n| tends to minus infinity; every finite independent set has the same divergence after a constant eventual shift. For the upper endpoint, c_n increases to infinity since any finite independent set of M/T eventually lies in E_n. Every M-basis D spans E, so q_n(D)=c_n tends to plus infinity. Finally q_n(T)=0 for every n. Repetitions, empty initial E_n and arbitrary enumeration order do not affect these arguments.

## 4. Crossing: finite endpoints, opposite infinities, stopping and limit verified

Suppose independent I subset Y with ell(I)<0<ell(Y). Extended-integer liminf is either an integer or an infinity, so the following cases are exhaustive.

If a=ell(I) is finite negative, add -a elements of Y\I. If this many elements were unavailable, the gap would be finite of size h<-a and the eventual-shift identity would give ell(Y)=a+h<0, contradiction. The output has ell=0. This covers finite/finite and finite/+infinity endpoints. If ell(I)=-infinity and b=ell(Y) is finite positive, delete b gap elements. A finite gap h<b would give ell(I)=b-h>0, contradiction. The output again has ell=0. The same deletion argument works whenever b is finite; no finite/infinite endpoint is lost.

For ell(I)=-infinity, ell(Y)=+infinity, use the common supports on 2^Y and H_j=union_{n<=j}R_n. Begin X_0=Y; every finite stage differs from Y by finitely many deletions, contains I, and remains M-independent. At stage j do nothing if some n>=j already has q_n<=0. Otherwise every such probe is a positive integer. Enumerate the eligible elements (X_{j-1}\I)\H_j and delete singly until a tail probe becomes nonpositive.

This is a legitimate countable procedure with a finite stopping time at every stage, not an instruction to perform infinitely many deletions within one stage. Deleting all eligible elements would leave Z between I and I union H_j, so ell(Z)=-infinity. Choose ONE fixed n>=j with q_n(Z)<0. Its finite support R_n is reached after finitely many eligible deletions; at that finite time the probe already equals its value at Z. Hence the stopping condition is attained no later. If the eligible pool is finite or empty, this reasoning still applies; in fact that possibility at a deleting stage is ruled out by ell(X_{j-1})=+infinity and finite distance from I, but no infinite-pool assumption is needed for the stopping proof.

Immediately before the first stopping deletion all tail probes are positive integers. A single deletion lowers each by zero or one, so immediately afterwards every q_n for n>=j is nonnegative and at least one is exactly zero. The whole stage changes no q_n with n<=j because H_j was excluded. There is therefore no index-j conflict: if it was positive it stays positive, and any newly attained zero lies later.

Let X_infinity=intersection_j X_j. It is a subset of independent Y and contains I. Common finite supports prove eventual exact stabilization at every fixed probe; mere semicontinuity would not suffice here. A first deleting stage j_0 must exist: otherwise the unchanged Y would have a nonpositive probe in every tail, contrary to ell(Y)=+infinity. Fix n>=j_0. It is nonnegative after j_0. Every later stage through n either does nothing or resets the entire relevant tail to nonnegative values. Every stage j>n protects R_n and hence preserves it exactly. Thus q_n(X_infinity)>=0 for every n>=j_0.

Every stage j also leaves a witness m>=j with q_m(X_j)<=0. Later deletions can only decrease that fixed probe, and finite-support stabilization transfers its value to the limit. For j>=j_0 the already proved nonnegative limiting tail forces this witness to be zero. These witnesses are unbounded in index because m>=j. Therefore the limit has an eventually nonnegative profile with arbitrarily late zeros, and ell(X_infinity)=0. This verifies all preservation, continuity and lower-limit obligations. Neither Borel choice of witnesses nor any uniform/effective construction of all interpolants is used.

## 5. Independent sets, exact bases, augmentation and arbitrary restrictions: verified

Define I_N exactly as frozen. Empty belongs by the lower endpoint divergence. Heredity follows from q-monotonicity and M-independence. If ell(B)=0 and independent Y properly contains B, choose one e in Y\B. The gap inequality gives ell(Y)>=ell(B)+1=1, so B is globally maximal in I_N. Conversely, if I belongs to I_N and ell(I)<0, extend I to an M-basis D. Its upper limit is +infinity, and crossing supplies a proper extension B with ell(B)=0. A set with ell=0 extends to itself. Thus every N-independent set extends to a global maximal member, and the global maximal members are EXACTLY the independent zero-level sets.

The augmentation comparison has the correct direction. If a zero-level B were contained in cl_M(I), then r(A|B)>=r(A|I) for each finite A: choose a contraction basis C for A over B; A subset cl(B union C) subset cl(I union C), giving r(A|I)<=|C|. Hence q_n(B)<=q_n(I) for every n. This contradicts ell(B)=0>ell(I) when I is an N-independent nonbasis. Therefore some e in B lies outside cl_M(I); it is outside I and I+e is M-independent. The unit shift gives ell(I+e)=ell(I)+1<=0 because ell(I) is a negative integer or minus infinity. This is axiom(I3), for ANY maximal N-independent B.

For(IM), fix ANY I in I_N and ANY I subset Z subset E; Z may be M-dependent. First extend I to a maximal M-independent J inside Z using the original matroid's(IM). If ell(J)<=0, J is N-independent and any proper N-independent extension within Z would contradict its M-maximality. If ell(J)>0 and ell(I)=0, I is already globally maximal. If ell(J)>0 and ell(I)<0, crossing on the independent interval [I,J] supplies a zero-level B containing I and lying inside Z, globally maximal and therefore maximal inside Z. These cases cover all possibilities, including finite-rank restrictions where no global zero-level basis fits. No independent-ambient restriction was silently imposed.

The four infinite independence axioms consequently hold. As a cross-check, the actual Gollin–Joó Lemma3.1 conditions also follow: nonempty independent basis family (T belongs), balanced-change closure, no proper subset of one basis spans another (the same spanning inequality), and its interval alternative. For the last condition, if I lies under a zero-level basis and I subset J is independent, then ell(I)<=0. If ell(J)<=0 extend J globally to a zero-level basis; if ell(J)>0 use I itself when ell(I)=0 and crossing otherwise. This verifies compatibility of the one fixed global family rather than gluing incompatible local choices.

## 6. Full generalized truncation and all structural consequences: verified

Definition1.1(I) and(II) hold by the same ground set and I_N subset I_M. For(III), take ANY N-independent nonbasis I and ANY e outside I with I+e M-independent. The just established exact base identification gives ell(I)<0. The eventual unit shift yields ell(I+e)<=0. The e need not lie in another N-basis. This proves the FULL generalized-truncation axiom, beyond ordinary augmentation.

Every finite M-independent set has ell=-infinity, so the finite independent families agree. The finitarization of N consists of sets all of whose finite subsets are N-independent. Finitarity of M and the finite-family agreement identify this with I_M exactly. Every N-basis is infinite, since finite sets have ell=-infinity. Every N-basis B has infinite M-relative corank: if r(E|B)=k<infinity, then r(E_n|B)<=k while c_n tends to infinity, forcing q_n(B)>=c_n-k to tend to plus infinity, contradiction.

T is a zero-level N-basis, for the originally prescribed arbitrary T. An M-basis has ell=+infinity and is not N-independent, so N differs from M. For every n>=0 the n-truncation has finite n-element bases, whereas N has only infinite bases. For every k>=1 a basis of the(-k)-truncation is an M-basis with k elements deleted. Its relative corank is k, by independence and contraction over that remaining subset, whereas EVERY N-basis has infinite relative corank. Thus N differs from every integer truncation. If the zero truncation is instead interpreted as the trivial M, the already established distinction from M covers that convention too. “Wild” is used only in the generalized-truncation sense; no circuit/cocircuit wildness assertion is inferred.

For the universal existence consequence, an infinite-rank matroid on countable E has a countably infinite basis D. Split D into infinite T and U. Independence of D implies U is independent in M/T, so r(M/T)=infinity. This gives an allowed input and proves the stated existence for EVERY countable finitary infinite-rank M in ZFC. All choices used are ordinary ZFC basis extensions, enumerations and finite selections; MA and CH do not occur.

## 7. Descriptive complexity for every exhaustion: verified

Use the Cantor topology on 2^E. I_M is closed because each dependence has a finite dependent witness. The minimum-attainment fact was proved for arbitrary subsets X, so for every finite A and integer k,

    {X:r(A|X)<k}=union_{F finite, r(A|F)<k}{X:F subset X}

is open; each cylinder on the right is clopen. This is an unrestricted 2^E calculation, not a claim of global continuous rank. Consequently {r(A|X)>=k} is closed, and {r(A|X)<=k}={r(A|X)<k+1} is open. Empty/full cases for thresholds outside the possible ranks cause no difficulty.

For any integer sequence (q_n), liminf q_n<=0 is equivalent to infinitely many q_n<=0. If those indices were finite, every sufficiently late term would be at least1. Conversely infinitely many nonpositive terms force lower limit<=0, including minus infinity. Hence with closed C_n={X:r(E_n|X)>=c_n},

    I_N=I_M intersect intersection_m union_{n>=m} C_n

is Pi^0_3. Countability of E supplies the usual Cantor/Borel setting; all c_n are fixed finite constants for the arbitrary chosen T and exhaustion.

For integer sequences, liminf=0 is equivalent to eventual nonnegativity AND infinitely many nonpositive terms: eventual nonnegativity gives lower bound0, and the latter gives upper bound0. If liminf=0 then infinitely many negative integers are impossible, and infinitely many nonpositive terms are necessary. With open O_n={X:r(E_n|X)<=c_n},

    B_N=I_N intersect union_m intersection_{n>=m} O_n

is Borel. This proves the asserted upper bound on independence and Borel bases, with no optimality or exhaustion-invariance claim. There is no projection over interval choices and no Borel selector smuggled in.

## 8. Adversarial boundaries and disposition

The conditional-rank argument explicitly handles dependent contraction sets and dependent ambient restrictions, infinite circuits being excluded only by the ACTUAL finitarity assumption. Basis-coordinate transport, representability, local finiteness, finite-rank surrogates and finite samples play no role. The common support, rather than a pointwise witness alone, pays both finite stopping and the limiting preservation. Discreteness of the integer probes, rather than real-valued liminf intuition, pays exact zero identification and the Borel formulas.

Source185's stipulated local interpolation and maximality operations were read in their actual operative bodies; their truth was not inferred from abstracts. The current proof's exact-support specialization and subsequent global rank comparison were checked separately above. Bowler–Geschke's nonanalyticity result uses self-duality and does not contradict the free-matroid specialization here: the frozen theorem asserts no self-duality. Gollin–Joó's broader simultaneous-prescription/uncountable-ground MA theorem is neither assumed in ZFC nor reproduced by this statement. No excluded old target or prior role finding is a mathematical premise.

All six requested obligation groups and all frozen clauses pass together. Unresolved mathematical issues: none found within the frozen scope. Needed mathematical repairs: none. The verdict is a human-readable independent analytic review, not machine proof checking. Artifact hashes and copied integrity controls are evidence about bytes only. The parent alone may adopt this PASS; it neither overturns TECHNICAL contribution nor assigns acceptance/count or opens downstream gates.
