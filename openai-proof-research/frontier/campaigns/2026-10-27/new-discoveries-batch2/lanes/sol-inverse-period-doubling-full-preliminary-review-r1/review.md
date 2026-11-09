# Independent preliminary review: inverse period-doubling zero enumeration

Recommendation: **HOLD for campaign acceptance; ordinary full-scope mathematics PASS.** I independently reconstructed the argument and found no mathematical gap. This is the assertion for every integer k≥2, not merely base 2. Novelty clearance and a literal formal endpoint remain outstanding. Counts stay 9 additional / 39 total / next 40. Root alone decides credit.

| Gate | Finding | Exact reason |
|---|---|---|
| SOURCE | PASS | Actual JIS body, Table 1, Propositions 3, 10, 16 and Problem 27 match the definitions and full endpoint. Item 15 is **Definition 15**, with its following language description, not “Proposition 15.” |
| MATH | PASS | Independent suffix recurrence, first-threshold proof, synchronized-language construction and pumping work; Durand Theorem 16 supplies the non-power-of-two bases with its actual hypotheses met. |
| SUBSTANTIVE | PASS, preliminary only | The exact first-threshold extraction is a genuine additional argument; no inspected classical theorem supplies it. The standard logic and pumping machinery is credited background. No separate credit for those tools or other-base reduction. |
| NOVELTY | HOLD | No complete same-object subsumer found in the inspected bodies, but current registry heads/history and a sufficiently broad citing corpus are not cleared. Empty/irrelevant searches prove nothing. |
| FORMALFEASIBILITY | HOLD | Existing DFA/pumping support is useful; full regular-sequence, synchronized arithmetic and nonprimitive substitution bridges have not been supplied formally. No Lean run or formal endpoint was requested or produced. |

## Frozen target and provenance

Reviewed r242 PROOF.md and selected r240 inherited inputs only after freeze.py copied and checked their originals and copies. bindings.json records exact paths and SHA256 values. Scientific originals and copies are rechecked by a separate final guarded verifier; administrative files are point-in-time snapshots only. No recursive historical trees were copied. r242's candidate checker was frozen for provenance but was neither imported nor used as mathematical evidence.

Attribution: the parent dispatch identifies root's first-threshold/pumping suggestion; r240 records the formula as observed with missing proofs, and r242 provides the actual all-t proof and pumping argument. This review does not reattribute those contributions to itself. The reviewer independently reconstructed the reasoning below and wrote independent.py. There is no inference that the r240 finite observations alone were a proof.

## Literal source and indexing

The actual journal PDF is Rampersad–Stipulanti, *The Formal Inverse of the Period-Doubling Sequence*, JIS 21 (2018), Article 18.9.1, https://cs.uwaterloo.ca/journals/JIS/VOL21/Stipulanti/stip8.pdf. Its Section 4 defines D(U(X))=U(D(X))=X over F₂. Proposition 10 (p9) has u₀=0,u₁=1,u₂ₙ=0, u₄ₙ₊₁=u₂ₙ₋₁ for n≥1, and u₄ₙ₊₃=uₙ. Thus this is compositional inversion, not reversing or complementing the word. Definition 15/p13 defines a as the increasing ONE positions. Problem 27/p20 defines b as the increasing ZERO positions, beginning 0,2,3,4,6,8,9,… and asks for some k≥2. Corollary 26 already excludes all k for a; that does not answer Problem 27.

Table 1/p14 is literally 1→(8,2), 2→(3,4), 3→(5,6), 4→(3,2), 5→(3,5), 6→(8,7), 7→(8,6), 8→(8,8), finals {2,6}. The surrounding proof explicitly says this determinized automaton reads MSB first. Figure 2's LSD convention must not be transferred to Table 1. The language following Definition 15 is (11)*1 ∪ 1(1|00)*0(11)*1. The table and this language agree with the candidate.

Replacing the initial state by S→(S,2) preserves every positive canonical representation and gives output 0 on all-zero words, including index zero. Iterating the associated uniform substitution on S lists the states reached on **all padded length-m words in numeric order**, so positions below 2^m are neither dropped nor shifted. This is the key leading-zero justification.

Every one is isolated because every even index is zero. The zero at aⱼ−1 has exactly aⱼ−j−1 earlier zero positions, so g=Δb takes value 2 exactly at cⱼ=aⱼ−j−1. The sequence c is strictly increasing: a-gaps are at least 2 and hence c-gaps at least 1. Other g-values are 1. A pair (0,u₂ₙ₊₁) contributes 11 or 2 respectively to the ordered gap word, starting with the gap from b₀=0. The second child is final exactly for states S,3,4,7. Consequently H maps those four states to 2 and states 2,5,6,8 to 11. This is a nonerasing morphism, not a coding or an automaticity closure claim.

## Independent all-level endpoint derivation

Let p=2^t. Store each nonempty suffix set as (minimum,maximum,count). The recurrence from the literal table is the disjoint **ordered** concatenation A_q(t+1)=A_left(t) ∪ (p+A_right(t)). Emptiness is part of the data. At t=3 the sets for S,2,3,4,5,6,7,8 are {1,5,7},{5},{1,7},{5,7},{5},∅,{7},∅. I reconstructed this table:

| state | t even | t odd |
|---|---|---|
| S | (1,p−3,F(t+1)−1) | (1,p−1,F(t+1)) |
| 2 | (1,p−1,F(t)+1) | (5,p−3,F(t)−1) |
| 3 | (5,p/2−3,F(t−1)−1) | (1,p−1,F(t−1)+1) |
| 4 | (1,p−3,F(t)) | (5,p−1,F(t)) |
| 5 | (1,p−3,F(t)) | (5,p−3,F(t)−1) |
| 6 | (p−1,p−1,1) | ∅ |
| 7 | ∅ | (p−1,p−1,1) |
| 8 | ∅ | ∅ |

Here F(0)=0,F(1)=1. This is valid for all t≥3; the even column first applies at t=4. To verify the simultaneous induction, for each row use its children (S,2),(3,4),(5,6),(3,2),(3,5),(8,7),(8,6),(8,8). Min takes the first nonempty child; max takes the last nonempty child, adding p only for the right child. Counts add. For odd→even the counts in the first five rows become F(t+2)−1,F(t+1)+1,F(t)−1,F(t+1),F(t+1); for even→odd they become F(t+2),F(t+1)−1,F(t)+1,F(t+1),F(t+1)−1. These are precisely the next columns. States 6 and 7 swap emptiness/singleton. Extrema follow by the same ordered-union rule: for example 3's absent right child at odd t yields max p−3 at the next even level, whereas its right singleton at even t yields 2p−1 at the next odd level. This verifies the parity and empty-state cases, not an observed extrapolation.

The first eight p-block states are σ³(S)=S2345632. All first five blocks are nonempty. Their final accepted index is A=5p−3. Internal consecutive a-gaps are ≤p−1. Computing the four boundary gaps directly from the table gives (6,4,6,6) for odd t, and (4,6,p/2+4,4) for even t. The latter is ≤p because even t≥4; odd t=3 already works. There is no earlier initial gap to check: a₀=1 lies in the S-block and these five blocks cover every index up through A. Thus **every** consecutive a-gap starting before A is ≤p.

The next block, state 6, is a singleton at 6p−1 for even t, and empty for odd t. In the odd case the following state 3 starts at 6p+1. Thus the next accepted index B is exactly 6p−1 or 6p+1, respectively. The first five counts sum to 2F(t+2)−1 in either parity. Hence A has rank J=2F(t+2)−2. Subtracting ranks gives

    c_J = A−J−1 = 5·2^t−2F(t+2)−2 = C_t,
    c_(J+1)−c_J = 2^t+1 (even t), 2^t+3 (odd t).

All earlier c-gaps are ≤p−1. This proves exactly the FIRST gap strictly greater than p. It neither needs nor asserts a complete classification of intervening record gaps. Base checks reconstructed directly: t=3 gives A=37,B=49,J=8,C=28,gap=11; t=4 gives A=77,B=95,J=14,C=62,gap=17.

## Recognizability and pumping: adversarial checks

Assume g 2-automatic and let E(n) mean g(n)=2. Next(x,y) requires E(x),E(y),x<y and absence of E strictly between them. Large(p,x) is ∃y Next(x,y)∧x+p<y. First(p,x) adds absence of Large(p,z) for z<x. All variables range over nonnegative integers; these strict inequalities agree with the threshold above. Addition by a fixed integer and multiplication by 5 are Presburger relations. Restrict p's MSB representation to 10^t,t≥3. The formula ∃x First(p,x)∧x+d+2=5p now defines exactly (p,d)=(2^t,2F(t+2)).

I read Charlier–Rampersad–Shallit, arXiv:1102.3698v2, Section 2 pp3–4, actual body https://arxiv.org/pdf/1102.3698. Its Theorem 1 is worded as decidability; relying solely on that conclusion would be insufficient. But the preceding construction explicitly builds automata for free-variable tuples using arithmetic, lookup, nondeterministic existential choice and complement. Their tuple convention explicitly permits extra all-zero columns and reversed representations. Independently: LSD addition is a finite carry machine, order has a finite-state comparison machine, and lookup is a DFAO after reversal if necessary. Boolean closure follows by products and determinization. Existential projection permits a witness longer than the visible tuple: first project the padded language, then close under deleting/adding terminal all-zero columns. This is regular right quotient by 0* followed by multiplication by 0*. Complement is relative to the universe of padded tuples, not just one length's incomplete guesses. This prevents the hidden witness-length problem. Reversing the entire tuple word produces MSB synchronous encoding; intersecting with canonical p and minimally padded tuples is regular. No variable exponentiation is introduced into the formula.

For d_t=2F(t+2), d_t is strictly increasing for t≥3, unbounded, and d_t/2^t→0 by F(n)≤φ^(n−1), φ<2. Thus the difference of bitlengths tends to infinity. Although at small t the output can be longer than the input, the proof chooses sufficiently large t, when the input is the longer coordinate. The minimal padded word begins (1,0), then an arbitrarily long (0,0) run. In a Q-state DFA, take Q+1 states along that run, locate equal states, and repeat the intervening nonempty segment. Its length r>0 increases the first integer to 2^(t+r). The output integer stays d_t: insertion occurs entirely inside its leading zeros. The suffix, including all significant output bits, is untouched; canonical input and minimal equal-length padding remain valid. This contradicts d_(t+r)>d_t. No reset, global left-padding pump, or changed output alignment is assumed. Therefore g is not 2-automatic.

## All other bases: exact scope

Proposition 3 supplies Δ-closure, finite-valued regular⇔automatic, and base-power equivalence. Therefore b k-regular forces g k-automatic; k=2^r is excluded by the binary result.

I read Durand, arXiv:1010.4009v1 (2010-10-19), Definition 2/p5, Theorem 5 and Corollary 6/p6, Sections 3.1–3.4 pp7–11, and Theorem 16/p11, actual body https://arxiv.org/pdf/1010.4009. Definition 2 requires all letters to occur, a prolongable substitution, dominant eigenvalue α and a coding. Theorem 16 then explicitly permits **nonerasing morphisms of α- and β-substitutive words**, with α,β multiplicatively independent Perron numbers. It imposes no primitive-substitution restriction. Theorem 9's growing/purely-substitutive hypotheses should not be mistaken for Theorem 16's scope; Corollary 6 and Theorem 1 are its actual bridge.

Here w itself is 2-substitutive by identity coding: S is prolongable, every letter is reachable and occurs, and each substitution column has sum 2. A nonnegative matrix with constant column sum 2 has spectral radius 2 (the norm upper bound and eigenvalue 2 coincide). All letters grow exactly as 2^n, despite the substitution being nonprimitive and S occurring only once. Occurring once meets Definition 2. For a k-automatic g, use the usual leading-zero-invariant DFAO, make it prolongable on a start state, and retain reachable states. This gives a k-uniform fixed point, all retained letters occur, and dominant eigenvalue k. Its coding is nonerasing. H is nonerasing too. Integers 2,k≥2 are Perron; an equality 2^a=k^b with positive a,b forces k a power of 2 by prime factorization. Thus Theorem 16 applies to every remaining k and would make g ultimately periodic.

The exceptional set {c_j} is infinite and density zero. Indeed all-1 odd-length words give infinitely many a's; the suffix count for S is O(φ^m) below 2^m. Bounds between dyadic endpoints give density zero on all prefixes, so j/a_j→0. Then c_j/a_j→1 and (j+1)/c_j→0. An infinite ultimately periodic set contains a tail arithmetic progression and has positive density. Contradiction. This completes the **full** endpoint. No stronger complement-enumeration closure has been assumed.

The current arXiv metadata still lists Durand v1, and a fresh retrieval of the current PDF has the identical SHA256 to the frozen v1. No correction was found in that bounded check. This is not a claim that all later corrigenda or every cited proof has been audited. The journal citation is JEMS 13 (2011), 1799–1814; the separately published journal body was not newly acquired here. The precise original proof body and hypotheses actually used were read.

## Closest-body and current-status limits

Merta arXiv:1803.00292v1, https://arxiv.org/pdf/1803.00292, Sections 2 and 6 were read, including Theorems 2.4–2.6 and their proof: the one-position enumeration reduces mod 2 to the Fibonacci word. Theorems 4.13 and 5.20 concern zero enumerations of different formal inverse variations, with explicit affine/derived-word bridges; they do not state this target. Crucially **Problem 6.1 itself leaves the Baum–Sweet ZERO enumeration open** and discusses why the naive irrational-frequency argument fails; Remark 6.2 gives a morphic parity presentation, not its automaticity or nonautomaticity. This reinforces the need to distinguish one positions from complement enumeration. JIS Remark 28's u_(2n+1)=bs_(n+1) transfers the known one-enumeration result only.

Merta arXiv:1810.03533v3, https://arxiv.org/pdf/1810.03533, actual published DMTCS 22:1 (2020) #15 body, introduction and theorem inventory/scope were inspected. It studies generalized Thue–Morse and modified Rudin–Shapiro inverses, not a new proof of JIS Problem 27. Its later publication date is not alone evidence of resolving the earlier question.

The classical logical construction is a complete standard bridge **once the first-threshold identity is known**; it does not establish that identity. Durand only handles multiplicatively independent bases and cannot settle base 2. Thus I see no basis for EXCLUDE merely because the final pumping step is short. The new mathematical content is modest and explicit: extracting the exact first long-gap location with Fibonacci displacement and excluding its synchronized graph. A published equivalent first-threshold identity or general theorem already proving this same nonautomatic image could change the substantive/novelty decision. No such complete subsumer was located in these bodies.

Fresh guarded metadata retrieval at 2026-10-30 11:40 UTC identifies target 1807.11899v1, original 2018-07-31; Durand v1; logic v2 updated 2011-10-13; Merta Baum–Sweet v1, 2018-03-01; generalized-inverse v3 updated 2020-04-30 and published May 2020. The target journal body is dated 2018-12-05. The exact phrase search returned two irrelevant dynamics/biology hits, missing even the target; it is explicitly a poor search, not novelty clearance. All responses and hashes are in current-retrieval.json and frozen-current. Existing r240/r242 bounded searches are retained as immutable references, not promoted into independent comprehensive checks.

No current public proof-registry head or exact repository history/alias interval was retrieved: inherited GitHub API/raw/codeload/diff/patch denials remain parked. ScienceDirect, Google challenge routes, failed author-hostname paths and historical intervals were not retried. No browser, proxy or TLS bypass was used. The 2017 Merta thesis mentioned by the later body and a complete current citing corpus remain unread. These are material NOVELTY HOLD limitations, not presumed clearance or presumed prior resolution.

## Formal feasibility and diagnostics

Read-only local assessment froze five selected files from the campaign's mathlib installation before reading them. library-assessment.json records the bounded Computability inventory and declarations. DFA.lean has evalFrom_split, evalFrom_of_pow and pumping_lemma, plus regular complement/intersection; NFA and language machinery support the elementary language work. No automatic-sequence, k-regular-sequence, synchronized Presburger interpretation or Durand endpoint was identified in this selected scope; no global library-absence claim is made. The local manifest names mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612; no Git operation verified its current checkout.

The finite-state table/count induction and loop pump look tractable. The large obligations are the actual k-kernel/regularity definitions and closure, numeric convolution with padding/projection, and especially Durand's nonprimitive substitution theorem (return words, growth, and Cobham-type machinery). They cannot be hidden behind axiom interfaces while claiming a literal full-source Lean endpoint. Base 2 formalization alone would not meet the all-base source claim. Formal investment therefore remains HOLD pending an honest dependency plan. No Lean invocation or file was created or changed.

independent.py uses Proposition 10's scalar recurrences independently of the automaton and checks equality with literal Table 1 for 0≤n<524288. It separately builds the uniform fixed point, H-image and compressed exceptional positions; computes suffix min/max/count recursively to t=100; and checks first-threshold/rank/next-accepted formulas for t=3,…,16 by searching all preceding finite gaps. independent-result.json records exact results. These checks are diagnostic; the infinite proof is the induction and language argument above. The run succeeded under the prescribed guard, sampled group RSS about 52 MB, no raised caps. Candidate checkers were not run.

## Disposition

No scientific correction is required for the proposed ordinary full-scope proof. Correct the minor “Proposition 15” label when editing is authorized. Preserve all attribution and the distinction between r240 observations and r242 proof. Continue only with root's novelty adjudication and a realistic full-endpoint formal dependency assessment; this report grants neither acceptance nor a discovery count.
