# Family129: fixed-binary transfer is a technical consequence

Pre-freeze disposition: TECHNICAL SCREEN, not a substantial nomination. No target was frozen. The full quantified consequence below is retained. Source truths are stipulated at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb; their proof truth is not audited.

## Complete deduction

For every h>=2 there is a one-way binary NFA A_h with at most14h+2 states such that every equivalent s-state unrestricted two-way deterministic automaton satisfies

    4(2s+6)^2 >= 2^floor((h-2)/31),

and every s-state unrestricted two-way nondeterministic automaton for the complement of L(A_h) satisfies

    2s+4 >= (1/2)2^floor((h-2)/127)-1.

Thus both costs are exponential in the source-state budget over one fixed binary alphabet. Targets may have partial transitions, stays and nonaccepting infinite computations. Padding with unreachable states gives exactly n states for every sufficiently large n. These consequences import respectively the deterministic and complementation companion main theorems; the lower-bound mechanism is not new.

Here is an independently specified two-bank version of the standard alphabet-substitution operation. Put Q=A disjoint-union B with A={a_i}, B={b_i}, indices modulo h. Use six letters I,U,V,E,D,S. I is the identity relation. U cycles A forward and fixes B; V cycles B forward and fixes A. E is identity plus a_0->b_0. D is identity on B and undefined on A. S swaps the banks pointwise. For a relation R on[h], form c(R): for j=0,...,h-1, for i=0,...,h-1 append E if(-i,-j) belongs toR and I otherwise, then append U; after the inner loop append V. Finish with DS. Every code has length2h²+h+2.

Starting from X subset A, the live states after c(R) are exactly R[X] in A, with B empty. During an inner cycle, input a_x visits a_0 exactly when i=-x. E then creates a path in b_0 precisely for the selected pair(x,-j), while the input path survives. Once in B a path cannot take another cross-bank edge, so no spurious composition occurs within one relation letter. It undergoes h-j subsequent V steps and finishes at b_{-j}. All input U cycles return to the initial coordinates. D deletes input survivors, S moves the accumulated outputs to A. This proves the assertion for every subset X, including empty R and X. Induction on blocks identifies nonempty relation products with the fixed-letter language on all canonical encodings, starting from all A states and ending in A. Behavior on other words is determined by the same NFA; no promise is imposed.

Encode six letters by six distinct length-three binary words. Use a copy of every base state for each proper binary prefix of length<3: seven copies, or14h states. A full triple applies its letter transition and resets the prefix; unused triples reject. Add one initial state whose left-marker rule chooses any a_i and one accepting state reached only at the right marker from an A state with empty prefix. Ordinary moves are rightward, marker stays are allowed. This has14h+2 states and accepts the empty word. No word-length or validity promise is introduced.

The two-way pullback is a finite macro simulation. Pair the target state with the side from which an encoded block was entered. For each original relation letter and each entrance, hardwire every finite computation confined to that block until its first exit or acceptance. An exit becomes a left/right step to the adjacent original symbol with the corresponding new entrance side; acceptance enters a success state. An internal infinite computation supplies no accepting exit. For a deterministic target there is at most one outcome; a repeated internal configuration is a rejecting outcome. For a nondeterministic target keep every finite possible exit, so the same proof works. Two copies of the s states and at most four initial/marker/acceptance states suffice. The actual two endmarkers and empty input are treated separately. No internal-position memory is required because the finite response is hardwired for each large-alphabet symbol. Concatenating finite visit witnesses in either direction proves exact acceptance equivalence, even with arbitrary reentries. Time and transition-table size are unrestricted in the stipulated source model.

An s-state binary deterministic recognizer therefore pulls back to a <=2s+4-state recognizer of one-way liveness, and the deterministic source bound gives the first displayed inequality. A binary nondeterministic complement pulls back to a <=2s+4-state recognizer of relation-product emptiness, giving the second. Malformed binary words never enter the reduction, while A_h itself still recognizes a total language on all binary words. No uniform logarithmic-space separation is inferred.

## Actual comparison and decision

Yan, *Lower Bounds for Complementation of omega-Automata Via the Full Automata Technique* (LMCS2008, arXiv0802.1226), Section3 defines full-relation alphabets and equivalent-word substitution; its complete Theorem3.1 binary construction uses rotation and selective deletion. Section4.3 Lemma4.8 explicitly uses rotation/swap/copy/clear letters and tracks predecessor sets. These are direct proof-operation antecedents for the simple finite-register construction above. Yan is not claimed to prove this unrestricted two-way exponential theorem; its automata/acceptance scope differs.

A closer original public construction was located: TheoremDB R816, `twnfa-claim-fixed-binary-quadratic-transfer`, in the July2026 P2832 packet. Its actual construction and macro argument were read, not merely a search snippet. It already supplies a linear-state fixed-binary liveness decoder and constant-factor deterministic macro pullback for precisely this relation-product language. It applied the then-quadratic bound, so its consequence was quadratic. Substituting the stipulated exponential bound in that same proof pays the deterministic conclusion directly. This record is agent-reported research, not peer-reviewed validation; its induction and macro reasoning were independently checked here. Its reported computational enumeration was not replayed or adopted. The nondeterministic complement pullback uses the same finite exit relation with multiple choices, an ordinary inverse-substitution operation.

The two-bank variant is not substantial just because its state constant differs. The source introductions explicitly restrict their own claims to growing alphabets, but the full fixed-binary consequence is a short composition with existing compatible operations. No worldwide exact-duplicate theorem is asserted, and absence of an identical published headline is not novelty evidence. No adjacent alphabet/state-count/code-length variant is nominated.

## Reading limits and failures

Both full pinned introductions and the full deterministic separation.tex were read. The complementation automata.tex convention/main-proof/determinization ending was read; lower diagram/amplification bodies are authenticated stipulated inputs, not audited. All23 selected TeX/Bib/README files in these two complete-tree manuscript families are retained with Git-blob and SHA256 identities; this does not assert full semantic reading of all23.

Actual primary reads: Yan extracted260–445 and680–765, including the complete cited substitution proofs. Pighizzini was only consulted at search hits and the final minicomplexity discussion, not read in full. The complete R816 mathematical decoder and macro description was read via its original record and P2832 lines210–227; the public packet identifies it as reported evidence. Direct urllib retrieval of R816 failed HTTP403 and a subsequent web open returned InternalError; these are preserved as access failures. A successful web response for P2832 retaining the complete construction is saved, not passed off as an original full HTML/PDF body.

A focused canonical Markdown history search found no developed family129 target, but a later broad JSON search produced a severely truncated inherited-task dump and is not credited as complete reading. Since the route is technical before freeze, no positive eligibility certificate is asserted. Source and primary retrieval identity is not a mathematical proof or independent gate.

## New finite controls

check_129.py independently executes all relation/subset combinations at h=2,3 (4,160 cases), verifies 528 binary code roundtrips, and detects three deliberately false variants. finite-checks.json records exact counts and witnesses. This newly executed check is separate from TheoremDB’s unreplayed reported enumeration. The universal proof above does not rely on finite enumeration.
