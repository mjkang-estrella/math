# Family129: fixed-binary transfer is technical support, not a nominee

Author: Myeongjin Kang, no affiliation. Original prose CC BY4.0. Source truth at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is stipulated. This is an author-side deduction and contribution screen, without independent proof/contribution review.

LATE HISTORY CORRECTION: `../fresh-structural-discovery-r31/screen-129.md` already develops a stronger fixed-binary transfer (14h+2 source states and constant-factor macro pullback). It was located after the initial narrower keyword search missed its notation. The derivation below is retained as redundant work, not a fresh candidate or a new technical result. No further129 development is authorized in this lane.

The fixed-binary statement in `original-scope.txt` follows from a direct finite-control encoding. It does not require a new matching-diagram rank amplification or a new nondeterministic path-diagram obstruction. Those exponential mechanisms remain the source's work. The proof below is explicit to distinguish a valid technical transfer from an unsupported novelty claim.

## Source contracts

For h>=2 let OWL_h consist of words of binary relations on[h] with nonempty product, including the empty word. The deterministic companion's `introduction.tex`, Theorem `thm:main`, gives

    4(t+2)^2 >= 2^floor((h-2)/31)

for every t-state equivalent unrestricted2DFA. Its `separation.tex`, `prop:small-nfa` and `lem:syntactic-quotient`, give the h+3-state no-left-move recognizer and singleton-context quotient onto the full relation monoid. The matching-diagram amplification is an upstream premise, not new work here.

The complementation manuscript's `introduction.tex`, Theorem `main:theorem`, with n=h+2 gives

    t >= (1/2)2^floor((h-2)/127)-1

for every2NFA recognizing the complement of OWL_h. Both statements allow arbitrary finite input length, partial rules, one read-only head, endmarkers, stay moves and nonaccepting infinite computations. No writable tape, advice or random bits are allowed. The deterministic bound also covers the positive-transition acceptance convention. The coding construction below accepts after a positive transition and therefore works with either convention.

## A linear-state source for unary endpoint lists

Use alphabet Gamma={a,b,c,d}. For R subset[h]^2 define C_h(R) by listing its pairs(i,j) in lexicographic order, replacing each pair by a^i b a^j c, and appending d. In particular C_h(empty)=d. Every code is nonempty and

    |C_h(R)| <= h^3+3h^2+1.

For a word of relations concatenate the codes. We define a total language K_h by the following NFA on ALL Gamma words; behavior outside the code image is not a promise and need not match relation syntax.

Its states are E_i,F_i,G_i,S_i for1<=i<=h; M_k for0<=k<h; T_j for0<=j<=h; initial q_in and accepting q_acc. There are6h+3 states. Every body transition moves right. Missing transitions reject the branch.

* On the left endmarker q_in moves right nondeterministically to any E_i.
* E_i on a moves to either F_i or M_(i-1). F_i loops on a and goes to G_i on b. G_i loops on a and goes to E_i on c. These states skip one entire pair while retaining i. E_i has no transition on d.
* M_k on a goes to M_(k-1) if k>0. M_0 on b goes to T_0. These states check that the FIRST field has exactly i a's. Entry is only from the pair-boundary state E_i, so matching a suffix of a longer field is not allowed.
* T_j on a goes to T_(j+1) if j<h. T_j on c goes to S_j if1<=j<=h. This chooses the second endpoint j.
* S_j loops on a,b,c, and on d goes to E_j. Thus after choosing one edge it ignores the rest of that relation's list and carries j to the next relation.
* At the right endmarker E_i makes a stay move into q_acc. No other state accepts there; q_acc is the only accepting state.

On a concatenation of valid relation codes an accepting branch chooses exactly one listed pair per block, with successive endpoints matching. This follows inductively from the E/S phase invariant: crossing a d requires a previously selected pair, and after d the selected endpoint is the next E index. Conversely every relation path induces such a branch. Hence

    C_h(w) in K_h iff w in OWL_h.

The empty code word is accepted by the left-marker choice followed by right-marker acceptance. Malformed words have whatever total language membership this explicit NFA defines; no syntax oracle or extra promise is used.

Encode a,b,c,d by00,01,10,11 respectively, and call this fixed-length binary morphism B. Replace each source state q by a boundary copy and two half-code copies(q,0),(q,1). The first bit stores its value; the second performs the original body transition. Endmarkers are processed only in boundary copies, so an odd trailing bit rejects. This gives a binary one-way NFA for a total language L_h with at most

    N_h=3(6h+3)=18h+9

states and B(C_h(w)) in L_h iff w in OWL_h. The body moves are all rightward. The two endmarker actions retain the described acceptance behavior.

## Pulling any two-way target back through the code

Set M=2h^3+6h^2+2, the maximum binary code length of one relation. Suppose a t-state read-only two-way automaton A recognizes L_h, or its full binary complement. Build an automaton A' over the full relation alphabet that simulates A on B(C_h(w)). Its states are(q,j),1<=j<=M, together with(q,L),(q,R),(q,0), for each target state q. Thus A' has at most t(M+3) states. Tag0 is used on actual endmarkers; L/R are arrival tags.

At a relation letter R, offset j identifies the scanned virtual bit of its finite code. The transition table can inspect this bit because R is the actual scanned symbol and h is fixed for the machine. An interior virtual move updates j by a stay move on the real head. Moving right from the last bit moves the real head right with arrival tag L; moving left from the first bit moves left with tag R. At a new relation letter, L is converted by a stay move to offset1 and R to the last offset of that letter. At an actual endmarker an arrival tag is converted to tag0. From tag0 simulate the target's endmarker rule: a movement into the body uses the appropriate arrival tag, while a stay remains tag0. Moves outside endmarkers remain forbidden.

Initial state and actual head location match A's initial endmarker configuration. A state is accepting exactly when its q component is accepting. Invalid offsets are unreachable from the initial state and can have no successors. This preserves every nondeterministic choice. Removing the bounded arrival-normalization steps gives exactly the target computation on the encoded input, and conversely every target computation has a lift. Missing transitions, accepting configurations, stay loops, finite rejection and infinite nonaccepting branches are preserved. No branch is allowed to make a free choice about the encoded bit or block length.

The construction works for deterministic and nondeterministic targets, with the same bound. It is a state-count construction: the full relation alphabet and its enormous transition table are allowed by the stipulated source model. It makes no uniform time or transition-table-size assertion.

## Bounds and disposition

For a binary2DFA with t states recognizing L_h, the source deterministic bound yields

    4(t(M+3)+2)^2 >= 2^floor((h-2)/31).

For a binary2NFA with t states recognizing {0,1}* minus L_h, its pullback recognizes exactly the complement of OWL_h on ALL relation words, so

    t(M+3) >= (1/2)2^floor((h-2)/127)-1.

Since M is polynomial in h and N_h is linear in h, both bounds are2^{Omega(N_h)}. For every sufficiently large n choose h=floor((n-9)/18)>=2 and pad with unreachable states to exactly n. The constant in Omega is absolute, and the total binary languages include malformed encodings. This proves the stated technical source-relative consequence without changing its scope.

The operation is routine bounded-word coding plus finite-control offset simulation. The unary-list format keeps the source state count linear by separating the guessed first-endpoint comparison from second-endpoint counting; it does not strengthen the source algebraic obstruction. Kapoutsis's primary2013 paper already explicitly uses binary relation encoding and boundary-preserved lower-bound transfer in its restricted-reversal setting. That earlier theorem does not itself prove the unrestricted lower bound used here, but its encoding operation is a direct antecedent. We therefore classify this as TECHNICAL and do not nominate it as a substantial finding. No further family is silently substituted after this screen.
