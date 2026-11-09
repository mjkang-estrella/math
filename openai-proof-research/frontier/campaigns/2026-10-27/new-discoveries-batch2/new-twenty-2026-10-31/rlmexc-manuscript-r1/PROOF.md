# Hand proof and certificate scope

DRAFT; AI-assisted. No acceptance or priority claim.

2. Which conjecture is being refuted?

In §5.2 of [1], cycle type is defined as “the integer partition (μ1,μ2,…,μℓ) where the parts are the cycle lengths of π arranged in decreasing order.” In particular, fixed points contribute parts equal to 1. We transcribe the version-of-record conjecture verbatim, with the displayed formula set inline with the text:

“Conjecture 5.2.1. Let k be a fixed positive integer such that 2 ≤ k ≤ n. Then

(−1)n−1 ∑π∈Sₙ, min(type(π))≥k (−1)inv(π) xRLMv(π) yEXCv(π),

where type(π), the cycle type of π, is an element in ℕ[x1,…,xn,y1,…,yn]. The case k = 2 follows from Theorem 1.0.1 (the conjecture is not true for k = 1). For the case k = n, all permutations have the same sign, so the statement is trivial.”

The grammatical placement of “where type(π), the cycle type of π” is retained. Polynomial membership refers to the displayed sum. Define that normalized sum to be Fn,k, and denote the same sum without the factor (−1)n−1 by Gn,k.

Version distinction. arXiv v3 and MathDB 350721 instead say: “Let k be a fixed positive integer such that 1 ≤ k ≤ n. Then” followed by Gn,k, and “where type(π) is the cycle type of π, is an element in ℕ[x1,…,xn,y1,…,yn].” There is no normalization factor. The next sentence says that k = 2 follows from the main theorem.

Versions v1 and v2 have the identical, malformed assertion: “Let k be a fixed positive integer. Then”

(−1)n ∑π∈Sₙ (−1)ℓ(type(π))(∏j∈RLMv(π) xj)(∏j∈EXCv(π) yσ(j))

“is an element in ℕ[x1,…,xn,y1,…,yn].” Here k is absent from the sum, and the displayed σ is retained from the source. The following note asserts “(−1)ℓ(type(π))−1 = (−1)inv(π)” and refers to k = 1. We do not repair or use that assertion.

The k = 1 and even-n sign failures of the v3/MathDB statement are trivial wording defects and are not claimed as mathematical contributions. The supplied root ruling scores the substantive question against the refereed statement. Our odd-n witness refutes both later readings without exploiting either defect.

3. The negative-coefficient family

Theorem. For n ≥ 8 put R = {1,n−4,n−2,n−1} and E = [n] ∖ R = {2,…,n−5} ∪ {n−3,n}. Then

[xRyE] Gn,3 = (−1)n,[xRyE] Fn,3 = −1.

Consequently Conjecture 5.2.1 fails for k = 3 at every n ≥ 8.

4. Proof: forcing the complete list

A permutation contributes to the indicated monomial exactly when RLMv(π) = R and EXCv(π) = E. Since E and R are complements, each v ∈ E has pos(v) < v, and each v ∈ R has pos(v) ≥ v, where pos = π−1.

The value in the last position is a right-to-left minimum. Right-to-left minimum values increase with their positions: if i < j are such positions, π(i) < π(j). Hence π(n) = max R = n−1. The value 2 must be at position 1. Inductively, for 2 ≤ v ≤ n−5, the requirement pos(v) < v and the already occupied positions force pos(v) = v−1. Thus π(i) = i+1 for 1 ≤ i ≤ n−6.

Set c = n−5. The remaining positions c,c+1,c+2,c+3,c+4 contain {1,c+1,c+2,c+3,c+5}; the final value is c+4. The excedance conditions force pos(c+2) ∈ {c,c+1}, pos(c+1) ≥ c+1, and pos(c+3) ∈ {c+3,c+4}. The RLM conditions force

pos(1) < pos(c+1) < pos(c+3).

If pos(c+3) = c+3, the value after it must be c+5, since it is a right-to-left minimum. Now c,c+1,c+2 contain 1,c+1,c+2. If c+2 occurs at c+1, their order is (1,c+2,c+1); if it occurs at c, their order is (c+2,1,c+1). These give B1 and B2.

If pos(c+3) = c+4, then the first four tail positions contain 1,c+1,c+2,c+5. If pos(c+2) = c, ordering 1 before c+1 leaves three orders for the other values, giving A1, A2, A3. If pos(c+2) = c+1, the condition pos(c+1) ≥ c+1 puts c+1 at c+2 or c+3. The former gives A4; the latter gives A5 or A6. These cases exhaust all possibilities.

The following explicit one-based words at n=9 instantiate the tails, whose general forms and cycle decompositions are given in the manuscript source.

A1: [2, 3, 4, 6, 1, 5, 9, 7, 8]; inv=7; partition=[6, 3]; admissible=True

A2: [2, 3, 4, 6, 1, 9, 5, 7, 8]; inv=8; partition=[9]; admissible=True

A3: [2, 3, 4, 6, 9, 1, 5, 7, 8]; inv=9; partition=[5, 4]; admissible=True

A4: [2, 3, 4, 1, 6, 5, 9, 7, 8]; inv=6; partition=[4, 3, 2]; admissible=False

A5: [2, 3, 4, 1, 6, 9, 5, 7, 8]; inv=7; partition=[5, 4]; admissible=True

A6: [2, 3, 4, 9, 6, 1, 5, 7, 8]; inv=10; partition=[9]; admissible=True

B1: [2, 3, 4, 1, 6, 5, 7, 9, 8]; inv=5; partition=[4, 2, 2, 1]; admissible=False

B2: [2, 3, 4, 6, 1, 5, 7, 9, 8]; inv=6; partition=[6, 2, 1]; admissible=False

Conversely, every listed tail satisfies the required value sets. In each, 1 precedes c+1, which precedes c+3, followed by c+4 at the final position. Their later values are larger, so precisely these four values are RLMs. Every prefix value has the later value 1; the value c+2 has a later 1 or c+1; and c+5 has the later c+4. None of those values is an RLM. Direct position comparison gives exactly E as the excedance-value set.

The table therefore describes the whole coefficient fibre before imposing any restriction on cycles. No cancellation or cycle argument has been used to prune the list.

5. Proof: cycles, signs and the boundary

To check the cycle column without extrapolating from experiments, let C denote the chain 1 → 2 → ··· → c. In cycle notation the eight permutations decompose as follows; the notation (C,a,…) means the cycle (1,2,…,c,a,…).

A1: (C,c+2,c+1)(c+3,c+5,c+4);A2: (C,c+2,c+5,c+4,c+3,c+1);A3: (C,c+2)(c+1,c+5,c+4,c+3);A4: (C)(c+1,c+2)(c+3,c+5,c+4);A5: (C)(c+1,c+2,c+5,c+4,c+3);A6: (C,c+5,c+4,c+3,c+1,c+2);B1: (C)(c+1,c+2)(c+3)(c+4,c+5);B2: (C,c+2,c+1)(c+3)(c+4,c+5).

All cycles have length at least 3 precisely for A1, A2, A3, A5 and A6, since c = n−5 ≥ 3. A4 has a 2-cycle, while B1 and B2 have a fixed point. A cycle of length d has sign (−1)d−1, as it is a product of d−1 transpositions. The usual inversion-parity sign therefore gives (−1)inv(π) = (−1)n−number of cycles. The five surviving signs, in the above order, are (−1)n times 1,−1,1,1,−1. Their sum is

(−1)n(1−1+1+1−1) = (−1)n.

Multiplying by (−1)n−1 yields −1, completing the proof. At n = 7 the forcing and the same list still apply, but A5 has a cycle of length 2 and is also excluded. The remaining four signs cancel. The target coefficient at this boundary is 0.

6. Fresh finite computations

The following are exact computations, not additional formal theorems. A new isolated Python script enumerated every permutation, computed the two value sets directly, decomposed all cycles including fixed points, and accumulated signs by monomial for every 2 ≤ k ≤ n. Its cycle-parity signs were independently checked against literal inversion counts on every row of the family certificate for n = 7 through 16.

For every n ≤ 7 in the nonempty range 2 ≤ k ≤ n, no negative coefficient occurred. At n = 8 and 9, exactly eight permutations have the target pair of value sets, agreeing with the hand proof. The n = 10 computation was divided into disjoint chunks by the first value, with coefficients combined before counting their signs. The dossier retains every chunk. It also contains the words, inversion counts, complete cycle types and target coefficients for n = 8 through 16, plus independent searches through all orders of the five free values.

Source typo. The polynomial labelled “for n = 3” after (23) of [1] is the n = 4 single-cycle sum. A fresh single-cycle calculation verifies this identity; this observation is only a transcription remark.


General tails at c,...,c+4, with c=n−5 and last value c+4:
A1=(c+2,1,c+1,c+5,c+3)
A2=(c+2,1,c+5,c+1,c+3)
A3=(c+2,c+5,1,c+1,c+3)
A4=(1,c+2,c+1,c+5,c+3)
A5=(1,c+2,c+5,c+1,c+3)
A6=(c+5,c+2,1,c+1,c+3)
B1=(1,c+2,c+1,c+3,c+5)
B2=(c+2,1,c+1,c+3,c+5)

The Lean packet formalizes only the n=9 witness, the dual negation and the n=3 positive control; the universal family is a hand proof.
