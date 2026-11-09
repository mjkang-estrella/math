# Exact counterexample proof and scope

DRAFT, AI-assisted (OpenAI Codex). No human authorship, affiliation, publication, priority claim, or acceptance is asserted.

## Statement

For the tree obtained by contracting each hexagon in the Deutsch–Klavzar D_k recursion and retaining junctions and intervening edges, D_4 is isomorphic to G_phi(A), where A is the 23-element positive set printed in paper.pdf and recomputation.json. Therefore the universal nonexistence assertion for all k >= 4 is false. This contraction interpretation is inferred from the matching published Figure 10 and cited Figure 12; the original source does not explicitly prescribe a contraction operation. We make no claim about the cyclic molecular graph itself.

## Finite, exact proof

For each n in the table, trial division computes its prime factorization. Trial division exhausts possible prime divisors through the square root of the residual integer; the remaining factor, if greater than 1, is prime. The product of the prime powers is n, and Euler's product gives phi(n). The case n = 1 has empty prime product and phi(1) = 1.

Starting independently from every generator, recompute its complete orbit until repetition, including iteration zero. The union V has exactly 88 positive labels. Every computed totient lies in V; each table row agrees with the independently generated row, and every row lies on at least one generator orbit. Thus V = A_phi in both directions. The undirected non-loop edges are precisely {n, phi(n)} for n in V minus {1}; there are 87 distinct edges. Positivity and strict decrease until 1 establish connectivity and acyclicity.

Separately construct a graph from the recurrence arm(0) = leaf and arm(j+1) = unary(unary(binary(arm(j),arm(j)))), with D_k a centre joined to three copies of arm(k-1). Canonical rooted strings recursively sort all child strings, so matching strings supply a root-preserving isomorphism, not just a degree or distance histogram. The checker constructs an explicit bijection, stores it as model_to_label, and compares the complete undirected edge set under this bijection. The centre of the orbit tree is uniquely 1024; layers are 1,3,3,3,6,6,6,12,12,12,24.

For an additional bridge to the actual formal data, read Certificate.lean as text only; extract its 88 labels, compare the label set, and check every ordered pair against both the independently constructed recursive graph and the computed totient adjacency. All pairs agree. No formal tool or discovery algorithm is executed.

This proves Realizable(nanostar 4). A purported universal conjecture applied at 4 would give its negation, a contradiction.

The arm order satisfies a_0=1 and a_(j+1)=3+2a_j, giving a_j=4*2^j-3 and |D_k|=6*2^k-8 for k>=1. The D_2 source control has 16 vertices, 15 edges and centre 16; D_3 has 40 vertices, 39 edges and centre 128. Full control factorizations, phi values, edges implicit in parents, profiles and isomorphisms are stored in recomputation.json.

## Formal proof and trusted receipts

The literal endpoint is R162.not_conjecture349177 : ¬ R162.Conjecture349177. Definitions.lean defines the general tree, orbit, adjacency, positivity, isomorphism and all-k conjecture. realizes_of_label proves the label-to-orbit graph bridge without a residual arithmetic assumption. The formal generator Finset is all 88 labels; its orbit is the same as that of the smaller 23-element set.

Twelve modules (Definitions, Arithmetic, Certificate, EdgeRows0 through EdgeRows7, Endpoint) occur in the original byte-identical proof-source.zip. Independent review reports strict builds, explicit-module leanchecker replay, and all-local axiom coverage. Only propext, Classical.choice, and Quot.sound are reported. The manuscript task has not rerun Lean or leanchecker and does not certify these reports as a new replay.

There are four compiler-generated partial runtime helpers. They remain in the unchanged packet. The reviewer reports 271 safe, non-partial reachable local endpoint dependencies, with none of these helpers reached. The root ruling resolves the review's literal metadata hold by the ASEP 368807 precedent; the original review HOLD and root qualified pass are both retained. We do not erase or rewrite that disagreement.

Prebuilt dependency oleans remain trusted, without full source attestation or upstream rebuild. leanchecker uses Lean's own kernel foundation. Sampled resource monitoring is not a transient-peak guarantee. Source fidelity and significance are qualified passes; the result is a modest exact counterexample from routine backtracking. Unread Tau-function successor and Rashid et al. work remain literature limitations. No worldwide priority certification is asserted.
