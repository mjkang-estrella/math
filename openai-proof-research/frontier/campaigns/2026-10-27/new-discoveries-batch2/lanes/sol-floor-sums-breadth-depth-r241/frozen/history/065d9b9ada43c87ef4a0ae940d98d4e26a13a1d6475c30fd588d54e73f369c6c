# r112: no eligible discovery

Two distinct full-scope source questions survived the required-file local duplicate triage as leads: Fu's admissible assigning-polynomial conjecture and Hayashi's finite connected quandle conjecture. This means no same-question hit was identified in the inspected local content, not semantic registry absence or literature novelty. The third lead, minimal filling architectures, is publicly refuted and was dropped immediately. No discovery credit is requested.

## Fu: full surviving question, classical exclusion

Primary bytes: `inputs/fu-v5.html`, arXiv:2409.12404v5, 22 January 2026, Definition 1.2 and Conjecture 5.3. For every finite graph G (parallel edges and loops allowed), every admissible assigning alpha with alpha(e)=1 on every loop, the unsigned coefficients w_0,...,w_r of P(G,alpha;k)/k^c(G) are log-concave and unimodal. Admissibility arises from oriented edge gains in an additive Abelian group. This is the full latest question, not the unrestricted arbitrary-assignment version of v1 Conjecture 4.3. The current arXiv abstract history confirms v5 is latest at retrieval.

Strongest objection: it is a direct specialization of the reduced-characteristic-polynomial theorem for matroids. The following all-parameter bridge confirms that objection; no novelty is claimed for the bridge.

Declare cycles with zero gain balanced. They form a biased graph: in a theta, two zero path-difference sums force the third to vanish, so precisely two balanced cycles cannot occur. Let M be its complete lift matroid, adjoining the extra point e0. Zaslavsky, *Biased graphs II*, Theorem 3.1(A)(j), printed pp57–59, gives, for S contained in E,

    rank_M(S) = r_G(S) + 1_{S unbalanced},
    rank_M(S union {e0}) = r_G(S) + 1.

Thus rank(M)=r_G(E)+1, including the entirely balanced case where e0 is a coloop. No balanced loops occur by the source hypothesis; all other singleton edge sets and {e0} have rank1, so M is loopless. The construction permits disconnected graphs, parallel edges, unbalanced loops, arbitrary Abelian gain groups including torsion, and isolated vertices. The empty edge-set case gives a rank1 matroid on {e0}.

Write r=r_G(E). Pair the S and S union {e0} terms in the characteristic-polynomial subset expansion. Their total is

    (-1)^|S| [k^(r+1-r_G(S)-epsilon(S)) - k^(r-r_G(S))].

For unbalanced S epsilon=1 and this cancels exactly. For balanced S it is (k-1)(-1)^|S| k^(r-r_G(S)). Consequently

    chi_M(k) = (k-1) tau(G,alpha;k),
    reduced_chi_M(k) = tau(G,alpha;k) = k^(-c(G)) P(G,alpha;k).

Adiprasito–Huh–Katz, Annals188 (2018), Theorem9.9(1), printed p446, applies to M and supplies log-concavity of these exact unsigned coefficients. Positivity (also source Corollary5.2) gives unimodality by monotonicity of successive ratios. This covers both parts of the latest full conjecture. It is excluded as a routine classical specialization under the user's rules; neither the open label nor the apparently missed lift connection makes it eligible.

Actual closest bodies read: Zaslavsky Theorem3.1 statement/rank formula and its proof indications via linear classes, dual one-point extensions and the Dowling–Kelly lift, printed pp57–59 (retained scans `bg2a-13.png`, `bg2a-14.png`); AHK Section9 Definition9.1, Proposition9.8 and Theorem9.9 proof, printed pp442,445–447 (retained publisher PDF and text). AHK identifies the reduced coefficients with nef mixed degrees and proves the inequalities by rank truncation and Lemma9.6. No representability or characteristic-zero assumption is needed. The 1991 and 2018 bodies precede the 2024/2026 question.

`check.py` independently pairs subset expansions for 69 gain-graph cases, including parallel edges and unbalanced loops, checks 1,052,736 submodular rank pairs and exact coefficient inequalities. These tests check normalization and loops; the universal deduction above relies on the cited classical theorems, not the finite census. No new PROOF.md or formalization is nominated.

## Hayashi: unresolved full source question

Primary: Filipi arXiv:2503.22377v1 Conjecture2.1. Every finite nonempty connected quandle Q must have, for each left translation L_a, a cycle whose length is the order d of L_a. Equivalently every cycle length divides the largest length. Connectedness makes all translations conjugate; idempotence fixes a itself. Scope is all finite connected quandles, not just conjugation quandles or prime-power orders.

Closest actual proof bodies: Filipi Proposition5.1 uses the fact that prime-power permutation orders force nested cycle lengths; Proposition5.2 uses products and lcm; Theorem4.1 and its proof translate the conjugation subproblem to a generating finite conjugacy class and centrality. Lages–Lopes arXiv:2405.11660v1 Section4 proves the cases with at most five distinct profile lengths. Their finite profile split does not supply the arbitrary-profile step. No variant of these already proved classes is nominated.

Sustained route: put d=ord(L_a), and for each prime p dividing d let B_p=Fix(L_a^(d/p)). A point has orbit length less than d iff it belongs to at least one B_p. The desired full conclusion is precisely

    Q is not the union of B_p over primes p dividing d.

For a single prime, B_p is proper and the conclusion is immediate; for several primes each B_p being proper is insufficient. The exact missing universal inequality is |union_p B_p| < |Q| for translations of every finite connected quandle. Neither transitivity of the full multiplication group nor conjugacy of translations makes the fixed sets of powers of this one translation nested.

Executable route falsifier: the permutation (0)(1 2)(3 4 5) has order6 but no length6 orbit, even though it fixes the distinguished point0 as an idempotent translation must. Fix(g^3)={0,3,4,5} and Fix(g^2)={0,1,2}; both are proper and cover the six-point set. This refutes the proposed generic faithful-cyclic-action shortcut and the inference from separate maximal p-parts to their simultaneous realization. It is NOT a quandle counterexample: no connected idempotent self-distributive envelope is supplied.

For the conjugation branch the missing step is equally explicit. For every group G generated by a finite conjugacy class C, and c in C, one needs a single z in C with

    <c> intersect C_G(z) = <c> intersect Z(G).

The quotient of <c> by its central part is finite, since G acts on finite C with central kernel. Prime-by-prime noncentral powers can each fail to commute with some class element; the missing part is choosing ONE class element witnessing all primes. Filipi's Theorem4.1 proves the equivalence, not this assertion. Moreover a solution only for conjugation quandles would still leave arbitrary nonfaithful quandles outside the full Conjecture2.1 scope. No claim of progress beyond a reduction/route obstruction is made.

## Third lead: known public refutation

Kubjas–Li–Wiesmann arXiv:2402.00949 Conjecture12 asks whether all minimal filling polynomial neural-network width vectors are unimodal. Dao–Rodriguez arXiv:2605.09609v1 Theorem2.1 gives (2,3,4,5,4,6,4,1), activation degree2. Actual Lemma2.2 proof uses a rank65 finite-field Jacobian certificate, then Lemmas2.3/2.4 and recursive dimension bounds establish minimality. Source and refutation bytes are retained. Copied local public-catalogue hits additionally mention minimal filling results; therefore no local freshness is asserted for this lead, and no rederivation is attempted.

## Limits

Current public-prior HOLD is inherited: complete dated18:13 registries plus bounded later chains, latest successful r108 Omega89cda9c274d1122b7676173296af3047c3b64cd1 at20:10:57Z, OpenAI7ef5c0cc unchanged. The 300-file comparison-cap uncertainty and known HEAD/recursive-tree403 remain unresolved. No retry or alternate API endpoint was used. This lane fetched primary manuscripts and author-hosted classical bodies only. Path/term scans do not establish semantic absence. No accepted result, worldwide priority, Lean certificate, or paper is claimed.
