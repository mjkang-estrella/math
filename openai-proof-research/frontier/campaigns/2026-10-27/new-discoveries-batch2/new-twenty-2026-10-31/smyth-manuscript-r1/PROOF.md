# Proof and scope: DRAFT, AI-assisted, zero accepted credit

Source: Clifford Smyth, arXiv:1512.04084v1, Conjecture 1.5; MathDB 332037. N includes zero. U^m_n consists of length-m ordered maps to N summing to n. Rearrange concatenations decreasingly and compare equal total sums and all prefixes. The domain must dominate its image.

At (A,a,B,b)=(3,20,2,19), let X=U^3_19 × U^2_20 and Y=U^3_20 × U^2_19. Let D be all partitions of 39 dominated by some generator in G:

[[13, 12, 8, 4, 2], [13, 13, 7, 3, 3], [12, 12, 8, 6, 1], [14, 12, 6, 4, 3], [13, 11, 7, 7, 1], [14, 11, 6, 6, 2], [15, 11, 5, 5, 3], [16, 10, 5, 4, 4]]

Define S={x in X: rearr(concat(x)) in D} and T likewise in Y. Direct enumeration gives |S|=1137 and |T|=1134. D is downward closed by transitivity: total weights agree and each prefix inequality composes. A conjectured injection would map S into T and remain injective there, requiring 1137 ≤ 1134. Contradiction. This refutes the exact universal conjecture, not Smyth's independently proved total-nonnegativity theorem.

The row counts are in audit-certificate.json and every row matches the copied Lean certificate text (audit-correspondence.json). Compositions are enumerated uniquely by successive first entries. Prefixes beyond five equal the total. Complete sorted ordered-pair lists, including zeros, are S.json and T.json, serialized with Python json.dumps default separators and no trailing newline:

- S SHA-256: 08e5379d0fed4b8c241356e8bd5098bae47ce2b29412fac73d95b22e72b27064
- T SHA-256: 269c1bfb06bb0c380d93e8ab212397d9794e31f0704f99d6243530a468c45e09

The Lean ZIP is reused byte-identically. Its endpoint is Smyth1512.not_conjecture15 : ¬ Smyth1512.Conjecture15. Seven literal definitions are compared textually to the reviewed discovery draft. The structural enumeration bridges, sum condition, finite/all-prefix bridge, duplicate-free lists and list/function realization are in Bridges.lean; CountBase and the row modules prove counts; Endpoint gives the finite injection contradiction. Controls proves sorted permutation fidelity and an inhabited true instance.

Supporting computation only: maximum matching 4407 by fresh HK and flow, reversed flow 4050, small region through bounds 10 and sum 16 passing, and family b=19 through 43 failing. The fresh sweep checks 1836 nontrivial cases; all remaining cases have the explicit general constructions in the paper. No infinite-family theorem or separate credit is asserted.

Root's copied replay receipt reports PASS for the packet's 48 modules and explicit checkers, with endpoint axioms propext, Classical.choice, Quot.sound. This worker never ran Lean, lake or leanchecker. The current registry receipt is bounded path/header screening, not full-body proof reading.

Retention: the author-hosted submitted Order manuscript retains the conjecture as Conjecture 6 and its implication as Theorem 7. The printed post-refereeing body is UNREAD. Prior-art searches are bounded; no priority claim is made. Significance is modest, low-profile and non-load-bearing. Root alone accepts; accepted credit is zero. The campaign context supplied to this lane was 37/40 beyond 39; this document makes no ledger update or assertion of a refreshed count.
