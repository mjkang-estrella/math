# MathDB320321: exact primary-clause counterexample candidate

Primary source: M. R. Allen, *An investigation of partizan misère games*, arXiv:1008.4109v1; actual downloaded PDF misere.pdf. Definition 6.3.1 printed p.128 (PDF p.143), arrow definition p.129, Conjecture 6.5.1 p.131 (PDF p.146); Section 1.2 gives game positions, impartiality and disjunctive sum. The thesis carries July 2009 and a 2018 copyright date; the arXiv banner says 24 August 2010. These are recorded without inventing revision chronology.

The conjecture's main clause is definite: a→b iff Left moving second wins b+a°. Its final parenthesis says “or something similar”. We refute the definite clause, not an unspecified alternative category or relation. For impartial games all options for Left and Right coincide at every follower. Their adjoints and disjunctive sums remain impartial. Thus Left-second, Right-second, and second-player winning conditions coincide. We do not replace this with the first-player criterion.

Write a position by its common option set. Set

    Z={}, S={Z}, T={S}, U={Z,S}, B={U}, V={S,T}, C={V}.

In partizan notation each common option list is repeated on both sides: e.g. U={Z,S | Z,S} and B={U | U}. All are finite impartial game trees. In particular B must not be replaced by its normal-play nim-value; misère outcomes depend on the actual tree.

Adjoint recursion gives Z°=S, S°=T, U°=V, B°=C. The terminal Z is an N-position in misère play (the next player wins). Every nonterminal position is P exactly when every option is N. The following table follows immediately from this rule and lists all sums needed:

| Position | Outcome | Options, or reason |
| --- | --- | --- |
| Z | N | terminal |
| S | P | Z |
| T | N | S |
| U | N | Z,S |
| B | P | U |
| V | N | S,T |
| C | P | V |
| S+S | N | S |
| S+T | P | T,S+S |
| S+U | N | move in U to S+S or S; in particular S is P |
| T+U | N | move U to S+T, which is P |
| S+B | N | move S to B, which is P |
| T+B | P | S+B and T+U, both N |

Consequently S→B because B+S°=B+T is P; B→Z because Z+B°=C is P; and S↛Z because Z+S°=T is N. This refutes transitivity using α=S, β=B, γ=Z. No search minimality is claimed.

## Formal statement and semantics

formal/Counterexample.lean defines finite impartial trees with an identical option list available to either player; lists represent the finite option sets in the source. The displayed trees have exactly the specified options. Repeated options in a disjunctive sum do not affect the existential winning rule. add implements exactly the two kinds of source disjunctive-sum move; adjoint implements Definition 6.3.1 restricted to impartial games, where a nonzero position has both Left and Right options. nextWins implements the misère winning-strategy recursion; nextWins_rule and secondWins_rule prove its existential and universal option formulations, including the terminal exception. Every recursion has a sizeOf termination proof.

The endpoint Misere.not_transitive is the negation of universal transitivity for Arrow a b := nextWins (add b (adjoint a)) = false. This is a counterexample over actual finite game trees, not a parameter-only fragment of a proposed universal positive theorem. Since these trees are impartial source positions, they also refute a universal assertion over a larger universe containing them. No quotient by normal-play equivalence is used.

The individual arrow facts and endpoint have transitive axioms [propext, Quot.sound]. The project uses Lean 4.34.1 and its bundled Std only; there is no mathlib dependency or external theorem bridge. replay.py extracts only the submitted source into a clean directory and compiles again with warnings as errors, auditing every public definition/theorem. verification/result.json and Replay.log contain the result.

This is an unaccepted candidate. Root must independently assess source fidelity (including the parenthesis), prior art, and substantive significance. The source already gives a partizan counterexample in Example 6.3.3; that example is not this impartial one. A tiny obstruction to the explicitly conjectured impartial restriction may resolve the named main clause, but its size alone establishes neither novelty nor significance.
