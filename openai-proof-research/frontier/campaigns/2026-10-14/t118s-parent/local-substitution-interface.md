# Conditional local substitution interface for T118S

Parent author assistance, not an independent proof or contribution gate. The complete pinned completeness and consequences sections were read; identities and limits are in `source-reading.json`. The agent originated the clause-local inventory split. This note checks its degree bookkeeping conditionally on that split and a consistent source family of local assignment laws.

Index the source's B bin slots by physical X-rows. Every such row is used exactly once in either local state; selected/unselected switching changes the other four items in its bin. A witness configuration therefore has a unique row slot. Assign zero to every feasible configuration outside the witness family, including configurations containing multiple X-rows. This leaves the relaxation itself unrestricted.

Suppose all named item assignments have been made within one clause or one edge, and every resulting bin indicator f_H is a Boolean function of at most six underlying XOR variables. Suppose also that conservation of each physical item is a pointwise identity on the satisfying assignments of its one clause or two endpoint clauses. Then a product of at most r+1 configuration literals can be evaluated using a source local distribution on at most 6(r+1) variables. Its value is nonnegative. Consistency of these source laws makes the induced moments well-defined when enlarged supports are used.

For an item constraint times at most r literals, take the union of the queried supports (at most 6r variables) and that item's clause/edge support (at most six). In that local law every term of the physical-item sum is present on one common support, and its sum is exactly one. Multiplying the pointwise identity by the literal product proves the lifted equality. Formal polynomial degree alone would not ensure this: the source law must exist on the union and enforce the relevant clause constraints there.

For each X-row, its possible configurations partition its local assignments. Summing their first moments gives one. Summing over the B rows therefore gives objective B. This argument uses local conservation and consistency, not a globally satisfying XOR assignment or globally feasible packing.

These observations do not supply the needed source pseudo-distributions, prove the exact stock split, or establish integral soundness. They also do not make a routine local substitution substantial. Those obligations and primary credit remain with the full author proof and comparison.
