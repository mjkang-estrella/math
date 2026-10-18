# Prospective full target: extensional BGK

Status: unresolved research target, not a candidate or nomination.

For every pure type specification S=(Sorts,Axioms,Rules), without functionality, finiteness or stratification assumptions, equip the ordinary fully annotated syntax with raw beta-eta conversion in the conversion typing rule. If every legal expression in every valid finite open context is weakly beta-eta normalizing, then every such expression is strongly beta-eta normalizing. Reduction is compatible in all positions, including lambda annotations and both product components. Eta contraction is lambda x:A.(M x) -> M only when x is absent from FV(M), including annotations. Legal expressions include terms and types appearing in derivable judgments.

This is the extensional version of the existing Geuvers thesis Conjecture 8.1.2, not an invented restricted theorem. Source245 supplies the beta-only BGK theorem with beta conversion; it does not directly supply this statement. No restriction to beta-legal terms, functional specifications, closed terms, erased syntax, or an assumed beta-normalizing extensional system may replace this target.

Chronology: source introduction/metatheory1–210/erasure and primary Geuvers and Barthe contraction interfaces were read before this freeze. Raw erasure obstructions and possible labelled eta lifting were explored before freeze; no full proof exists. Any subsequent unified proof must preserve this statement.
