# Quotient units and symmetric cycle opening

Author: Myeongjin Kang, no affiliation. Original prose CC BY 4.0. Candidate proof supplement, not independently reviewed. The parent supplied the quotient-cycle formulation and the correction that equal-period agreement covers a text and its distinct reverse-complement as well as different rotations of one text.

## Units and orientations

For a nonself reverse-complement orbit of primitive texts, select the lexicographically greatest forward rotation among BOTH text groups as the canonical source text. Run the ordinary source group procedure on that representative and mirror its outgoing constructions. A unit is an ordinary block together with its reflected block. It may have two separate connected pieces, called its two ports. A k-layer block of period p has unit budget2kp, and its two ports can be internally joined separately for at most2(k-1)p, freeing2p. There is no assertion that the two ports meet.

For a self-reversed group, use adjacent sorted-layer pairs. Each pair already meets at reflection-axis vertices. An individual pair or a collective block of2k layers with odd core2k-1 is one unit, with budget2kp. Its internal band and mirror cost at most2(k-1)p, freeing2p; its two conceptual ports are already connected. All outgoing constructions use the lexicographically greatest forward phase of the text.

Incoming host routines may choose either orientation of a nonself host orbit or splice a self host pair. This choice affects only already rooted units and immediate attachments. It does not change canonical outgoing plans. The anchored request reclassification in `self-text-rule-and-host.md` is essential for this separation.

Each outgoing unit has an actual target record R on a layer; its reflected construction has target rho(R). After group processing the target layer and its reflection either belong to the same quotient unit or are both marked rooted. Thus mapping every unit to its target unit (or to a rooted sink) gives a finite functional directed graph. Budget assignments are disjoint. Ordinary incidental intersections may help but do not consume budget or change this graph.

Each planned pair of links connects the source's two ports to corresponding target ports, possibly with a swap. For a self unit the ports coincide. Therefore a quotient path lifts to at most two paths, each leading to a corresponding port at its endpoint. This elementary two-port invariant handles twisted lifts without assuming they form two disjoint cycles.

## A one-unit cycle

Its target lies in this unit, hence has the same period p as the source. The chosen record is on a different aligned periodic TEXT. The equal-period part of the source agreement lemma gives |R|<p, whether the target is another phase of A or the distinct text rho(A). The stronger statement does not require the two alignments to be rotations in one forward group.

Omit both outgoing constructions. Internally join the unit's port or ports, using at most its budget minus2p. Root R and rho(R) by a round trip and its reflected round trip, costing2|R|<2p. Both ports are now rooted, even if they had been disjoint. This covers an ordinary two-cycle A->rho(A)->A that becomes a self-loop after quotienting.

## A cycle of at least two units

Select a unit whose canonical distinguished periodic text is lexicographically greatest among the units on this quotient cycle. Let q be its target unit's period. Every forward rotation of either target orientation is bounded above by the target's canonical distinguished text, hence by the selected source's text. The original, not merely reflected, outgoing plan is at this maximal phase. Thus the source maximal-rotation contact argument applies.

For an individual construction, the existing short-contact estimate gives a vertex of length at most q. For a collective construction on a nonself unit, use the source proof verbatim on its representative block. For a self unit use the same proof on the odd core: it needs only the geometric inequalities with K=kp, not the number of layers. If any core layer already has a vertex of length at most q, the collective link connects it to the core and target. Otherwise the source argument obtains b-t<q, chooses x=min(t,a+K), and constructs the ordered list

    [a,b), [x,b), [x,F), [a+K,b+K),

where F=f_top(x)<=H<=b+K. This has cost K, touches every core layer, and has short contact [x,b). The omitted final paired layer is connected to the last core layer through its fixed-axis vertex. Hence the whole unit is connected as required. Reflection gives the second short contact at no further geometric assumption and with the mirrored reserved budget.

Retain this pair of outgoing links. Omit the TARGET unit's outgoing pair instead. The selected and omitted pairs differ since the quotient cycle has at least two units. Internally join the target unit, freeing2q, and spend at most2q on rooting the selected short contact and its reflection.

After deletion, the quotient cycle is a path ending at the target unit, with the selected link immediately before that target. Every port of every unit on this path connects along its lift to a target port. Each target port is attached to one of the two retained short-contact pieces and is therefore rooted. The lift may have one connected component (a twisted lift, or a self unit) or two components; either way each component has a rooted contact. No assertion that the quotient cycle lifts to two cycles is needed.

Distinct quotient cycles have disjoint units. Execute all other reserved links toward rooted sinks or opened cycles in increasing distance order. The two-port invariant then roots every port, hence every layer. All additions are ordinary closed walks together with their reflected closed walks; they preserve balance, tau symmetry, and even degree at fixed vertices. Each unit's budget is spent at most once, with the replacement savings charged only to that unit. Total added up cost is at most the sum W of all original layer budgets.

This closes the proposed global cycle accounting conditional on the count, decomposition/pairing, group partition, and host lemmas in the other notes. A complete assembled candidate and independent review are still required. This note is not a campaign acceptance or review PASS.
