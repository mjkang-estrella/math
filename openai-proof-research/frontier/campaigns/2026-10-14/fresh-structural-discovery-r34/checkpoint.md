# Family 134: full height-two question remains unresolved

Status: **UNRESOLVED / TECHNICAL CHECKPOINT; no nomination or campaign increment.** This is discovery work, not an independent review. The parent reported 11/20 accepted results at assignment. Source truth at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is stipulated throughout.

The unchanged question is whether every regular language over **every original finite alphabet** has a generalized regular expression of height at most two, with union, concatenation, complement in that same alphabet's free monoid, and Kleene star. Constants are the empty language and the singleton empty word. No bound on expression size or construction time is requested. Empty alphabets remain included. No restricted recognizing monoid, alphabet, or episode condition replaces this question. The full mechanism gate has not passed, so no proof-candidate scope freeze is claimed.

## What the supplied construction pays for

The height-three manuscript supplies a prefix code E of nonempty episodes, an exceptional subcode D, a deterministic affine update F_e on V whose linear part is the original monoid action, and two split constructions. The outer split is sound on E* but complete only on E minus D. The inner split is sound and complete on D*, for a different affine update G_e on U = V plus F_2. The linear part of G_e is the homogeneous lift of F_e. Boolean queries recover F on D* from G on D*, and eventually recover the original monoid action from F on E*.

The graph-language split formula has cost H -> max(2,H+1), where H is the height of graph tests on skipped episode sequences. Thus the actual chain is 0 -> 2 -> 3. The zero bound is for the empty skipped class, not for all finite-state computations. The component compiler proves height one by explicit finite unions of ultimately periodic templates a c^j b, including each standalone suffix with false metadata and its own exact endpoint. It does not say that arbitrary regular tests have height one.

The height-four companion uses three splits and two total-table lifts. The height-thirteen companion already uses two splits computing the **same** enlarged update at each residual stage, yet still pays separately for the two split applications. Thus merely naming a common state space, total table, affine recovery, or common update is not a new height-saving operation. The primary Pin–Straubing–Therien compiler preserves height under star-free injective substitutions; arbitrary tagged-word projection or inverse general morphism is not one of the paid closure operations. Their Theorem 8.1 represents every regular language as an inverse image of a restricted-height-one language, making that distinction material.

## A proved obstruction to two proposed shortcuts

See `clock-barrier.md` for a full proof. For the actual finite clock image H, let m be the number of tags, B the good totals in H and W_H the exceptional totals. The source's edge alternative implies

    |W_H| >= m(m-1) sqrt(|B|).

The roster estimate and multiplicity choice ensure B is nonempty. Hence, with at least two tags, there is an actual finite-clock total having a unique off-diagonal edge. This conclusion is about the finite clock used by the source, not a point of the ambient torus that the clock never reaches.

Over any alphabet with distinct letters a,b, take q sufficiently large and set

    e_q = a^q b a^(L_tail-1).

Choose q-L in that off-diagonal clock residue. Every fixed marker-inspection window and seed at the true origin is then in the constant a-region, so all relevant marker searches are absent. The first subsequent mismatch is exactly q; e_q is a genuine complete episode with that clock total and belongs to D. Every successful outer split must use the unique off-diagonal tag pair (alpha,lambda), so its incoming state must equal X(alpha). Since V has at least two elements, the outer split is unavailable for another input state. Infinitely many q realize the same residue. For every k, e_q^k is a correctly parsed sequence of k exceptional episodes.

Consequently, one cannot obtain a single complete outer split by deleting D, treating the off-diagonal residues as unreachable, declaring exceptions finite, or imposing a bounded length on exceptional runs. These are barriers to those repairs only. They are **not** a lower bound of three for generalized star height.

## The unpaid operation

One sufficient route would construct, over the original alphabet, a deterministic update with a recoverable monoid action and one universally sound, everywhere-complete split with finite prefix languages and height-one suffix languages. The source split formula would then give height two. A different route could directly eliminate the outer star over height-two exceptional graph tests, with a proof of all same-word state correlations.

Neither route is established. The exceptional decoder cannot simply be used on all episodes: its uniqueness test chooses an origin satisfying the exceptional predicate. On a nonexceptional episode the true origin does not satisfy that predicate; any unique chosen witness is therefore a false origin. The source soundness proof expressly uses membership in D. Adding a domain test after the cut does not by itself recover the missing prefix or synchronize independent metadata.

I also investigated simultaneous affine shifts. On an abstract product grid, demanding a constant coordinate line in each of finitely many coordinate blocks is obtainable by the same local-lemma argument as the source; `simultaneous-shifts.md` records the exact credited extension. This does not unify the actual two splits. Their tables are indexed by different later contexts, the exceptional decoder has the restricted domain just described, and the off-diagonal clock case prescribes an affine translation. A common correction compatible with these constraints and universally sound cross-kind pairs has not been constructed.

## Formal and contribution limits

A feasible supporting Lean fragment is the finite-clock obstruction: define edges by witnesses i in I_alpha, j in J_lambda, i+j=z; prove cross-edge disjointness under the source edge alternative, nonemptiness from active tags, and the forced-input consequence of a singleton edge. A finite-cardinality extension can verify the displayed lower bound. That fragment would not formalize the episode geometry, the full source compiler, or a height-two theorem. No Lean file was compiled in this checkpoint and no formal PASS is claimed.

The clock counting and explicit exceptional words are elementary consequences of the source operations, retained as diagnostic mathematics. The simultaneous shift lemma is a routine extension of the supplied probabilistic argument. None is offered as a substantial campaign result or a new-to-literature theorem. Even a future height-two deduction would concern the exact stipulated-source-to-height-two consequence; it must not be described as settling whether height one always suffices or the general problem of computing minimum generalized star height.
