# 355433: complete ordinary classical/source bridge, zero credit

This is a proof using existing classical theorems and arXiv:2207.11596v2 Theorem 11. It is not a new-credit submission, a kernel certificate, or an independent acceptance. The unread journal body remains a source-comparison gate. No claim of worldwide priority is made.

Fix an arbitrary nonnegative integer total budget b. Write >=_b for the source order: A>=_b B means that for every finite loop-free test form X and every split of b and marker ownership, the outcome of A+X is at least that of B+X, with L>R. Write >_b for >=_b and failure of the reverse inequality. Budgets are not summed when adding forms. Write >=_c for the classical alternating normal-play order on the SAME literal finite game trees. None of the arguments below identifies the two orders on arbitrary game forms.

Define C recursively: all options lie in C and every left option is <_c every right option. Empty option sets are allowed. These are classical number FORMS, not all forms classically equal to a number. This distinction is indispensable: replacing a general form by its classical canonical form is not allowed here.

## Exact existing inputs

Schleicher–Stoll, An Introduction to Conway's Games and Numbers, author-hosted games12.pdf: Definition 2.7 (literal sum and conjugate); Theorems 2.8, 2.10, Lemma 2.11, Theorems 2.12–2.16 (classical group/order laws); Definition 3.1; Lemma 3.2 (strict interpolation for C); Theorems 3.3–3.4 (C closed under literal sum/conjugation and totally ordered). The actual proof passages were read, not just an abstract. Only finite forms are used, so transfinite extensions are irrelevant. In particular, these results give:

* Every literal follower of a form in C belongs to C; every Left move strictly decreases its classical value, and every Right move strictly increases it.
* A form in C is exactly one of positive, zero or negative in classical order. If it is positive, there is a Left option >=_c0. Indeed, in alternating normal play Left wins moving first, so some first move leaves a position she wins moving second. By totality that option is nonnegative. If it is negative the symmetric Right option <=_c0 exists.
* If N=_c0, all its Left options are strictly negative and all its Right options strictly positive.
* For A,B in C, A+bar(B) belongs to C and has the sign of the classical comparison A versus B; A+bar(A)=_c0.

These inputs concern classical order only. In particular they do NOT yet assert any contextual bidding comparison.

The bidding input is Kant–Larsson–Rai–Upasany, arXiv:2207.11596v2, Theorem 11 and its role-swapped version (also Corollary 12(1),(2)): if Left has an optimal 0-bid strategy at every follower of (D,0), and wins (D,0), where Left initially has no chips and Right owns the marker, then D>=_b0. The conclusion is universal in test game and partition. Its proof, including the use of additive Lemma 10 and both marker cases, was read. We verify a stronger hypothesis below: both players can optimally bid zero at EVERY follower and EVERY partition. We do not use source Proposition 15 to establish that fact; that proposition already assumes bidding interpolation and would be circular.

## The new-to-this-lane invariant: sign and marker, independently of chips

For every N in C and every partition of b, define

W_L(N,m) := (N>_c0) or (N=_c0 and marker m is owned by Right).

Claim: Left wins with an all-zero bidding strategy precisely on W_L; on its complement Right wins with an all-zero bidding strategy. Thus both players have optimal all-zero bids at every follower/partition. Here “optimal” includes losing states, where no strategy can improve the binary minimax outcome.

Proof by induction on the birthday of N, simultaneously for the two players. It suffices to establish Left's assertion on W_L; exchanging Left and Right, conjugating the form, and reversing the chip partition proves Right's assertion on the complement, because C is totally ordered.

Left bids 0, including the marker if she owns it (at a zero bid this makes no difference to the tie rule).

If Left wins this auction, she necessarily held the marker and Right bid 0. Hence W_L implies N>_c0. Choose a Left option N^L>=_c0, whose existence was established above. The tie transfers the marker to Right, without transferring chips. Thus W_L holds at N^L: it is either positive, or zero with Right owning the marker. Induction gives a win. In particular, the required move exists.

If Right wins the auction, any legal Right move is to N^R>_c N>=_c0, hence to a STRICTLY positive form. This remains in W_L irrespective of who owns the marker after that auction or how many chips Right paid. This covers a tied zero bid with Right's marker, a positive bid retaining Right's marker, a positive bid explicitly transferring it, and a positive Right bid while Left owns the marker. Induction applies at the resulting partition. If Right cannot move after winning, he immediately loses by the terminal-auction rule.

At N=0 the same argument works: if the marker belongs to Right he wins the auction against Left's zero and cannot move. More generally at a classical zero form with Right's marker, every Right option is strictly positive. No invocation of “last move wins” is needed. All plays end because birthday decreases on every actual move. Positive bidding streaks therefore cannot obstruct termination; no chip threshold or financial monotonicity is being used. This proves the claim.

Notice the crucial strength: this statement controls EVERY literal follower of N and every partition, not just the outcome at the root, and N has been certified in C without assuming bidding interpolation.

## Lift to all-context bidding comparisons

Apply the invariant and source Theorem 11 to N in C with N>=_c0. At (N,0), Right owns the marker, so W_L holds; every follower has optimal zero bids. Consequently N>=_b0 for every b. By role exchange, N<=_c0 implies N<=_b0. If N=_c0, both implications apply, yielding N=_b0. If N>_c0, N>=_b0 and N is strictly >_b0: take X=0 and Left owning the marker, with zero Left chips. The invariant gives outcome L for N and the terminal auction gives R for 0. Thus 0 is not >=_b N. The negative case is symmetric.

In particular A+bar(A)=_b0 for A in C; this inverse conclusion is proved before cancellation is used. Contextual order is preserved under sum simply by replacing X with the sum of the extra summand and X. Addition of an invertible form also reflects order, by adding its inverse. Hence for A,B in C:

A>=_b B iff A+bar(B)>=_b0 iff A>=_c B,

and likewise strict order and equality agree. For the second “iff,” the three classical signs are exhaustive and their bidding signs have just been established. This is not an inference from an outcome table: the non-strict forward signs were lifted by the source's all-context comparison theorem, with its strategy hypothesis proved. A single explicit partition is used only for the necessary strictness witness, after universal weak order is already known.

## Finish the hereditary endpoint

Assume that every follower H of G satisfies A<_b B for each Left option A and Right option B. We show G belongs to C by birthday induction. Every proper option of G inherits the hypothesis, so belongs to C by induction. By the order agreement just proved for C, every pair A<_b B at the root satisfies A<_c B. This is exactly the classical defining separation condition, so G belongs to C. This works equally when either option set is empty; no comparison is required then.

Now every follower H belongs to C, classical Lemma 3.2 gives separately H^L<_c H and H<_c H^R for every existing option, and order agreement transfers BOTH inequalities to bidding contextual order. Thus hereditary separation implies hereditary interpolation, at the originally fixed arbitrary b. This also proves the conclusion when the hypotheses are instead stated uniformly over all b. There is no interchange of fixed-budget premises with uniform-budget premises.

Conversely, hereditary interpolation implies hereditary separation by strict-order transitivity. Directly, A<_b H<_b B gives A<=_b B. If B<=_b A held, it would force H<=_b A by H<=_b B<=_b A, contradicting A<_b H. Therefore not B<=_b A, and A<_b B. This uses only the contextual preorder and the definition of its strict part.

The source and literal record write a joint quantifier over both option sets. If read literally, interpolation is vacuous at one-sided nodes; the forward argument above proves the stronger, separately quantified one-sided inequalities as well. Reverse transitivity is only needed where both options exist. Thus the displayed joint-quantifier equivalence is covered too, without seeking credit from vacuity.

## Audit of r361 and scope limit

R361's reverse transitivity and identification of the missing contextual interpolation lemma are correct. Its failed subtract-an-option route did not establish a strategy on all contexts. The present bridge avoids comparing arbitrary left options by first identifying all proper options as CLASSICAL number forms. Their classical totality and the independently proved zero-bid invariant then supply the missing contextual comparison. Invertibility is derived from the bridge, not assumed for an arbitrary bidding form.

The route does not prove that arbitrary games equal to a classical number retain that equality in bidding, nor that every invertible bidding game is a number. No classical group law is imported on the entire bidding universe. Only classical numeric literal forms and their literal sums/conjugates are transferred.

## Credit and remaining gates

The ordinary bridge above is complete relative to the precisely cited classical results and published source Theorem 11. It is a direct adaptation of those existing results and therefore earns ZERO under the explicit task rule for complete classical/source adaptation. This is a substantive exclusion based on the dependency mechanism, not proof length or superficial similarity. Journal/accepted-version comparison remains incomplete; source fidelity is to arXiv v2, not a claim that the journal retained Conjecture 68. Independent adversarial review and formal execution were not performed. No qualified candidate survives the significance/source gates, so no Pi plan or dispatch is produced. Campaign count remains 52/60.
