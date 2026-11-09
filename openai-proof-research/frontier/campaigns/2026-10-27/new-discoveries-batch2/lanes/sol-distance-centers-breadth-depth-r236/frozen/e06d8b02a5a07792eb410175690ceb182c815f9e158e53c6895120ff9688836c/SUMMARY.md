# Handback: full ordinary proof found; credit 0 pending root gates

2026-10-28 UTC. SOLO, no children. All writes are inside this assigned lane.

**PROOF.md closes the ALL-COEFFICIENT GAP for every r>=1**, for the literal
Definition 2.1 shifted polynomial in u=alpha²-1/4,v=beta²-1/4. Combining it with
the supplied r3 attainment proves the exact full law

    delta_r = 2r + v2((r-1)!).

It actually proves the stronger degree-d statement

    (d-1)! [degree d]J(s_(2r-1)) in 2^(2r-2) Z_(2)[u,v].

The new mechanism is an integral midpoint algebra with
x=(t-t^-1)/2,w=(t+t^-1)/2,w²=1+x²; a=u+v,b=u-v.
After homogeneous scaling, the Riccati recurrence is integral with derivation
partial x=-w², partial w=-wx and potential P=aw²+bwx. Its coefficient at a^i b^j
is divisible by 2^(s2(i)+s2(j)-1). The weighted class is closed under 2fg and
squares; spectral-index pairing proves the assertion for all orders. Odd j
selects the w-odd component and supplies 2^s2(d-1). The primitive has an
odd-unit triangular inverse, so this factor survives midpoint evaluation.
All coordinate denominators, factorials and integration constants are handled
explicitly. No generic shifted-binomial bound or t-termwise bound is assumed.

Independent constructions agree in fixed small diagnostics: normalized midpoint
recurrence/primitive, original Laurent recurrence/primitive, literal source
inverse-factorial cumulants. `python3 check.py` passes, about 55 MiB RSS.
These checks are falsifiers for the written proof, not an all-order substitute.

`LEAN-BRIDGE-PLAN.md` gives the precise literal endpoint and every remaining
formal bridge. `formal/ArithmeticStart.lean` compiles with Lean 4.34.1;
five elementary dyadic arithmetic lemmas use only propext. This is a small
start, **not a complete source certificate**. An initial broad Lean import used
642500 KiB RSS and violated the requested memory ceiling; its failed run is
preserved. Subsequent runs were guarded; final observed RSS was 174220 KiB.

Current primary/companion v2 bodies are byte-identical to the r3 cached HTML.
Fresh registries: openai/math 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a;
trureturing e1b5b0c6ee6c878a2b9a1b2df49f59bac5d6ed37 (23:34:01 UTC).
No matching shifted-law counterpart located in the recorded bounded screen.
Original-variable companion theorem is excluded; MathDB391922 is not the target.
No worldwide-priority claim, independent-review claim, acceptance or count change.

Root next: adversarially review PROOF.md, especially both quadratic pairings and
the normal-form primitive argument, then decide whether to invest in the complete
literal Lean endpoint and remaining novelty/manuscript/packet gates.
