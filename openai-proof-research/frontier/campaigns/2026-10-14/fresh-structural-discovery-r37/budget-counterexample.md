# Counterexample to the proposed same-budget equivariant extension

Author: Myeongjin Kang, no affiliation. Original prose CC BY4.0. This refutes one proposed bridge, not the full RC factor-two approximation target.

Take identity complement on {b,c} and the symmetric input set

S={bbcbbc,bcbbcb,cbbcbb}.

The first and third words are reversals. The middle word is a palindrome. Thus there are only two RC requirements, represented by `bbcbbc` and `bcbbcb`; the redundant third word merely makes the periodic construction transparent. All words have length6. A length6 output can contain only one distinct length6 word, while these two required orientation-orbits are disjoint. Therefore OPT_RC>=7. The word `bbcbbcb` has length7, contains `bbcbbc` as its prefix and `bcbbcb` as its suffix, so

OPT_RC=7.

The symmetric/even forced-count recursion in `counts-and-euler.md` gives:

| length | counts |
|---|---|
|6|m(bbcbbc)=m(cbbcbb)=1; m(bcbbcb)=2|
|5|m(bbcbb)=m(bcbbc)=m(cbbcb)=2|
|4|m(bbcb)=m(bcbb)=m(cbbc)=2|
|3|m(bbc)=m(bcb)=m(cbb)=2|
|2|m(bb)=m(bc)=m(cb)=2|
|1|m(b)=4; m(c)=2|

These are all nonempty substrings. Every row is forced by requirements, the extension inequalities, orbit equality and even rounding at fixed words. For example the required palindrome has count2, the two nonfixed length6 words have count1, and its length5 extensions force the counts shown. At the bottom, m(b)>=m(bb)+m(cb)=4 and m(c)>=m(bc)=2.

For completeness, the source's **entire** period-rule list has13 entries here, including nonleast periods. All have k=1. The trigger is false for (v,p)=(bb,1) and(bcb,2): B_A(v;m)=m(v)=2, although B_A(b;m)=4. The active rules are:

| v | p | shorter w | B_A(w;m) | required lower bound |
|---|---:|---|---:|---:|
|bbcb|3|b|2|4|
|bcbb|3|b|2|4|
|cbbc|3|c|0|2|
|bbcbb|3|bb|0|2|
|bbcbb|4|b|0|2|
|bcbbc|3|bc|0|2|
|cbbcb|3|cb|0|2|
|bbcbbc|3|bbc|0|2|
|bcbbcb|3|bcb|0|2|
|bcbbcb|5|b|0|2|
|cbbcbb|3|cbb|0|2|

Every active rule has B_A(v;m)=0. The displayed counts satisfy all of them. Thus no period rule raises the extension/parity-forced table, proving that this is exactly the proposed recursion, not merely a feasible subsolution. In particular

W_sym=m(b)+m(c)=6<7=OPT_RC.

Suppose the proposed equivariant connection existed for every input, retaining the symmetric base, adding up-cost at most W_sym, remaining balanced and connected to empty, and preserving even outdegree at fixed vertices. Its total up-cost would be at most2W_sym=12. The half-Euler lemma would produce an RC-feasible word of length at most6, contradicting OPT_RC=7. Hence **that same-budget connection statement is false**. This is a general logical refutation with an explicit finite witness; numerical search is not the proof.

The count lower bound W_sym<=2OPT_RC is unaffected; it never implied W_sym>=OPT_RC. The half-Euler graph lemma is unaffected. Nor does this show that no equivariant construction can attain the actual factor-two target: that target allows length14 on this instance, whereas the failed bridge demanded length at most6. A different accounting, augmentation of the initial count system, orientation construction or direct output analysis could still succeed, but requires a new argument.

Discovery protocol: parent requested the necessary-condition test after the earlier geometric checks. `search-budget.py`, seed3737128, tested15,000 random proposals with2–4 words of lengths3–9 over {a,b,c}, finding no counterexample; that bounded negative is not evidence of the bridge. A structured test then took every length-L rotation of periodic texts, starting with A=bbc and L=3,4,5,6. The pairs (W_sym,OPT_RC) were(6,4),(6,5),(6,6),(6,7). The last case above is the first structured failure. `period-budget-counterexample.json` records all orientation/path witnesses, and `period-rule-certificate.json` records every rule. The direct length argument above independently establishes the optimum, and the complete13-rule table establishes the count value.

This supersedes the tentative wording that the same-budget interface was merely unpaid. The full family128 factor-two research target remains unresolved and no candidate, contribution credit or acceptance is claimed.
