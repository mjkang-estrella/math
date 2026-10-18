# A strengthened rule at reversal-fixed periodic words

Author: Myeongjin Kang, no affiliation. Original prose CC BY4.0. The parent proposed this repair after the initial same-budget counterexample and supplied the reflection/coefficient argument. This is a technical count-interface repair, not a full RC approximation theorem.

Preserve the original recursion and its counterexample as separate, immutable mathematical claims. Define a new recursion by replacing the source period implication, only when v=rho(v), with

m(v)>B_A(v;m) implies m(w)>=B_A(w;m)+2(k+1),

where v=A[0:|v|), w is its nonempty prefix, |v|-|w|=kp, and p<|v|. Continue to take the maximum of all constraints on both words of a rho-orbit, and round fixed-word counts to even. Nonfixed-v rules retain k+1. This is implemented by `fixed_boost=True`; the default in the saved exploration code remains the initial unstrengthened recurrence, so its prior certificates keep their meanings.

## Reflection identity

Because v is fixed and has period p, the periodic text satisfies

cm(A(u))=A(|v|-1-u) for every integer u.

It suffices to check one full set of p residues inside v, where this is precisely fixedness of v. Since |v|-|w| is a multiple of p, the same identity holds with |w| in place of |v|. In particular w is fixed too.

For s=v or w, reversal maps a bracketing placement j of s in r to the placement

j'=|r|-|s|-j

of s in rho(r). The bounds on j, matching interior and the two mismatching endpoint conditions all correspond under the displayed reflection. Thus

b_A,s(rho(r))=b_A,s(r)

for s=v,w, with multiplicity. This includes fixed r, where placements may themselves be fixed or paired.

## Domination by the disjoint pair of texts

Let N(s)=N_T(s)+N_rho(T)(s), as in the original count proof. Suppose descending induction gives m(r)<=N(r) on longer words. The original extension and nonfixed-v period bounds remain dominated by N. For the stronger bound there are two cases.

If N(v)>B_A(v;N), choose an unblocked v occurrence. Reflect it into the other **tagged** text component. The two occurrences are distinct even when T=rho(T) as words. The reflection identity preserves unblockedness. In each occurrence the k+1 period-spaced prefixes w are distinct and unblocked; between the two tagged components they are disjoint. Hence N(w)>=B_A(w;N)+2(k+1)>=B_A(w;m)+2(k+1).

Otherwise N(v)=B_A(v;N)>=m(v)>B_A(v;m). Put Delta(r)=N(r)-m(r) on longer words. These nonnegative integers are symmetric. At a fixed r they are even, since N and m are both even there. Some bracketing word r with b_A,v(r)>0 has Delta(r)>0. The source placement argument gives b_A,w(r)>=k+1. If r is nonfixed, its partner has equal coefficient and equal positive difference, contributing at least2(k+1) to B_A(w;N)-B_A(w;m). If r is fixed, Delta(r)>=2 gives the same contribution. All other terms are nonnegative. Thus N(w)>=B_A(w;N)>=B_A(w;m)+2(k+1).

All imposed bounds are therefore dominated by N. Maximum across an orbit and even rounding preserve domination exactly as before. The strengthened recursion satisfies

m(s)<=N_T(s)+N_T(rho(s)),
W_strong<=2OPT_RC,
and m(s)<=2L.

Its number of rules and integer bit lengths remain polynomial in the fully encoded input size. These statements concern the new recursion only. They do not prove the connection theorem or any lower bound W_strong>=OPT_RC.

## Exact test of the original counterexample

For S={bbcbbc,bcbbcb,cbbcbb}, the required fixed word v=bcbbcb has period3. Its fixed prefix w=bcb now receives lower bound4 instead of2. The resulting counts are:

m(b)=8, m(c)=4;
m(bb)=m(bc)=m(cb)=4;
m(bbc)=m(cbb)=2, m(bcb)=4;
all length4 and length5 counts remain2;
the length6 counts remain1,2,1.

Thus W_strong=12, while OPT_RC=7. The old W_sym6<OPT7 obstruction no longer applies. `strengthened-old-instance.json` saves the complete exact data.

`strong-periodic-search.json` records48 structured cases: all length-L rotations of each periodic text in {bbc,abba,abcba,abccba,aababb}, for p<=L<3p, stopped at no failure. None had W_strong<OPT_RC. This is a bounded diagnostic, not proof of a universal inequality. The15,000-case negative random search in `budget-search.json` concerned the weaker recurrence; it must not be presented as a separate direct run of the strengthened algorithm.

## Remaining construction

The stronger fixed-word period rule plausibly supplies the paired occurrence surplus needed at a reflection-axis word on a self-reversed layer. The corresponding half-period group/host/cycle construction has not been established. One must still prove the monotone contact order, membership in V, actual fixed-layer block charges and global disjointness of budgets. Earlier profile and per-layer link examples remain warnings about those steps; they are not counterexamples to every possible strengthened construction.

Current disposition: initial count/budget bridge refuted; strengthened count domination proved in this note subject to independent review; **full factor-two RC target unresolved**. No new candidate, acceptance, novelty claim or full formalization.
