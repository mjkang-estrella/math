# Self-reversed periodic texts, odd cores, and spliced hosts

Author: Myeongjin Kang, no affiliation. Original prose CC BY 4.0. These are new deductions proposed jointly in the parent/worker discussion, not upstream statements and not independently reviewed. The initial recurrence counterexample remains valid for that initial recurrence. The new rule below is a further repair, beyond the fixed-word rule in `strengthened-fixed-rule.md`.

## A count rule at every phase of a self-reversed text

Let A be a periodic text of period p whose reverse-complement is a translate of A. For v=A[0:h), w=A[0:h-kp), with k>=1 and w nonempty, impose

    m(v)>B_A(v;m) => m(w)>=B_A(w;m)+2k+1.

Keep the ordinary rules for other texts, symmetry, fixed-word evenness, and required counts. The stronger 2k+2 bound for fixed v proved in the earlier note may also be retained. The new rule does not require v itself to be fixed. It therefore applies at the lexicographically greatest forward phase needed for cycle opening.

Here is a domination proof. Work with the disjoint TAGGED pair of texts T and rho(T) and N(s)=N_T(s)+N_rho(T)(s). Suppose longer counts have been dominated. Since rho(A) is a translate, there is a phase offset delta in {0,...,p-1} such that rho(v) contains copies of w starting at delta,delta+p,...,delta+(k-1)p. All fit: the last start is at most kp-1, whereas |rho(v)|-|w|=kp. The original v contains the k+1 copies at starts0,p,...,kp.

If there is an unblocked v occurrence in the tagged texts, its k+1 internal copies of w are unblocked, by the source nearest-mismatch bracketing argument. Reflect that occurrence into the other tagged component. Its periodic matching interval is a shifted A interval. The k indicated w occurrences inside it are also unblocked: a nearest-mismatch bracket around any of them would bracket the entire matching rho(v) interval and, after reflection, would block the original v. The two tagged components make these contributions disjoint even if the two component words are equal. Thus N(w)-B_A(w;N)>=2k+1.

Otherwise N(v)=B_A(v;N)>=m(v)>B_A(v;m). Let Delta(r)=N(r)-m(r) on longer bracketing words. Delta is nonnegative and symmetric, and is even at fixed words. Choose r with b_A,v(r)>0 and Delta(r)>0. A bracketing placement of v gives k+1 distinct bracketing placements of w in r. Reflect its matching interior and mismatching endpoints into rho(r); the phase offset construction gives at least k distinct bracketing placements of w in rho(r). If r is nonfixed, the pair contributes at least (2k+1)Delta(r)>=2k+1 to B_A(w;N)-B_A(w;m). If r is fixed, Delta(r)>=2 and the original k+1 placements already give at least2k+2. All other contributions are nonnegative. This proves the new bound is dominated by N in both cases.

Maximizing the bounds across each rho-orbit and rounding fixed counts up to even still preserves domination. Consequently m(s)<=N(s), W<=2OPT_RC, and m(s)<=2L, where L is the total input length. A primitive-period test and a test of equality up to rotation with reverse-complement are polynomial. The number and bit lengths of the finite descending constraints remain polynomial. This proof does not infer W>=OPT_RC from finite tests.

## Processing at the maximal phase using an odd core

Use the adjacent sorted-layer pairs proved in `folded-threshold.md`. A self-reversed group has 2r currently available upper layers, grouped into r connected pairs. Each pair has budget2p. Let t be the maximal forward rotation phase and H=f_top(t), with the source ENTER convention. This is now an arbitrary word phase; no fixed-axis assumption is needed.

The easy upper root branch uses an ordinary excursion of cost at most rp when H-t<=rp and adds its mirror, spending at most2rp. The easy baseline band similarly uses width rp and its mirror. If both fail, H>t+rp and any baseline satisfies l_base(t)<H-rp.

Choose the first k with #{layers i: l_i(t)>=H-kp}<=2k. The search stops by r. The previous failed test supplies at least2k-1 layers above H-(k-1)p. For k=1 the top layer alone supplies this inequality. Hence the CORE of the top2k-1 layers has sharp band (k-1)p and wide band K=kp, exactly by the source translation argument. Form a unit using all top2k layers: the final layer shares a fixed-axis vertex with layer2k-1, so connecting the core connects the whole unit. The pair boundary is preserved.

The new rule supplies2k+1 unblocked occurrences of w=A[t:H-kp), but at most2k have identical full-text alignment. Choose one different-alignment record R=[a,b) by the source matching-window lemma. The source collective proof, applied to the odd core with budget K, uses only its three geometric inequalities, not its cardinality. A cost-K link and its mirror therefore connect the whole2k-layer unit at total cost2kp. The core can instead be internally joined by a cost-(k-1)p band and its mirror, freeing2p from the unit budget. For k=1 the pair is already connected and no internal addition is needed.

If the collective test fails, all upper layers have first end at a at most b. Outside a successful top2k unit, the stopping rule gives the same fact. Treat each remaining adjacent pair using its upper member's individual test. A root or link of cost p, plus its mirror, pays the pair's2p budget because the two members already meet. Otherwise reserve a request for that pair. Request periods strictly increase by the source agreement bound. All units in this group use the one chosen record. This paragraph does not by itself settle host routing or global cycles; the following construction addresses the former.

## Splicing a recipient pair into exchanged host walks

Let D1,D2 be adjacent sorted layers in a self-reversed group of period q. The phase-labelled parity argument gives shared vertices U,V at both reflection-axis residues in a primitive turn. Lift them so U precedes V precedes U+(q,q). Form

    E = D1[U,V] followed by D2[V,U+(q,q)],
    F = D2[U,V] followed by D1[V,U+(q,q)].

Each is a valid increasing window staircase, periodic under (q,q), with q up steps and q down steps. Their union as labelled edges equals D1+D2. Reflection reverses each interval between the two axes and exchanges the two splicings, so tau(E)=F. This holds for coinciding profiles by retaining edge-copy labels. No sorted-profile duplication is assumed. The sorted pair remains available for bands and odd-core geometry; E,F are used only as recipient host walks. Every actual record on the pair is on E or F (possibly both at a splice), and its reflection is on the other walk.

Suppose this pair receives requests. Choose one original request and choose the name E so that its original record lies on E. This guarantees at least one genuine unchanged left-anchored request remains. For each other CHILD ORBIT, all its requests use one record. If that record lies only on F, reflect that entire child's request batch so the reflected record lies on E. Different child orbits still have distinct primitive texts, all of smaller period than q.

Reflection turns a left-anchored requester window into a right-anchored window, so the source host lemma must NOT be applied without repair. At the reflected record R'=[a',b'), the reflected requester has an actual contained window [u,b'); hence its first end f(a') is at most b', by monotonicity. Reapply the source individual cases to the reflected requester:

1. A vertex of length at most p permits immediate rooting by a p-cost excursion and its mirror.
2. Otherwise, if l(a')+p>=b', use the ordinary p-cost link to R' and its mirror, but execute it AFTER the host is rooted.
3. Otherwise a'+p<f(a')<=l(a')<b'-p, which is exactly a valid left-anchored host request.

A self-reversed requester unit uses one of its paired layers; its other layer is connected through the fixed-axis contact. A nonself requester unit consists of exchanged layers, so reflecting swaps its two members. In either case the total reserved budget is2p. Case2 links are NOT inserted as new outgoing plans in a flipped, potentially noncanonical orientation. They attach directly to the host once it is rooted, so they cannot invalidate maximal-phase cycle selection.

At least the originally selected request remains in case3 without any flip. Apply the source host lemma ONCE to the actual monotone host walk E and the remaining valid case3 requests, then add its mirror on F. This costs at most2q plus the sum of the remaining requester-unit budgets. E and F, hence both sorted recipient layers, are rooted. Execute the case2 attachments using only their own reserved budgets; case1 units were already rooted. Thus every original request unit and the recipient pair are rooted within their combined budgets. The source host ordering proof applies because all chosen records now lie on one actual path E, so both starts and ends have the required order. It does not apply to an arbitrary mixture of records on the two original sorted profiles.

The recipient pair has an actual short record of length<q+p<2q on one member. For lower-pair attachments use that member's short vertex; it need not be the upper member. The highest rooted recipient PAIR determines the upper-region pair boundary. The upper member is a rooted baseline for band tests, whereas either member's short record may serve the lower attachment operation. These are distinct roles and need not be the same vertex.

Status: these are candidate local proofs, awaiting the global invariant and independent review. No full theorem, acceptance, review PASS, or campaign count is claimed here.
