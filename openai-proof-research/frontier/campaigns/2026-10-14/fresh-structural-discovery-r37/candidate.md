# Candidate: a factor-two algorithm for reverse-complement superstrings

Myeongjin Kang (no affiliation). Original prose CC BY 4.0. This is an assembled, **unreviewed candidate proof**, not an acceptance, review PASS, publication, or campaign count. It depends on the stipulated ordinary-superstring source at revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The unchanged target was recorded during exploration in `original-scope.txt`, SHA256 `7dfa38dbfdc0298863bbd29c76af27061d9f033cf67aa0800979e3310de1eb60`; that record is not claimed to predate exploration.

## Statement and source dependencies

For every explicitly encoded finite alphabet Sigma, every explicitly encoded involution cm on Sigma, and every finite explicit list S of words, there is a deterministic algorithm polynomial in the full encoded input size that outputs a word containing s or rho(s) for every s in S, where rho reverses a word and applies cm letterwise, and whose length is at most twice the minimum possible length OPT_RC(S). Fixed letters, fixed words, duplicates, substring redundancy, empty words, and the empty input are included. Alphabet labels and cm are not fixed constants. Word length in the guarantee is the number of symbols; complexity charges their full encoded bit lengths.

The stipulated manuscript is `A-Polynomial-Time-2-Approximation-for-Shortest-Common-Superstring-September-24-2026`. We use these exact operations from its `build/sections/` bodies:

* `02-counts.tex`: blocking functional, extension and ordinary period rules; proofs of `lem:counts` and `lem:base`.
* `03-layers.tex`: `lem:recorded`, `lem:layers`, `lem:matching-window`, `lem:agreement`, and `lem:max-rotation`.
* `04-connections.tex`: `lem:ordered-windows`, `lem:band`, the proof of `lem:collective` (in its geometric form below), and `lem:host`.
* `05-processing.tex`: ordinary group partition and its individual-link/request inequalities, used on nonself text orbits.
* `06-cycles.tex`: the geometric short-contact construction, generalized to odd cores below; we do not assume its one-sided cycle bookkeeping is equivariant.
* `07-algorithm.tex`: finite record search and the suffix invariant for extracting the output.

These operations depend on the displayed count inequalities and the resulting balanced graph, not on choosing the smallest ordinary counts. The extra symmetric constraints below preserve every ordinary inequality. The new work is the strengthened self-text rule, phase-specific parity and adjacent pairing, odd-core group processing, spliced/anchored hosts with request reclassification, symmetric quotient-cycle opening, and the half-Euler extraction. None of these new interfaces is asserted to follow merely by relabeling an ordinary input.

## 1. Symmetric counts dominated by two tagged texts

Remove empty requirements. Group the remaining words into rho-orbits and discard any orbit contained as a substring in a different larger orbit. This preserves feasibility: containment is reversed by rho, so either orientation of the larger word satisfies one orientation of the smaller. If no requirements remain, output empty. Otherwise let R contain both orientations of the surviving orbits, and let V contain all their substrings, including empty. V is rho-closed; every required word is maximal in V. Write L for the total length of one representative of each surviving orbit, bounded by the input size.

For a periodic text A with s=A[0:|s|), let b_A,s(r) count placements of s in r whose matching interior is bracketed by one mismatching letter at each end, as in the source, and B_A(s;m)=sum_r b_A,s(r)m(r). Only |r|>=|s|+2 contribute. It counts blocked recorded occurrences; a nearest-mismatch bracket is unique.

Define integer counts m in decreasing word length and simultaneously on rho-orbits. Missing words have count zero. Impose both extension inequalities m(s)>=sum_c m(cs),sum_c m(sc). Required nonfixed words receive at least1; fixed required words receive at least2. For v=A[0:h), w=A[0:h-kp), k>=1 and w nonempty, impose the implication

    m(v)>B_A(v;m) => m(w)>=B_A(w;m)+g(A,v,k),

where g=k+1 normally, g=2k+1 if the periodic text A is reverse-complement equal to a translate of itself, The actual algorithm uses precisely these two cases: g=2k+1 for self-reversed periodic texts and g=k+1 otherwise. The stronger fixed-word variant from the earlier note is not included in this algorithm or its new diagnostic. Take the maximum of all bounds for both words of an orbit and assign it to both; at a fixed word round upward to even. All terms are already determined from longer words. Enumerate v, positive p<|v| that is a period of v, and k with kp<|v|; test that repeating the first p letters agrees with all of v before retaining the rule. A is specified by its first p letters. Thus this is a finite explicit recursion, including nonleast periods.

**Count lemma.** For every feasible T, m(s)<=N(s):=N_T(s)+N_rho(T)(s), and W:=sum_letters m(a)<=2|T|. In particular W<=2OPT_RC and m(s)<=2L.

Proof. Regard T and rho(T) as two distinct tagged text components, even when they are identical words. N is symmetric and even at fixed words. Extension and required bounds hold. Descending induction for ordinary period rules is the source occurrence proof applied to a disjoint collection: either an unblocked v gives k+1 distinct unblocked w occurrences, or a positive longer-word difference in a blocking sum gives k+1 multiplicities. Linearity permits summing over the two components.

For a self-reversed periodic text, choose delta in {0,...,p-1} so that rho(v), viewed at its translated phase in A, contains w at offsets delta,delta+p,...,delta+(k-1)p. These k copies fit because their last start is at most kp-1 and |v|-|w|=kp. The original v has k+1 copies at offsets0,p,...,kp.

If N(v)>B_A(v;N), choose an unblocked v. Its k+1 internal copies are unblocked. Reflect the occurrence into the other tagged component; the k indicated copies in rho(v) are unblocked too. Indeed, a mismatch bracket around any such copy must surround the entire matching rho(v) interval. Its reflection belongs to V and would block the original v. The two tagged components make the contributions distinct. Hence N(w)-B_A(w;N)>=2k+1.

In the other case N(v)=B_A(v;N)>=m(v)>B_A(v;m). Set Delta(r)=N(r)-m(r) for longer r. Some r has b_A,v(r)>0 and Delta(r)>0. Its selected bracketing placement contains k+1 counted w placements. The reflected bracket in rho(r) contains at least k of the shifted-phase w placements. If r is nonfixed, its symmetric partner has the same positive Delta, so their total contribution to B_A(w;N)-B_A(w;m) is at least2k+1. If r is fixed, Delta(r) is even and positive, hence at least2; the original k+1 placements suffice. This proves domination of the new rule.

Separately, the earlier fixed-v2k+2 variant is also dominated by N, as proved in `strengthened-fixed-rule.md`, but it is not used here. Finally orbit maxima and even rounding preserve domination because N has the same symmetry and evenness. Summing letter counts proves the bound on W; concatenating input representatives gives m(s)<=2L. This proof covers arbitrary cm, including fixed letters. ∎

## 2. Base graph, paired walks, and phase parity

Use the source hierarchical graph on V. An up edge pref(s)->s has multiplicity u(s)=m(s)-sum_c m(cs); a down edge s->suf(s) has d(s)=m(s)-sum_c m(sc). These are nonnegative. The graph G is balanced, uses every required vertex, and has W up and W down edges by the source telescoping proof. Pair copies so that the edge-reversing involution tau maps the up edge at s to the down edge at rho(s). It has no fixed edge.

At a nonempty fixed word s, outdegree is m(s)-sum_c,d m(csd), an even number: the extension words pair under rho and fixed extension words have even counts. At empty the outdegree is sum_a u(a)=sum_|s|=1 m(s)-sum_|s|=2 m(s), also even by the same whole-length orbit sum. This is not W, which counts all up edges. Adding any closed walk C and its reversed image tau(C) preserves balance, symmetry, and even fixed-vertex outdegrees.

Construct a tau-paired closed-walk decomposition of G. At each nonfixed vertex pair incoming and outgoing copies arbitrarily and force the reversed pairing at its partner. At a fixed vertex pair outgoing copies by a fixed-point-free involution; after identifying incoming copies with reversals of outgoing copies this gives the transition matching. Every resulting edge cycle has a distinct reversed partner. A reversal-fixed cycle would induce a reflection of its cyclic edge order, forcing a fixed edge or a fixed transition, both excluded. The construction is finite and deterministic with fixed tie orders.

Lift the walks to windows [x,e) in periodic texts as in the source. Up increases e; down increases x. A turn with P up edges translates by (P,P). Group by periodic text up to translation, reduce to least period p, and sort primitive passages using their exit-end multisets. Each sorted layer has exits z(x), entries f(x)=z(x-1), lasts l(x)=z(x), with z(x+p)=z(x)+p; at start x it visits all windows [x,e) with f(x)<=e<=l(x). Sorting preserves every labelled phase edge and every recorded occurrence count. Layers have period budget p; their budgets sum to W.

For a nonself orbit of periodic texts, reflection pairs the sorted layers in their order. Choose the canonical text to be the lexicographically greatest forward rotation among BOTH orientations; use its sorted layers as representatives. A basic paired unit consists of one representative layer and its reflected layer, budget2p.

For a self-reversed primitive text, choose a reflection R(x,e)=(c-e,c-x), where cm(A(j))=A(c-1-j). The group has an even number of primitive passages because the original walks came in reversed pairs. Reflection preserves the order of staircase profiles: its inverse-coordinate reflection sends upper regions to upper regions. The ordered decomposition is unique from the exit multisets. Therefore each sorted profile is individually fixed under R, although profiles need not occur with even multiplicity.

The stronger fact needed is phase-specific parity. At a fixed-alignment word w=A[t:t+l) with 2t+l congruent to c modulo p, reflection pairs occurrences at this phase on the paired original walks. Their count is even. Sorting preserves it: the count equals the number of normalized exits z_i(t)>=t+l. This uses the EXIT convention, since a window containing the occurrence exists exactly when the exit at its start reaches its end. It is not a claim derived from the aggregate m(w) alone.

Pair adjacent sorted layers from the top. At any reflection-axis vertex visited by the upper member, the even upper-tail count implies that its lower partner records that same fixed word. The lower entry is at most the upper entry, so the lower member actually visits the same vertex. Removing these top two layers preserves every fixed-phase even tail, since their indicators agree; induction handles all adjacent pairs. Each pair shares BOTH axis vertices in a primitive turn: x+e increases by one at every step and by2p per turn, so it crosses the two residues x+e=c and c+p modulo2p. An empty-word crossing already roots the pair and is also a valid shared vertex. The two profiles may otherwise differ. Thus every self pair is already connected and has budget2p.

For later hosts, splice a self pair D1,D2 at its two shared axis vertices U,V. Let E follow D1 from U to V and D2 from V to U+(p,p); let F use the opposite choices. E,F are valid period-p staircase walks, each with p up edges, their labelled union equals D1+D2, and tau exchanges them. Reflection reverses the two half-period arcs between fixed axes. Coincident profiles are handled with labelled copies. Use E,F only for hosting; keep the sorted profiles for band geometry.

## 3. Source geometric operations in the needed form

A record is an actual window on a target layer with an alignment agreeing with the source periodic text. The source matching-window lemma gives such a record from each unblocked occurrence. Distinct aligned texts of periods p,q agree for fewer than p+q letters; if their periods are equal p, they agree for fewer than p letters, including when they are opposite orientations.

The source ordered-window operation follows windows whose starts and ends are nondecreasing at cost equal to total end increase, using only prefixes/suffixes and single letters in V. A list returning to a period translate by K closes at cost K. A band with top first end H and bottom last end E at t can be joined for any nonnegative multiple K of p with H-E<=K.

The geometric collective operation is valid for ANY number of ordered layers, provided K is a multiple of p and, at record R=[a,b),

    r_H<=b+K, r_H-r_L<=K, r_L+K>=b.

Indeed Y=max(b,r_H) lies in [b,b+K]. Every layer meets height Y at an ordered start in [a,a+K]. Following R, these actual windows, and R+K gives a cost-K closed walk. The proof does not require K to equal the number of layers times p. This is why an odd core can consume a paired block's half-budget below.

The individual operation assumes f_i(a)<=b. If some vertex length is <=p, root it for cost p. Otherwise, if l_i(a)+p>=b, choose an actual window [a+p,e') with b<=e'<=b+p and follow R,[a+p,e'),R+p. This cost-p loop touches the layer and a word of length at most max(0,b-a-p)<q. Otherwise [a,f_i(a)) is a host request with a+p<f_i(a)<=l_i(a)<b-p. Since |R|<p+q, requests have q>p.

The source host lemma applies to one actual period-q monotone path, with one record per distinct child text group. Requester windows [a_i,e) satisfy a_i+p_i<e<=b_i-p_i. Its proof orders records on that path, chooses a child of least period, and uses the q-cost host excursion through clamped contacts plus the other child budgets; one unspent least-child budget roots a short contact. Only a valid period-q path is required, so a spliced E is eligible. We apply it only after the following routing repair ensures its exact hypotheses.

## 4. Hosting paired units

Process primitive-text ORBITS in increasing least period. Requests reserve entire paired-unit budgets and always go to a larger period. For a nonself recipient layer pair use its two exchanged layers E,F. For a self recipient pair use its spliced E,F. If it receives requests, select one original request and name E so its original record lies on E. Keep that child orbit's request batch unflipped. For each other child orbit, all requests use one record; if it lies only on F, reflect the entire batch so its record lies on E. Distinct child orbits remain distinct primitive texts and all have smaller periods.

A reflected left-anchored requester need not be left-anchored. At its new record R'=[a',b'), its reflected actual window is [u,b') contained in R'. Monotonicity implies f(a')<=b'. Reapply the three individual cases. Case1 roots its unit by a loop and its mirror. Case2 reserves a link to R' and its mirror to be executed AFTER the host is rooted. Case3 gives exactly the left-anchored host inequality. The unchanged selected batch still has at least one genuine case3 request.

Apply the source host lemma once to E and the remaining case3 requests, then mirror the entire resulting construction on F. The cost is at most2q plus their requester-unit budgets. Both E and F, hence the entire recipient pair, are rooted. Execute case2 attachments using their own2p budgets. These are immediate attachments to a rooted host, not new outgoing plans in a noncanonical phase. All original request units are now rooted. For a self child unit its two members already meet, so touching the selected member roots both; for a nonself unit the mirrored construction handles its other member.

One original anchor record on the recipient pair has length<q+p<2q. It need not lie on the higher sorted member. Choose the highest recipient PAIR as baseline pair. Its upper member bounds the available upper region and is used for subsequent band tests. For all unspent pairs below it, use the actual short record on whichever member contains it for the ordinary lower-link construction, then reflect. Each such pair lies below that member, so the source inequalities apply and cost at most its2q budget. Both baseline members are already rooted; the two roles need not use the same vertex.

## 5. Processing unspent upper units

For a nonself text orbit, run the source ordinary upper-group procedure on the canonical representative layers and mirror every resulting operation. Incoming rooted pair indices agree under reflection. Source easy branches, threshold, collective links, individual cases, and requests therefore use disjoint paired budgets. Each ordinary collective block of k layers together with its reflected block is a quotient unit of budget2kp. Its two components can be internally joined separately for at most2(k-1)p, freeing2p. The canonical orientation is fixed independently of incoming-host orientation choices.

For a self text group, the available upper layers form2r layers in adjacent pairs. Let t be its maximal forward phase and H=f_top(t). If H-t<=rp, an ordinary root excursion through [t,H), plus its mirror, roots all upper layers at cost<=2rp. If a rooted baseline has l_base(t)>=H-rp, a width-rp band plus its mirror does the same. Otherwise

    H>t+rp; and l_base(t)<H-rp when a baseline exists.

Choose the first k with #{i:l_i(t)>=H-kp}<=2k, counting the whole group. It stops by r because no layer at/below baseline qualifies. At the preceding failed threshold there were at least2k-1 qualifying layers. Thus the CORE of the top2k-1 layers has bottom last end at least H-(k-1)p; for k=1 the top layer itself gives this. Translating x into (t-p,t] gives f_top(x)-l_corebottom(x)<=kp everywhere. The full block consists of top2k layers; its final member meets layer2k-1 at the fixed-axis vertex.

The top actual vertex v=A[t:H) is unblocked relative to its own text. The strengthened rule gives2k+1 unblocked occurrences of w=A[t:H-kp), but at most2k have identical full-text alignment. Select a different-alignment record R=[a,b) containing that interval. Then a<=t, b>=H-kp, and |R|<p+q. Put K=kp. The core satisfies r_H-r_L<=K and r_H<=H<=b+K. If also r_L+K>=b, use the geometric collective loop on the odd core, cost K, plus its mirror. This connects the whole2k-layer unit within budget2kp. Alternatively the sharp core band and its mirror join it internally for at most2(k-1)p, freeing2p.

If the collective test fails, r_H<=r_L+K<b, so all upper first ends at a are <=b. If it succeeds, each remaining layer below the top2k has l_i(t)<H-K<=b and hence f_i(a)<=b. Treat each remaining adjacent pair by the upper member's individual cases, then mirror. Roots and links cost<=2p; otherwise reserve a2p request. All choices use the ONE selected record for this child text orbit. Requests go to q>p. Removal or expenditure is always by full pairs, preserving phase parity and the pair boundary for the next use.

After all groups, every basic pair is either marked rooted or in one outgoing quotient unit; reserved outgoing budgets are disjoint. Every unit targets one actual layer and its reflected partner, which belong to a quotient unit or to rooted material. Requests have all been fulfilled because their periods strictly increased.

## 6. Symmetric opening of quotient cycles

Form the functional digraph of outgoing quotient units. A nonself unit has two possibly disjoint ports, its representative and reflected block. A self unit is already connected internally once its core is joined, so its conceptual ports coincide. A pair of planned links attaches the source ports to corresponding target ports, possibly with a swap. Thus a path of quotient units lifts to paths each reaching a port at its endpoint. A twisted lift need not split into two disjoint cycles; the following argument does not require that.

For a quotient selfloop, target and source have equal period p and different aligned text. Therefore |R|<p even if the target is the source's opposite orientation. Omit both planned links, join the unit internally, freeing2p, and root R and rho(R) at cost2|R|<2p. Both ports are rooted.

For a cycle of length>=2 select a unit whose CANONICAL distinguished forward text is lexicographically greatest. Every forward rotation of either target orientation is at most the target canonical text and hence at most this source. Let q be the target period. The selected original plan has a contact of length<=q: this is immediate for an individual link. For a collective plan, apply the source cycle-contact proof to the representative block or the odd core. If a constituent already has a vertex of length<=q it suffices. Otherwise the maximal-rotation lemma gives b-t<q. Set x=min(t,a+K); then b-x<q. All constituent first ends at x exceed b and are at most H. With F=f_top(x)<=H<=b+K, the ordered list

    [a,b), [x,b), [x,F), [a+K,b+K)

has cost K, touches all constituents, and contains the short suffix [x,b). The last paired self layer is connected through its core partner. Reflect this link to obtain its partner and the reflected short contact within the reserved paired budget.

Retain these selected links. Omit the TARGET unit's outgoing pair and join that unit internally, freeing2q. Root the two short contacts at cost<=2q. The quotient cycle minus the omitted edge is a path ending at the target; every lifted component meets one of the retained contact pieces and is rooted. This covers both twisted and untwisted lifts and mixed self/nonself cycles. Distinct cycles have disjoint budgets. Execute other links toward rooted sinks/opened cycles in increasing distance order. Every layer is rooted.

All additions are closed walks paired with their reflections. Their total up cost is at most W, the sum of the original layer budgets. The final graph D is balanced, connected to empty, tau-invariant, and has even outdegree at every fixed vertex. Its total up cost U is at most2W.

## 7. Half-Euler extraction and complexity

We use the following elementary graph lemma. A finite balanced directed multigraph with a reversing edge-copy involution, no fixed edge, connected support, a fixed root, and even outdegree at every fixed vertex has a directed closed walk from that root using exactly one edge from each involution pair.

To prove it, quotient vertices and edges by the involution, retaining both incidences of loops. At a nonfixed vertex orbit choose a representative; label an incidence positive when its compatible lift is outgoing there and negative when incoming there. Balance gives equal positive and negative incidence counts. At a fixed vertex the quotient degree equals its directed outdegree and is even. Pair opposite signs at nonfixed vertices and arbitrary incidences at fixed vertices. These pairings decompose quotient edges into closed alternating trails. Such a trail lifts consistently: opposite signs match the directed arrival/departure state at a nonfixed orbit, while a fixed vertex permits either state. Closure follows from the paired final/initial incidences. If several trails remain, connectedness gives a shared vertex; cross-switch two incidence pairs there to splice trails, preserving the allowed pairings. Iterate and lift the final Euler trail from the fixed root. This construction is polynomial.

Apply it to D rooted at empty. There are U edge orbits because D has U up and U down edges. The lifted closed walk uses U edges, half up and half down since every edge changes word length by one. It visits one representative of every used vertex orbit, hence one orientation of every required word. Append letters at its up steps. The source suffix invariant shows each visited word is a substring of this output. Its length is U/2<=W<=2OPT_RC.

For complexity, |V|=O(L^2) with word lengths<=L, and every count is<=2L. Period, reflection-up-to-rotation, blocking, and orbit bounds are explicitly enumerable in polynomial time. The base graph has2W<=4L edge copies. Paired transitions, period reduction, sorted passages, axis crossings, and splices are finite scans; the total number of layer phases is W. Equality and lexicographic comparison of periodic texts use at most the sum of their periods by the source agreement lemma. A different-alignment record is found by enumerating actual windows and placements, exactly as in the source finite search. Coordinate normalization keeps all integers of polynomial bit length. Pair thresholds, host reclassification, functional-graph cycles, and the half-Euler construction are polynomial operations. The final graph has2U<=4W<=8L explicit edge copies. All finite choices use encoded-symbol order and stable IDs; no randomness or unbounded-label unit-cost assumption is used. Unused alphabet symbols may be ignored after reading the explicit alphabet and involution; all symbols in required words and their partners are retained. ∎

## Status, chronology, and limits

The initial unstrengthened symmetric recursion was disproved as a universal same-budget bridge by W=6<OPT_RC=7. That exact counterexample remains in `budget-counterexample.md`; it is not a counterexample to the stronger recursion used here. The first fixed-word-only repair left an axis/lexmax mismatch; the self-text2k+1 rule resolves that mismatch in the proposed proof by processing at the actual lexmax phase. Distinct sorted fixed profiles remain possible and are handled by shared-axis pairing and splicing, not assumed to be duplicates.

This proof is offered for independent validation. No complete executable implementation of the approximation algorithm, full Lean formalization, independent proof PASS, contribution PASS, manuscript PASS, or literature-wide novelty result is claimed. The precise primary-operation and history reading limits from r36 remain applicable; inherited bytes/hashes are provenance, not a new complete primary reading. A candidate nomination requires the parent to complete its separate gates.
