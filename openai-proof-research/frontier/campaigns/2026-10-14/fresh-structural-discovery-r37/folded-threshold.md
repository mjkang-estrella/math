# Adjacent-layer pairing and a conditional doubled threshold

Author: Myeongjin Kang, no affiliation. Original prose CC BY4.0. These are supporting local arguments in the strengthened-count investigation. Parent independently supplied the reflection-axis pairing formulation and doubled-threshold idea. No full connection algorithm is claimed.

## Sorting and phase parity

Start with the tau-paired closed walks constructed in `connection-interface.md`. Fix a self-reversed primitive text A of period p, align its walks, and write its reflection as R(x,e)=(c-e,c-x) in window coordinates. The union of lifted, phase-labeled edges is invariant under R. Reflection reverses traversal and interchanges up/down edges, so its reflected paths are again increasing staircase paths.

Pointwise order of staircase profiles is preserved by R. One way to see this is to describe a staircase by its upper region; R exchanges coordinates and negates both, so it sends that upper region to the upper region of the reflected staircase. Thus reflecting an ordered decomposition preserves its order. The ordered decomposition is unique as a multiset: at every integer x its exit-end multiset is prescribed by the down edges, and the kth profile is the kth order statistic. Therefore the sorted profile multiset is R-invariant and each ordered profile is itself fixed, although identical copies need not have individually specified identities. No conclusion about even multiplicity of a profile follows.

Now fix a nonempty fixed word w=A[t:t+l) whose template reflection agrees with R modulo period. On each pair of original walks, reflection pairs recorded occurrences at this specified full-text alignment. It has no fixed walk, so the total count is even. Sorting preserves this phase-specific count: it equals the number of exit ends at the specified start at least t+l, and sorting does not alter that multiset. In particular

#{i : z_i(t)>=t+l} is even

for each such fixed-word threshold. This is a phase-labeled statement. The aggregate m(w) alone would not establish it when a short word occurs in several phases.

The sorted profiles can consequently be removed in adjacent pairs from the top. Whenever the highest remaining profile records a fixed word at one of its reflection-axis vertices, the next profile also records it by evenness of the threshold tail. Because the next profile's entering end is at most that of the top profile, both actually visit that vertex. More generally, at every fixed-word threshold the top two indicators coincide: a nonzero even upper tail has size at least2. Removing the pair therefore preserves all phase-specific even tails. Repeat down the ordered group. Each pair is already connected through its actual fixed-axis vertex or vertices, despite possibly having different profiles.

For the existence of axis vertices, x+e increases by one along every step and by2p per primitive turn. Fixedness modulo a period translate means x+e=c+jp. Hence the layer passes through the two reflection-axis residue classes at actual integer vertices. If one crossing gives the empty word, that pair is already rooted. This handles the empty-word exception without using occurrence counts of empty. Nonempty crossings supply the fixed words used above.

This argument should receive independent checking before being used as a full algorithm interface. It is stronger than the false identical-profile pairing assertion and is consistent with both exact profile certificates.

## Local doubled threshold

Suppose a self-reversed group is processed in such adjacent pairs and the currently available upper region consists of n=2r layers. Any lower baseline is assumed already rooted, with a compatible pair boundary; establishing that invariant across all host operations remains part of the global proof.

Choose an actual nonempty fixed vertex v=[t,H) on the highest available layer, where H may be either its entering or exiting end. It suffices that H>=f_H(t), which always holds for an actual vertex. Suppose the easy paired root/band branches fail:

H-t>rp,
and l_base(t)<H-rp when a baseline exists.

For k=1,2,... stop at the first k with

#{i : l_i(t)>=H-kp}<=2k.

Each shortened prefix w_k=A[t:H-kp) is fixed. The relevant threshold count is even by the phase-parity statement, and the baseline layers do not qualify while k<=r. Therefore the process stops by r. The previous failed threshold, when k>1, has at least2k qualifying layers, giving for the lowest of the top2k layers

l_L(t)>=H-(k-1)p.

For k=1, the top fixed vertex is shared with its adjacent partner, giving the same inequality. Translation to x' in(t-p,t] and monotonicity then give

f_H(x)-l_L(x)<=kp for every x.

The stronger fixed-v rule supplies at least2(k+1) unblocked recorded occurrences of w_k, while at most2k have the identical full-text alignment. Thus there is a record on a different aligned text, exactly the kind needed by the source's matching-window argument.

Write K=kp. If that record R=[a,b) satisfies the source collective inequalities

r_H<=b+K, r_H-r_L<=K, r_L+K>=b,

the **proof** of `lem:collective` constructs a cost-K closed walk touching all top2k layers. The number of layers is not used in that geometric proof, only the inequalities and that K is a multiple of p. Add its reflected walk. Total cost2kp equals the budgets of the2k layers. If the collective test fails, a pair outside the collective block can be connected by a single ordinary p-cost individual link (when one member passes its test) together with its mirror, since its two members already meet at a fixed vertex. This uses the pair's2p budget. Pairs requiring a host can reserve2p instead, but the complete paired-host scheduling invariant has not been proved here.

This is a conditional local mechanism. It does not assert that every group can be processed while keeping the required available-pair baseline invariant or that all remaining cycles can be opened within budget.

## A genuine axis-versus-maximal-rotation mismatch

The source's final collective cycle-opening argument requires the chosen start t to be the lexicographically greatest forward rotation. The doubled threshold needs an actual fixed vertex at t. These conditions need not coincide.

Take A=(abcacb)^Z, period6, identity complement. The constant-height layer z(r)=r+8 has windows of lengths7 and8 and is reversal-fixed. Its actual fixed vertices occur at starts0 and3, with words `abcacba` and `acbabca`, respectively. The unique lexicographically greatest rotation starts at4 and is `cbabca`. At start4, the two actual windows are `cbabcac` and `cbabcacb`, neither a palindrome. Thus the source's maximal-rotation contact lemma cannot simply be invoked at the fixed-axis threshold point.

A shorter fixed prefix at the maximal rotation can lose fewer than p letters. That additive period is material to an exact factor-two budget. Likewise choosing a maximum among axis starts does not imply that all forward rotations of every target text lie below it, which is the actual hypothesis used in the source's maximal-rotation proof. No replacement cycle-opening lemma or charge for this loss has been established.

The exact remaining obligation is therefore a global paired-host and cycle-opening construction: paired bands/requests must retain disjoint budgets and phase-parity invariants, and every directed cycle of planned pair-block links must admit a mirrored short contact and omitted-link saving at the correct period cost, without assuming the fixed-axis start is lexicographically maximal. The local doubled surplus alone does not pay that step. The full RC factor-two target remains unresolved.
