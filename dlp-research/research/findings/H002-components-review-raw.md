# Unaccepted raw delegated review

Coordinator dispositions supersede unsupported dominance and experiment-budget claims.

T3 does not improve on the equal-budget baseline. Lazy weighted labels are valid bookkeeping for a shared add-only walk, and dynamic retirement is a scheduling rule already subsumed by sequential distinguished-point reuse. It must not be claimed as a cost improvement.

## Label recovery

The collision rule is right. An archived point is \(X=Q_i+aG\). One target-independent step \(F(X)=X+s(X)G\) sends the counter to \(a+s(X)\). A real point collision is
\[
d_i-d_j=a_j-a_i\pmod{q}.
\]
If \(F\) is deterministic, the two trajectories share the entire suffix and the counter difference stays constant, so a later collision on that suffix is the same equation. Joining the tame point \(Q_0=\mathcal{O}\), \(d_0=0\), reveals every origin in that component, and each \(d_i\) still has to be checked by \([d_i]G=Q_i\).

The sound representation is an immutable record \((\text{origin},a)\) plus a weighted union-find on the \(K+1\) origins. Path compression has to add the oriented deltas. A same-component collision is only a consistency check.

A single mutable “component potential” is not sound. Records written against an old representative and records written against the new one do not share one translation. That epoch bug double-shifts the new records. Lazy queries are cheap only if each collision composes the two records involved. Rewriting the archive on every merge is an I/O cost the card does not remove.

Target-dependent steps, or a key that is not the full point, void the shared suffix. An \(x\)-only fingerprint can alias \(\pm X\) and poison the union-find; verification then fails the batch after the budget is spent.

## Prior art

The scalar-difference graph is Fouque–Joux–Mavromati, Asiacrypt 2014, §2 (eprint 2013/761). Vertices are the users plus a known tame start. A cross-chain distinguished-point collision is an edge labeled by the linear relation. They already keep those relations before anyone is solved. For a constant fraction of the users they stop at the giant component (\(cL/2\) edges). For every user they require \(2L\ln L\) edges. A static variant that starts from random combinations of \(O(\log L)\) targets cuts that to \(O(L)\) rows. Neither variant is dynamic retirement.

The strongest same-preprocessing baseline is Kuhn–Struik, SAC 2001, §4, following Silverman–Stapleton’s ANSI X9F1 suggestion. Solve one target, relabel every stored distinguished point to a known multiple of the generator, then aim the next walks only at an unsolved target. Their Theorem 1 is
\[
E_L\approx\sqrt{\frac{\pi N}{2}}\sum_{t=0}^{L-1}\frac{\binom{2t}{t}}{4^t}\sim\sqrt{2NL}
\]
for \(L\ll N^{1/4}\), counting group operations until \(L\) useful collisions. The same hitting-time sum \(\sum_t\sqrt{N/(2t)}\) stays \(\sim\sqrt{2NL}\) as long as the covered set is \(o(N)\). Yun, Eurocrypt 2015, shows a generic lower bound \(\Omega(\sqrt{Kp})\) for \(K=o(p)\) instances at constant success probability, so the exponent is tight.

Bernstein–Lange, Asiacrypt 2013, §3.4, only points at Kuhn–Struik and at Hitchcock–Montague–Carter–Dawson (IJIS 2004). It is not the baseline. Their own algorithm is single-target cube-root preprocessing and must not be given to one side only. I did not retrieve the Hitchcock–Montague–Carter–Dawson paper itself.

I found no primary source for this allocation rule: retire a component as soon as it merges, keep its trajectories, and send the next chain to the representative with the least archived mass. The graphs and the tame relabel are already published.

## Cost

Use the same walk, the same distinguished-point rate \(\theta\), the same record cap \(M\), the same \(K\) targets, and the same \(W\) workers. Preprocessing is empty on both sides.

Parallel Kuhn–Struik puts all \(W\) workers on one unsolved target. Van Oorschot–Wiener already gives that target a linear worker speedup. Every stored point sits in the tame image, so it raises the hit rate of every later target. A satellite archive does not. It helps other targets only after it merges into tame, and the steps that built it could have enlarged the tame image directly. Balanced allocation therefore stores a worse use of the same \(M\).

Static Fouque–Joux–Mavromati is the weaker comparator. Equal chain counts keep sampling heavy components and pay the coupon-collector \(\log K\) to finish the last vertices. Retiring those components can cut that waste. Beating the static graph and losing to sequential reuse is subsumption, not an improvement.

Batching makes the dynamic rule strictly extra work. A merge is invisible until both walks reach a distinguished point, expected \(1/\theta\) further steps. Kuhn–Struik pays that tail too. T3 also finishes up to one batch of chains started under stale masses. If the batch is large next to \(K\), the policy collapses to the static allocation inside the batch. The control messages and union-find queries are small next to group operations only when records are not rewritten.

No version here changes the bulk exponent. The all-\(K\) cost remains \(\Theta(\sqrt{Kq})\) up to the Kuhn–Struik constant.

Multi-target scope cannot establish a single-target hardness change. A win, a loss, or a tighter scheduling constant for \(K>1\) says nothing about the one-target cost \(\sqrt{\pi q/2}\). Shoup’s generic bound still applies to one instance.

## Kill test

A falsifier is justified only as a pre-registered kill test of the improvement claim, not as a search for a gain. Do not run it here.

One program, three paired arms, identical permutations and starts:

- Universe \(\mathbb{Z}/q\mathbb{Z}\), \(q=65537\). The solver sees only a fixed public permutation key \(H(x)\) and the public step \(s(H(x))\). It starts target \(i\) at \(x=d_i+a_0\) and carries \((\text{origin},a)\). It never receives \(H^{-1}\) or \(d_i\).
- Distinguished when the low 4 bits of the key are 0. Cap \(M=512\) archived records. \(K=32\), \(W=8\), reallocate only every \(B=8\) reports. In-flight walks are finished and counted.
- Arms: static equal chain counts; sequential reuse, all workers on the current unsolved target, immediate tame relabel; T3, no new chains from a tame-connected origin, otherwise the component with the fewest archived records.
- Twenty seeds, cap 8000 steps per arm. Total cap \(4.8\cdot 10^5\) events.
- Primary metric: steps until every recovered \(d_i\) matches the planted secret, censoring at the cap. The improvement claim dies unless the paired mean beats both arms on uncensored all-\(K\) completions. Fraction solved, and the giant component, are not success.

## Assumptions

The walk is one shared add-only function of the full point. Records keep the original origin. The union-find is weighted and oriented. Every target is verified. Memory, workers, \(\theta\), and preprocessing match Kuhn–Struik, not merely the static graph. Outstanding walks are charged. Labels are not a discrete-log oracle.

Under those assumptions the high-risk scheduling idea can sit in the file as unproved, but it cannot claim a cheaper all-target algorithm. No curve, wallet, GPU, or Lean follow-up is justified.
