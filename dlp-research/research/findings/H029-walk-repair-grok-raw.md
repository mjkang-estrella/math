# H029 Grok walk repair — raw proposal, NOT admitted

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h029-walk-contracts-grok-20261008-r1`
Provider/model: grok / grok-4.7
Status completed, retrieved 2026-10-08. Root review pending. Proposed experiments are NOT authorized merely by this report.

The two H027 cards can be repaired into complete low-memory solvers. Neither has a proved complete-work gain. Verified improvement remains **NONE**. Card 3 stays closed. The Brent–Pollard gate \(5.09\sqrt{q}/\delta\), the optimized-\(\delta\) minimum, and the \(c\le 3\) cutoff are unused.

Both repairs use one global clock, so the mixer fraction is exact, equal points at the same time share a successor, and a per-walker phase is not part of the state. Distinguished points then detect a same-point merge with an additive wait. Full BSGS is not the fallback.

## Shared contract

Scope is one ordinary curve \(E/\mathbb{F}_p:y^2=x^3+Ax+B\), with \(\#E(\mathbb{F}_p)=q\) prime, \(q\neq p\), \(q\approx p\), \(\gcd(q,p-1)=1\), and \(\mathrm{Aut}=\{\pm 1\}\). The scalar \(k\) is full range. Inputs are public \(E,G,Q=[k]G\). Instances are synthetic. Setup, inversions, restarts, nulls, stalls, verification, and fallback are inside the paid total.

The comparator is the Bernstein–Lange–Schwabe negating additive walk (cryptojedi `negation-20110102.pdf`, §3, read here through the batch ledger): canonical representative, \(r=256\), one batched affine addition per step, 2-cycle check every \(w_2=32\) steps, and longer even lengths \(2c\) through the smallest even integer exceeding \(\log q/\log r\), with \(w_{2c}=\lceil 2\,r^{c/2}\rceil\). That \((1+o(1))\sqrt{\pi q/4}\) iteration count is their heuristic for their walk. It is a budget figure below, not an expectation for these maps. Their large-batch addition is \(5M+S+(I-3M)/n\). Their algorithm section writes \(a=-3\); the addition formula used for the ledger does not use \(A\).

Constants, frozen before any run: batch width \(m=32\), clock \(L=32\), memory words per distinguished record \(w_{\mathrm{rec}}=6\),
\[
B_{\max}=\max\bigl(1,\lfloor 0.19\sqrt{q}/6\rfloor\bigr),\qquad D=\max\bigl(2,\lfloor\sqrt{q}/B_{\max}\rfloor\bigr).
\]
A point is distinguished when the integer representative of \(x\) in \(\{0,\ldots,p-1\}\) is \(0\bmod D\). The table stores at most \(B_{\max}\) records \((x,x_{\mathrm{prev}},a,b,\mathrm{seed},\mathrm{step})\). A full table refuses new inserts and still answers lookups.

Starts, same on both repairs and the control: walker \(i=0,\ldots,31\) holds \(a=0\), \(b=i+1\), \(P=[b]Q\), and the pair \((x(P),x(P-G))\). Build \(Q,2Q,\ldots,32Q\) by \(31\) additions of \(Q\), then \(32\) additions of \(-G\). No pure-\(G\) walker exists. A public cursor begins at \(32Q\). Restart number \(n\) sets \(b=32+n\), replaces the cursor by the cursor plus \(Q\), and rebuilds the pair, for two charged additions, then waits until the next \(t\equiv 0\pmod L\) and rejoins the clock. No phantom steps during the wait.

Labels stay in \(\mathbb{Z}/q\mathbb{Z}\). On an exact hit, \(c=b-\varepsilon b_s\bmod q\). If \(c=0\), the hit is null: restart the younger walker and keep the paid trail. If \(c\neq 0\),
\[
k\equiv (\varepsilon a_s-a)\,c^{-1}\pmod q,
\]
checked by one scalar multiplication \([k]G=Q\), charged conservatively at one comparator addition per double or add. A failed check is charged and the walk continues. Powers \(2^e\) and \(3^e\) are never treated as nonzero merely because the integer depths differ.

Each walker keeps a ring of the last \(64\) keys. A repeated key with \(c=0\) is a fruitless cycle. Separately, \(4D\) steps without a distinguished event restarts that walker. At most \(8\) restarts per slot; then the slot stays dead. If every slot is dead, fall back.

Work cap: \(C_{\mathrm{cap}}=\lceil\sqrt{\pi q/4}\cdot(5+s)\rceil\) leading \(M\)-units at the pre-registered \(s\), plus the actual \((I-3M)/n_{\mathrm{active}}\) remainder, and \(T_{\max}=\lceil 8\sqrt{q}\rceil\) steps per walker. Either cap abandons the walk and runs the comparator from scratch. The complete cost is abandoned work plus the whole comparator run. There is no BSGS branch. Field additions, integer label updates, and canonical comparisons sit outside the \(M,S,I\) ledger on both sides, as in the Bernstein–Lange–Schwabe batch account.

## R1 — clocked quotient doubling

This repairs Card 1. The state is the H023 sorted pair, so it is a function on the reflection classes, a set of size \((q+1)/2\).

Prepared constants, charged once: \(c_1=2(3g^2+A)\), \(c_2=4y_G^2\). For finite \(u=x(P)-g\) and \(v=x(P-G)-g\),
\[
z=(c_1+c_2/u)/u-v.
\]
A fill sends the pair to \((z,u)\) and \((a,b)\leftarrow(a+1,b)\), then sorts. A swap replaces the representative by \(G-P\) and sets \((a,b)\leftarrow(1-a,-b)\). Leading cost in a full batch: \(5M+(I-3M)/n\), and no \(S\).

On steps \(t\equiv 31\pmod{32}\), every active walker doubles the current representative by the H023 pair formulas
\[
x(2P)=\frac{(3x^2+A)^2}{4\bigl(x(x^2+A)+B\bigr)}-2x,
\]
\[
x(2P-G)=2\frac{(x+x')(xx'+A)+2B}{(x-x')^2}-g,
\]
then sorts and reflects as above. Labels become \((2a,2b)\) before that reflection. Leading cost: \(11M+3S+(I-3M)/n\).

The block average is
\[
c_1(s)=\frac{166+3s}{32}=5.1875+0.09375s.
\]
At \(s=1\), \(c_1=5.28125\) against \(6\). At \(s=0.8\), \(c_1=5.2625\) against \(5.8\). Slack exists only while the observed step count \(N_1\) satisfies \(N_1/N_{\mathrm{BLS}}<(5+s)/c_1(s)\): about \(1.136\) at \(s=1\) and \(1.102\) at \(s=0.8\).

Detection stores the sorted pair. Equal representatives use \(\varepsilon=+1\) only. Fill stretches can sit in the known length-\(2\) translation cycle until the clock doubles. A length-\(2\) repeat whose both visits are fills does not restart the walker; those steps stay in the bill. If the state after the doubling step repeats any key from the previous \(32\) steps and \(c=0\), the mixer has preserved a fruitless cycle and the walker restarts. Infinity, \(u=0\), a zero denominator, or \(x=x'\) uses that same restart.

## R2 — clocked oriented jump

This repairs Card 2. The state is the oriented pair \((x(P),x(P-G))\) and is not sorted. The fill is the same translation, without the reflection update. Opposite points are different states and are not merged.

On steps \(t\equiv 31\pmod{32}\), recover the ordinate from the accepted identity. With \(u=x(P)-g\), \(v=x(P-G)-g\), and \(C=3g^2+A\),
\[
\mu=(uv-C)\cdot(2y_G)^{-1},\qquad y(P)=\mu u-y_G.
\]
The inverse of \(2y_G\) is setup. The recovery is \(3M\) plus additions, with no squaring and no Tonelli–Shanks step. Then add the precomputed jump and add \(-G\):
\[
h=x_{\mathrm{int}}\bmod 16,\qquad d_h=2h+1,\qquad c_h=1,\qquad J_h=G+[d_h]Q.
\]
Labels become \((a+1,\,b+d_h)\). The new pair is \((x(P+J_h),x(P+J_h-G))\). Two batched affine additions plus the recovery give the leading jump cost \(13M+2S+(I-3M)/n\). The sixteen jumps are built during setup and charged.

The block average is
\[
c_2(s)=\frac{168+2s}{32}=5.25+0.0625s.
\]
At \(s=1\), \(c_2=5.3125\) against \(6\). At \(s=0.8\), \(c_2=5.30\) against \(5.8\). The slack thresholds are about \(1.129\) and \(1.094\) times the matched Bernstein–Lange–Schwabe step count.

Lookup is by \(x\), with both orientations retained up to the two points that share an abscissa. A hit tries \(\varepsilon=\pm 1\). Same-point meetings share the later clock. Opposite meetings produce a relation only when that abscissa is stored. The cycle key is the full oriented pair.

## Premises

R1 has a positive matched premise because its state is already the reflection quotient and \(c_1(s)<5+s\) on \([0.8,1]\). The unsupported claim is dynamical: after restarts, nulls, stalled distinguished waits, and fill-stretch revisits, the step count still lands under the threshold above. No random-map constant is assigned to \(N_1\).

R2 pays a similar arithmetic gap on the full group of \(q\) oriented points. Its unsupported claim is stronger: same-point coalescence, plus whatever opposite distinguished hits actually occur, must still finish inside about \(1.13\) Bernstein–Lange–Schwabe step counts at \(s=1\). A full-group birthday heuristic would miss that threshold. That heuristic is not a lower bound for this clocked map, and it is not used as one.

Card 3 is not repaired. The raw \(24M+4S\) tally and the review’s \(22M+4S\) tally disagree, and this pass does not adopt either. A clocked tripling schedule becomes admissible only when a written batched count \(C_3\) satisfies \(((L-1)5+C_3)/L<5+s\) at both \(s=0.8\) and \(s=1\).

## Falsifier

Stage 0 is paper only. Recompute \(c_1(s)\) and \(c_2(s)\) from the formulas above. A schedule whose recomputed average meets or exceeds \(5+s\) at either \(s=0.8\) or \(s=1\) is closed with no curve.

Stage 1 is the cheap finite gate. Take the first eight primes \(p>2^{15}\) that yield \(A=1\) and the smallest nonnegative \(B\) for which \(E\) is ordinary and nonsingular, \(q=\#E(\mathbb{F}_p)\) is prime, \(q\neq p\), \(\gcd(q,p-1)=1\), \(j\notin\{0,1728\}\), and \(G\) is a generator. Set \(Q=\lfloor q/3\rfloor G\). Run each repair as a deterministic solver with a full-state dictionary and no distinguished-point wait. Pair it with the \(r=256\) control on the same curve, starts, and batch. Let \(U_j\) be the repair’s complete cost, including fallback, and \(V_j\) the control’s cost.

The parameter set \((L,m,r)=(32,32,16)\) fails this fixture when \(\sum U_j\ge\sum V_j\). That is a finite loss of the stated complete-work premise. It is not an asymptotic barrier, a median, or a random-map theorem. The set gains finite support only when \(\sum U_j<\sum V_j\) and every repair trial verifies \(k\) inside the walk, with the fallback unentered. Support authorizes stage 2 only. Parameters stay frozen.

Stage 2 repeats that paired sum on the first such curve with \(q>2^{28}\), now using the distinguished-point rule, \(B_{\max}\), \(D\), the \(4D\) stall, and the memory cap. A loss retires the low-memory claim for these parameters. A win is finite evidence for an independent cost review. It is not a verified gain and not an estimated expectation.

## Priors read for this pass

Read in full here: the H027 raw cards, the authoritative walk reconciliation, the raw Opus review (its numerical gate was not reused), H023’s translation, doubling, and quotient-cycle account, H025’s oriented-burst and bounded-stride screens, the H013 Bernstein–Lange–Schwabe ledger, the H019 high-memory screen, and the H024 detected-reversal negative. Bernstein–Lange–Schwabe §§1–3 were read in the cryptojedi PDF through the \(5M+1S\) batch identity, the heuristic iteration count, and the fruitless-cycle overhead. Teske’s papers and Brent–Pollard were not opened; none of their constants are used. The high-memory x-only baseline is outside the claim. H028 stays parked on the equal-unit loss.
