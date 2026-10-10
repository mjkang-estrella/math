# Iteration 5 parent screening: squarefree conditioning is a baseline, parity is not

Date: 2026-10-08. Internal research checkpoint, not an independently reviewed new finding. The user requests another substantial result beyond R006. The following distinguishes a routine consequence already available from the genuinely harder new target.

## 1. Squarefree-conditioned PD follows routinely from R006

Use the notation of R006: `N(x)=π(2x)−π(x)`, `V(p)` is the ranked normalized prime-factor sequence of `p−1`, and `L` has PD(1). Fix a reduced class `b mod M`, a fixed finite number of coordinates, and a bounded continuous test `H` of those coordinates. For a prime `q`, put `e=v_q(M)` and define

\[
 \rho_q(M,b)=
 \begin{cases}
 1/(q(q-1)),&e=0,\\
 1/q,&e=1\text{ and }b\equiv1\pmod q,\\
 0,&e=1\text{ and }b\not\equiv1\pmod q,\\
 1,&e\ge2\text{ and }b\equiv1\pmod{q^2},\\
 0,&e\ge2\text{ and }b\not\equiv1\pmod{q^2}.
 \end{cases}
\]

Then the following deduction has a short proof:

\[
 \frac1{N(x)}\sum_{\substack{x<p\le2x\\p\equiv b\ (M)}}
 \mu^2(p-1)H(V(p))
 \longrightarrow\frac{\mathbb EH(L)}{\varphi(M)}
 \prod_q(1-\rho_q(M,b)).
\]

If the product is positive, conditioning on squarefreeness retains PD(1). If a square dividing M is forced to divide b−1, the product is zero and the squarefree event is impossible. This is a standard finite-local-condition truncation argument using R006, not the next substantial discovery.

**Finite conditions.** For fixed `Y`, squarefreeness at primes `q≤Y` is a union of reduced classes modulo `lcm(M,∏_(q≤Y)q²)`. R006 gives the same limiting `EH(L)` in each surviving class. CRT gives exactly the product of the displayed local survival probabilities. All these moduli are fixed before `x→∞`. Finite primes dividing the modulus are harmless.

**Tail.** Dropping the class restriction only increases the number of primes with `q²|p−1` for some `q>Y`. For `Y<q≤x^(1/4)`, Brun–Titchmarsh gives

`#{x<p≤2x:p≡1 mod q²}≪x/(q(q−1)log x)`.

Summing yields `O(N(x)/Y)`. For `x^(1/4)<q≤sqrt(2x)`, count all integers instead of primes: the sum is at most `Σ_q(x/q²+1)=O(x^(3/4)+sqrt x)=o(N(x))`, even enlarging q to all integers. Multiply this tail bound by `||H||∞`. First take `x→∞` at fixed `Y`, then `Y→∞`. The infinite product converges, and gives the asserted formula. No independence of infinitely many conditions is assumed.

The classical Brun–Titchmarsh inequality used here is displayed in the introduction of Kevin Ford's [author-hosted primary paper, *An explicit sieve bound and small values of σ(φ(m))*](https://www.ford126.web.illinois.edu/wwwpapers/sigphi.pdf), attributing it to Montgomery–Vaughan. The parent read that displayed interval inequality on 2026-10-08. The only new-corpus input is the accepted [R006 progression law](../findings/R006-progression-PD-primitive-root-density.md). The density without H is classical; no literature-priority claim is made for the joint consequence.

The exact diagnostic in `../experiments/i05_parent/squarefree_crt.py` checks local CRT probabilities, including forced-zero classes and the prime 2. Finite checks do not prove the asymptotic statement. This note has not received a separate proof audit and is not added to the finding count.

## 2. Why this does not settle parity

Knowing μ² gives no control of the sign of μ. Likewise PD controls normalized large prime factors, not the parity of the number of microscopic factors. R006 alone cannot justify equal positive and negative signs.

The parent read the actual pinned E source `Prime-Predecessors-with-an-Even-Number-of-Prime-Factors-September-17-2026/build/sections/03-shifted.tex`. Equation `sh:sign` permits only ε=1 or the completely multiplicative sign supported on the active prime groups. This is not a theorem for arbitrary full Liouville weights. In the endpoint-energy argument following `sh:small-square-error`, the prime-slot and rough discrepancy factors are outside those active groups, so their ε-values are one. Replacing ε by full Liouville changes this step and the discrepancy input; it is not a harmless substitution. The restricted convolutional endpoint form `sh:core` must also be retained.

An in-flight clarification was delivered to the existing parity research task with these exact source qualifications. The target remains a genuinely additional parity estimate or construction; the routine squarefree result above must not be offered as the requested new substantial theorem.

## 3. Current research tasks

Three distinct T3-owned tasks are running, with full briefs and task IDs recorded alongside this note:

- `iteration5-parity_pd-task.json`: new parity/PD estimates for prime predecessors, with exact signed-source hypotheses.
- `iteration5-joint_artin-task.json`: simultaneous primitive roots for dependent signed bases, testing whether local-entanglement criteria yield a nonroutine theorem beyond standard transfers.
- `iteration5-crossfield-task.json`: at least three fresh cross-field candidates followed by a deep proof attempt for the best, excluding the closed operator family and stalled old Hodge route.

Each report remains provisional until a fresh independent audit and parent integration. No new substantive finding is claimed at this launch checkpoint.
