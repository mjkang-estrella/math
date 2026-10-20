# Other screens (all stopped before any freeze)

Families were chosen with the history-count table first (`private/history/r95-family-history-counts.txt`), then targeted `rg` over `frontier/iterations`, `frontier/campaigns`, `proposals`, `notes`, `findings` and `experiments`. The brief's CLOSED list (041, 017, 016, 037, 062, 249, 063, 250, 164) and the older avoid-list were not touched. The active analytic r128 and structural r131 directories were not read.

## 001: Milne's rationality conjecture (one history unit, catalogue only)

- **Read.** `00_intro.tex` in full (`thm:main`, the origins, method and overview subsections).
- **Source scope.** For an abelian variety $A/\overline{\mathbb Q}$ with good reduction at $w$, a rational Hodge class $\gamma$ and Cartier divisors $D_1,\dots,D_{d-r}$ on $A_0$, the source gives one $q\in\mathbb Q$ equal to the $\ell$-adic and crystalline pairings. With the CM Hodge theorem (family 032), `cor:algebraic-specialization` represents $\gamma_0$ by one rational algebraic cycle in all realizations. The source says its pairing with *any* complementary algebraic cycle is then a rational intersection number. That already pays the "higher-codimension test cycle" extension.
- **Directions considered.**
  - Products of K3 surfaces. A same-family companion title, "The rational Hodge conjecture for products of K3 surfaces" (catalogue and path listing only; body not acquired), would make the Hodge class algebraic in characteristic 0. Specialization then gives rationality as an immediate composition.
  - General varieties with abelian motive, such as K3 surfaces through Kuga–Satake. This needs mixed-characteristic algebraicity, or at least a compatible specialization of motivated correspondences that sends divisors on the reduction to divisor products. That is a central unbuilt input.
  - Bad (semistable) reduction. This is outside the conjecture's good-reduction formulation, and its realizations change. No closable formulation was identified.
- **Stop.** Each extension is either an immediate composition or a central gap.

## 013: Ostmann's inverse Goldbach conjecture (two history units, catalogue-level r72)

- **Read.** `01-introduction.tex` and `09-conclusion.tex` in full.
- **Mechanism.** The method has these stages:
  - residue partition $S_p$ and collision estimates;
  - quadratic and higher-character decorrelation;
  - a prime-supply tensor estimate;
  - a finite-field tree comparison;
  - a positive statistic;
  - permutation symmetrization with a bad-arrangement count (`eq:src60`), a diagonal reserve and a final rate (`eq:conclusion-final-rate`).
- **Directions considered.**
  - Primes in a fixed progression $a\bmod q$. The pair obstruction for a two-element summand (Brun upper bound for prime pairs) is classical. The full statement would rerun the whole source with progression-restricted prime counts, which is a parameter variant.
  - A density version, where $(A+B)\triangle\mathcal P$ has relative density zero. The source explicitly says neither coverage nor exclusion is replaced by a density condition. Its contradiction uses eventual coverage of *every* large prime inside the supply and arithmetic estimates. A density repair would need a new robust supply mechanism, and none was identified. Two elementary checks were made: a two-element summand forces $\lvert B(x)\rvert=o(x/\log x)$ by the prime-pair bound, and this alone gives no contradiction.
- **Stop.** One direction is a parameter variant; the other has no constructible route.

## 207: Kaplansky idempotents in positive characteristic (history r72, r79, r91)

- **History read.** `r79-public-research.md` 207 sections (twisted traces, algebraic HH₀ finite-commutator gap) and the r91 summary line in the brief.
- **Direction considered.** Torsion-free $G$ and $\mathbb F_p[G]$. An idempotent of $\mathbb F_p[G]$ lifts by Newton iteration $e\mapsto3e^2-2e^3$ to an idempotent of the $p$-adic completion $c_0(G,\mathbb Z_p)$. The conclusion would then follow from a *$p$-adic* Bass theorem for $c_0(G,\mathbb Q_p)$ with a faithful-trace argument.
- **Stop.** The source's $\ell^1$ proof is archimedean: it uses a square-root correction in a weighted Banach algebra, cyclic weights, a connection and a Pfaffian curvature bound. No $p$-adic analogue was built. In characteristic $p$ the trace is not faithful, so even $\operatorname{tr}e\in\{0,1\}$ would not finish the argument. This is a central gap. The lifting step is classical and is not offered.

## History-only exclusions

- **067 (sevenfold Campana–Peternell).** The r92 screen (copied) leaves $d=4,5,6$ and $\rho=2$ obligations with exact dimension-specific failures. Not reopened.
- **018 (Margulis–Platonov).** r72 and r90 screens are navigation only. Further congruence-subgroup consequences need Serre's conjecture outside the source's range. Not reopened.
- **033/034/036/056 (Iitaka subadditivity, Kähler log abundance, generalized minimal models, termination).** Combining 033's logarithmic subadditivity with 034's conditional abundance is a catalogue-level composition of two stipulated sources. r90 already credits the 036 abundance reductions. Not reopened (catalogue-level only).

No exhaustion or worldwide-priority claim is made.
