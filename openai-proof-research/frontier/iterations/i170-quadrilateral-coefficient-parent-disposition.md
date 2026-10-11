# Parent disposition: I170 quadrilateral coefficients and boundary residuals

**Date:** 2026-10-11. **Scope:** parent-side verification and integration
decision for [I170](i170-quadrilateral-coefficient.md). All earlier reports
and seals (I164–I169) are unchanged. No finding-count change.

## Verification performed by the parent

1. **Hash precheck before any child code execution.** All 44 owned
   payloads match the sealed inventory (report SHA-256
   `8345e1d12991cc328a5910e735c6d0fa625f27715b50bbd91af9917974c74096`,
   seal `7c59b8b4...`, verifier `c4a3bec4...`); the seal chain binds the
   inventory and the successful prevalidation; all 64 non-context external
   bindings match, including the immutable I169 report
   (`1b367131...`) and seal (`536a161d...`); the four context ledgers are
   drift-free at integration. Receipts:
   `frontier/experiments/i170-parent-precheck.json` and
   `frontier/experiments/i170-parent-verification.json`.
2. **Sealed replay before any ledger edit.** `python3 -I -B .../verify.py`
   returned PASS in 130.97 s. All seven payloads (audit, prism,
   coefficient, residual attempts 01–03, longscan) regenerated
   byte-identically, with residual-03 reproducing residual-02 exactly as
   claimed, and the authoritative sources byte-equal to their audited
   attempt snapshots. All eight guard probes were blocked: write,
   filesystem mutation, network, subprocess, outside compile, outside
   exec, unbound read, and forged owned source. Context drift: none.
3. **Mathematical reading.** The parent read the full report and all
   owned code (`core.py`, `audit.py`, `prism.py`, `coefficient.py`,
   `residual.py`, `longscan.py`, `verify.py`, plus the attempt chain and
   `attempts.json`/`refuted-proposals.json`). Payload numbers were
   independently re-read and match the report: the 636-step histogram
   $138/385/56/34/13/10$; the 206 quadrilateral steps decomposing
   $12/127/12/32/13/10$ with equality coefficients
   $-\tfrac12{:}72$, $-\tfrac34{:}20$, $-\tfrac56{:}28$,
   $-\tfrac78{:}62$; the additional 914-step quadrilateral scan (52
   parents of order $\le28$, 610 equality cases) with $\alpha$ histogram
   $-\tfrac34{:}12$, $-\tfrac56{:}28$, $-\tfrac78{:}62$,
   $-\tfrac9{10}{:}196$, $-\tfrac{11}{12}{:}312$, all of the shape
   $-(m-1)/m$ and never $-\tfrac32$; the 982-step longer-face scan (23
   parents of order $\le24$) with no failure and losses only $0/1$;
   residual corrections over all 636 steps with exactly three
   $\delta_V=1$ cases; 580 short-gap steps including all 282 hexagonal
   steps; prism rows for $L=4..18$ in both deletion types with
   $\alpha=-(L-3)/(L-2)$. The index-431 certificate was re-read in full:
   order-20 parent, step `[0,0,4]`, $(u,v,x,y)=(2,10,13,7)$,
   $(\ell,t,\eta)=(1,0,1)$, $(\delta_V,\delta_R,\varepsilon)=(1,0,0)$,
   separator $w$ with $w\cdot U=0$ and $w\cdot v=-8$.

## Verdicts

- **Audit of I169 (F169, S169, P169, and the 206-step coefficient
  data): all PASS ORIGINAL**, with fresh enumerators and two exact rank
  implementations; the parent reviewed the reconstructed six P4 forcing
  arguments and the per-step comparison against the ancestor payloads.
- **H170 (short-gap theorem):** accepted as proved. If either
  cross-terminal pair ($ux$ or $vy$) is an edge of $K$, degree-two
  forcing gives the exact translation bijections $N_{00}\to P_{ux}$ and
  $P_{vy}\to D_{11}$ (the second via the planar exclusion of the crossing
  pairing), hence $U=V+Z$ and $t\ge\ell-1$. On a bipartite face the two
  complementary arcs are odd and positive, summing to four for a
  hexagon, so every admissible facial hexagon expansion has a short gap;
  the quadrilateral case recovers S169's bound. The exact bridge relation
  $b\equiv r+2z\pmod{L+U}$ and the equality-case failure locus
  $z\equiv-r/2$ are correctly derived; they characterize, but do not yet
  exclude, hexagonal equality-case failure. The parent checked the
  bijection directions, the odd-arc parity count, and the offset algebra.
- **R170 (exact boundary-residual decomposition):** accepted as proved.
  The alternating arc sums $q_J$, the compatible old subfamilies $F_J$
  (a finite graph-theoretic condition), and the residual classes $R_J$
  give the exact identity $\operatorname{diff}(J)=\operatorname{diff}(F_J)
  +\operatorname{span}(E_J)$ with $\operatorname{diff}(F_J)\subseteq V$,
  hence $U=V_{\rm good}+R$ exactly, and the deficit identity
  $\ell-t=\delta_V+\varepsilon-\delta_R$ with exchange equivalent to
  $\delta_R+\eta\ge\delta_V+\varepsilon$. This is the correct exact
  replacement for the refuted blanket formulas; it reduces to S169 on
  quadrilaterals and to H170 on short gaps.
- **Refutation of $V\subseteq U$ and even $V\subseteq L+U$:** accepted,
  with certified octagonal counterexamples at indices 263, 272, 431
  (rank $U=8$, rank$(U+V)=9$). Index 431 is the sharp instance: exchange
  still holds there ($\eta=1$ covers $\delta_V=1$), so these refute the
  containment shortcut, not the target. The integer separator
  certificates check out by direct dot products.
- **Geometric reformulation of the quadrilateral gap:** the excluded
  value $\alpha=-\tfrac32$ is exactly the normalized weight
  $w(F-C_0)=-\tfrac12$ of the disconnected square-switch 2-factor
  $F=N+s$. The report correctly notes this is an equivalence, not a
  proof, and that treating $F$ as a convex combination of Hamiltonian
  cycles would be an unproved extra assumption.

## Disposition

**Technical research only; no ninth nomination; no count change. Eight
accepted findings remain eight.** Universal exchange, (T) and Q164 remain
unproved and unrefuted. I170 narrows the live gaps precisely:

- **Quadrilateral gap:** a single excluded coefficient,
  $\alpha\ne-\tfrac32$, equivalently a normalized-weight bound
  $\ne-\tfrac12$ for one specific disconnected 2-factor. All 1,120
  tested quadrilateral equality cases have $\alpha=-(m-1)/m$.
- **Lower-bound gap:** (R170.3), i.e. $\delta_R\ge\delta_V+\varepsilon-1$,
  now matters only for faces of length $\ge8$ with both complementary
  arcs of length $\ge3$; every short-gap expansion, hence every
  quadrilateral and hexagon, satisfies $t\ge\ell-1$ by H170.
- **Bridge gap:** (R170.4) remains open in general; on hexagons it is
  exactly the exclusion of $z\equiv-r/2 \pmod{L+U}$.

**Next step (I171).** Two obligations in order. First, attack the
quadrilateral equality case via the 2-factor route: prove the normalized
weight of the disconnected square-switch 2-factor cannot be $-\tfrac12$
(equivalently $\alpha\ne-\tfrac32$), which proves exchange for every
facial quadrilateral expansion; the observed $-(m-1)/m$ shape is a
guide, not an assumption. Second, attack (R170.3) on octagonal faces
whose two complementary arcs both have length three: prove
$\delta_R\ge\delta_V+\varepsilon-1$ or certify a counterexample with
$t\le\ell-2$; any containment-style argument must pass index 431 (and
263, 272) before anything else. Mandatory first tests: index 0, the ten
nine-direction steps, and index 431. D168 (no bounded-transfer route),
M168 (no typed-fullness route), $\rho(L)=\mathbb Q^2$ (no
deleted-coordinate separators), and the refuted containment
$V\subseteq L+U$ remain binding constraints.
