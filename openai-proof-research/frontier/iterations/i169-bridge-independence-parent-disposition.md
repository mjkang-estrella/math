# Parent disposition: I169 bridge independence and quadrilateral recovery

**Date:** 2026-10-10. **Scope:** parent-side verification and integration
decision for [I169](i169-bridge-independence.md). All earlier reports and
seals (I164–I168) are unchanged. No finding-count change.

## Verification performed by the parent

1. **Hash precheck before any child code execution.** All 39 owned
   payloads match the sealed inventory (report SHA-256
   `1b36713181c4f3f5b2ea6f084558dca6553bf86a7b863bfca867fee126f17fcf`,
   seal `536a161d...`, verifier `97b1caaa...`), including the 50 MB audit
   payload; the immutable I168 report and seal hashes are confirmed; all
   17 non-context external bindings match. Receipt:
   `frontier/experiments/i169-parent-verification.json`.
2. **Sealed replay before any ledger edit.** `python3 -I -B .../verify.py`
   returned PASS in 52.36 s with empty stderr. All six payloads
   (audit, both support versions, attack, both explorations) regenerated
   byte-identically. All eight guard probes were blocked: write,
   filesystem mutation, network, subprocess, outside compile, outside
   exec, unbound read, and forged owned source (a deliberately alien
   pre-compiled code object and a compile under a trusted filename with
   wrong bytes are both rejected). The context ledgers were drift-free at
   replay, verified again at integration.
3. **Mathematical reading.** The parent read the full report and all
   owned code (`toolkit.py`, `audit.py`, `support.py`, `attack.py`,
   `explore01.py`, `explore02.py`, `verify.py`, `seal.py`,
   `prepare.py`, runners). Payload numbers were independently re-read
   and match the report: 206 quadrilateral steps decomposing as
   $12/127/12/32/13/10$ over the six $(\ell,t,\eta)$ classes; the 182
   equality-case coefficients $\alpha$ distributed as
   $-\tfrac12{:}72$, $-\tfrac34{:}20$, $-\tfrac56{:}28$,
   $-\tfrac78{:}62$ (never $-\tfrac32$); 442 explicit bridge separators
   and 56 explicit $U$-recovery witnesses; 16 prism checks for
   $L=4..18$ in both deletion types with $\alpha=-(L-3)/(L-2)$; the
   face-length histogram (including 40 length-10 steps) consistent with
   the earlier 636-step distribution.

## Verdicts

- **Audit of I168 (R168/E168, D168, M168, histogram, mandatory sets):
  all PASS ORIGINAL**, with two independent enumerators and two
  independent rank implementations cross-checking all 636 main rank
  computations. The preserved first-run failures (unhashable-list
  enumerator crash; incomplete small-denominator coefficient scan) are
  child-side implementation failures, correctly retained and not
  attributed to I168. I169's clarification that M168's witness is an
  order-16 parent with an order-12 retract is a wording clarification
  of I168's informal opening, not a mathematical change; the parent
  disposition of I168 already states the correct orders.
- **F169 (deleted-edge-free reduction):** accepted as proved. Six-fibre
  nonemptiness from the stipulated P4 corollary is correctly derived in
  the child. The restriction map $\rho$ on surviving signatures is
  $\mathbb Q^2$ (three affinely independent points), so
  $L\cap\ker\rho=L_0$, and both rank identities and the
  $\eta$-preserving replacement $b\leftrightarrow\beta$ follow; with
  $N_{00}$ nonempty the fourth signature yields
  $d(G)=2+\dim(L_0+V+\operatorname{span}\{c\})$ and exchange becomes the
  exact $K$-space comparison. The parent checked the signature counting
  and the offset degree bookkeeping. The proved corollary that
  deleted-edge coordinates alone can never separate $b$ from $L+U$
  correctly kills that shortcut.
- **S169 (quadrilateral recovery, $\ell-1\le t\le\ell$):** accepted as
  proved. The three exact bijections $N_{00}\to P_{ux},P_{vy},D_{11}$
  (deleting $ux$, $vy$, both) are correctly argued: degree-two forcing,
  the impossibility of closing an isolated $ux$ path inside a spanning
  $ux$-path, and the planar exclusion of the crossing pairing, with
  $u$-$v$/$x$-$y$ forced because the other noncrossing pairing would
  close two cycles. Hence $U=V$ and $b\equiv 3r+2s\pmod W$; the
  exchange criterion in the equality case is exactly
  $\alpha\ne-\tfrac32$. The parent verified the bijection direction and
  the quotient algebra.
- **P169 (exchange for every lateral expansion of every even prism):**
  accepted as proved, with the explicit integral identity
  $(L-2)(r_0+r_1-t_0-b_0)=(L-3)C_0-\sum_{j\ne0}C_j+X+Y$ checked
  coordinate-wise in the report's argument; the coefficient
  $\alpha=-(L-3)/(L-2)$ approaches $-1$, never $-\tfrac32$, giving
  $\eta=1$ for unbounded losses $\ell=L-3$. The 3-connectivity case
  analysis of the children is complete. Finite two-enumerator checks to
  $L=18$ are supporting evidence for an analytic statement, correctly
  labelled.
- **Section 5 characterization** ($t=0$ iff every survivor-constant
  weight is separately constant on each new class; for quadrilaterals,
  iff $N_{00}$ lies in a single $L$-coset) is a correct annihilator
  duality restatement, and the report correctly refuses to call either
  case "generic" absent a measure.

## Disposition

**Technical research only; no ninth nomination; no count change. Eight
accepted findings remain eight.** Universal exchange, (T) and Q164
remain unproved and unrefuted. I169 narrows the live gap precisely:
exchange now reduces to (a) ruling out the single coefficient
$\alpha=-\tfrac32$ for quadrilateral faces, and (b) extending the
$\ell-1$ recovery bound beyond quadrilateral faces, where 430 of the
636 tested steps lie and no bijection structure is yet proved.

**Next step (I170).** Two obligations in order. First, attack the
quadrilateral equality case: prove $\alpha\ne-\tfrac32$ universally
(e.g. by a positive relation among $r,s$ modulo $W$, or a structural
obstruction), which would prove exchange for all facial quadrilateral
expansions. Second, attack longer faces: generalize the
$N_{00}$-to-class maps — deletion of the two cross diagonals no longer
gives bijections for face length $\ge6$, so the required statement is
an inequality or an injection with correction terms, keeping CW167's
exact offsets. Mandatory first tests remain index 0 and the ten
nine-direction steps; the prism family supplies unbounded-loss tests
with $\alpha\to-1$. D168 (no bounded-transfer route) and M168 (no
typed-fullness route) remain binding constraints.
