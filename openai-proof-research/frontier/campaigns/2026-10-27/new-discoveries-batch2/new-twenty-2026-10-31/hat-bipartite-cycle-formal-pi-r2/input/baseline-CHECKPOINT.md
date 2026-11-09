# CHECKPOINT — hat-bipartite-cycle-formal-pi-r1 — 2026-11-07 (run 1, Pi GLM5.3Flash)

Status: PARTIAL. Two modules strict-compiled green under runner/checker. Endpoint
NOT reached. No acceptance, credit 0, campaign 52/60 beyond 39 unchanged.

## Compiled state (all exits 0, receipts in receipt/, logs in logs/)

- src/HatCycle.lean  sha256 6f536e8f35b80cd22ab8d51a77d237ed32175056c905ac75fb8a7937d0041970
  build/HatCycle.olean sha256 100cfa3f939b9801acfbedf169bc99ade7b04f5a99e39804797cd17f720b4ac6
  checker.sh HatCycle exit 0 (receipt 1794033058731583585_leanchecker_HatCycle.json).
  Contents: literal source graph hatEdgeSet (labels 0..2s-1, A odd, B pos-even,
  z-edges {0,1},{0,2s-1}, canonical increasing orientation, no loops);
  HEdge; hatAdj (+symm/irrefl); IncidP; Bnd (boundary/parity map over
  HEdge -> ZMod 2); Rch (walk connectivity); HamCirc (explicit edge set,
  deg2 = exactly-two-incident at every label, conn): genuine connected
  2-regular spanning subgraph, no kernel/bridge encoding; HamVec;
  sum_indicator_card (self-contained induction); hamVec_even (every Hamilton
  circuit vector has even incidence); CycleKernel (Submodule, even-incidence
  kernel); HamSpan (F2-span of HamVec over all HamCirc); hamSpan_le
  (HamSpan <= CycleKernel) — the converse half of the endpoint, done.

- src/HatConstr.lean sha256 (see sha256sum output; final green build)
  build/HatConstr.lean olean present, check.sh exit 0 on final state.
  Contents: hatCan canonical-pair encoding; hatCan_swap; hatCan_inj
  (unordered-pair equality iff); hatCan_mem_AB / hatCan_mem_BA (canonical pair
  of A/B vertices is a genuine hat edge; omega-driven);
  tourAB / tourBA (tour edges x j -- t j and t j -- x (j+1) as HEdge, with
  parity hypotheses carried as arguments); tourSucc.

## Failed intermediate builds

Preserved in logs/ and receipt/ (exit 1): first HatCycle import/submodule
iterations; HatConstr hatCan_inj argument-order round; hatCan_swap dependent
proof rewrite; hatCan_mem_AB anon-notation; Fin.cast index round. No stale
passes; final states re-verified by exit 0 receipts above.

## Exact remaining bridges (none assumed; each needs real proof)

1. tourEdges: union (image tourAB) ∪ (image tourBA) ∪ {z-edge x 0, z-edge
   x (s-1)} as Finset HEdge; membership characterization; z-edge constructor
   needs x 0 = 1 / x (s-1) = 2s-1 label hyps (hatCan s 0 v member via
   e.1=0 ∧ (e.2=1 ∨ e.2=2s-1) disjunct; omega).
2. HamCirc instance for the tour under: x,t injective; x i odd; t j even
   nonzero; x 0=1, x (s-1)=2s-1; 2 ≤ s. deg2 by case on v in {z, x i, t j}
   with explicit two-witness filter equality + card; conn by walk along the
   tour sequence (Rch.step induction over j).
3. Rectangle realization: for distinct p,q in B, u in U=A\{1,2s-1}, y in
   U\{u}: two tours (A-order a,y,u,...,b; B-order p,q,...; and the p,q swap)
   are HamCircs; HamVec H + HamVec H' = rectangle vector R(a,u;p,q)
   (4-term indicator) by pointwise case analysis; mirror construction for
   R(b,u;p,q). Both rectangles in HamSpan via Submodule.span mem + hamSpan_le.
4. Chain identities: R(x,w)+R(w,t)=R(x,t) pointwise (2=0 in ZMod 2);
   R(x,x)=0; symmetry; then R(a,u),R(b,u) (u in U) + R(a,b)=R(a,c)+R(c,b)
   imply every R(x,w) in HamSpan (single-middle-a reduction:
   R(x,w)=R(x,a)+R(a,w)).
5. Kernel clearing: for f in CycleKernel with zero z-coordinates, off-double-star
   support: g = sum over off-star edges e with f e = 1 of R(e.1,a0;e.2,p0);
   off-star fingerprint uniqueness of rectangles; star T is a tree; leaf
   parity forces zeros; a0p0 from center parity; f = g in HamSpan.
6. z-cancellation: boundary at z gives f(z,a)=f(z,b); eps := f(z,a);
   H0 from step 2 (any A-order a..b, any B-order); f + eps.H0 z-free -> step 5;
   hence CycleKernel <= HamSpan; with hamSpan_le conclude equality
   CycleKernel = HamSpan for all s >= 4 (hyp s >= 4 used only for U nonempty
   in step 3 constructions; state as 4 <= s hypothesis on the final theorem).
7. Audits: #print axioms for all new decls (expect only propext,
   Classical.choice, Quot.sound) under same -j1 flags; checker.sh per module;
   CHECKPOINT/SUMMARY + results/325100.json keyed entry with paid/unpaid
   truth; frozen-after verification at seal by root.

## Environment (pinned, unchanged)

LEAN_BIN /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux
(lean e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550,
checker ccef1bfe...696fcbe per ROOT-PREPARATION.json); mathlib packages path
.../2026-10-14/formal/.lake/packages; runner caps as enforced in receipts
(2 CPU affinity, AS 12GiB, wall 140/devguard 130, MALLOC_ARENA_MAX 2).
No network/git/installs; all writes lane-local; frozen-before verify_frozen
before: count 145 mismatches 0 (receipt at run start).

Honest scope note: source/review inputs were read only after first compile
per TASK; author ordinary proof + independent review read in full; the module
split above mirrors their obligation list 1:1. Nothing here claims acceptance,
novelty settlement, or endpoint completion.
