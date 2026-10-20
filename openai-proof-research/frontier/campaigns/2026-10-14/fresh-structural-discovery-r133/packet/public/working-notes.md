# r133 working notes (author scratch, chronological)

Runner: provider Factory Droid, model claude-opus-5-5 (high). Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## Step 1: required reading (before any derivation)
- AGENTS.md; research-brief-2026-10-20.txt; fresh-structural-r133-brief.txt (both full).
- r131: outside REPORT.md, packet/public/report.md, plane-coloring-158.md, other-screens.md,
  reading-limits.md; discovery-structural-r131-parent/intake.json.
- r132 (unsealed, provider failure): packet/public/working-notes.md, rigidity-transcendental-158.md,
  discovery-structural-r132-parent/intake.json. Read only; no bytes changed; not treated as authenticated.
- NEW-TEN-2026-10-14.md lines 1-80 (acceptance rules).
- Not entered: fresh-arithmetic-discovery-r97, fresh-analytic-discovery-r130 (active rounds), and
  their parents.

## Step 2: family screen
- Catalogue headings extracted to scratch/families.txt (372 families). A first copy was briefly
  written to /tmp and moved into this root at once (disclosed; no other outside writes by me).
- Ranked structural-lane families by authored-history mentions (scratch/family-mention-counts.txt by
  title keyword; scratch/family-number-mentions.txt by "family NNN"). Both are navigation only.
- 181 (Erdos-Gallai): structural r33 attempted the full directed version (unresolved); excluded.
- 155 (periodic tiling): r18, r78, r115, r122 screens (connectedness paid by Kim / Demaine-Langerman;
  kernel period of exhibited tile); excluded.
- 179 (circulant Hadamard): arithmetic r72 and r78; arithmetic lane; excluded.
- 106 (hardness of colouring three-colourable graphs): no authored history note found (only corpus
  copies). Selected as principal family.

## Step 3: source 106 read
Source: preprints/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026,
build/source/{main,introduction,construction,lists,parameters}.tex read in full so far.
- thm:main: for each fixed 0<delta<1/3, deterministic poly reduction 3SAT -> graphs, SAT => 3-colourable,
  UNSAT => alpha < delta n.
- Construction: layered Label Cover phase spaces Gamma^{M_i}, pseudometric dist, half-shift T,
  clique test dist(x,Tx) <= 1/8, edges dist(x,Ty) <= 1/8 (eq:edge).
- Completeness (lem:completeness): nonexpanding evaluation phi with phi(Tx)=phi(x)+1/2, so adjacent
  phases are >= 3/8 apart; three arcs colour.
- Soundness uses 1/8 only through bump radius 1/32 and L=64 (lists.tex eq:bumps); every later
  constant depends on L only (parameters.tex).

### Observation O1 (prefreeze, not nominated)
Replacing the threshold 1/8 by eta in (0,1/4) and the bump slope 32 by 4/eta (L = 8/eta) leaves every
soundness step unchanged in form. Completeness then gives adjacent phases >= 1/2 - eta apart. If
eta < 1/(2(2k+1)), the 2k+1 half-open arcs of length 1/(2k+1) give a homomorphism to
C_{2k+1} = K_{(2k+1)/k}. So: for all fixed k>=1, delta>0, NP-hard to distinguish C_{2k+1}-colourable
graphs from alpha < delta n. Sandwich: then PCSP(H,G) is NP-hard for all non-bipartite H -> G
(Brakensiek-Guruswami conjecture), since C_{odd girth(H)} -> H and G -> K_{chi(G)}.
This is a parameter substitution in the source proof. Need: (i) primary status of the
Brakensiek-Guruswami conjecture and of PCSP(C_{2k+1},K_c); (ii) whether the substitution is already
stated in the source/companions; (iii) honest classification.

## Step 4: threshold audit of the whole source proof (prefreeze feasibility)
Read in full: preliminaries (thm:label-cover, thm:junta, lem:influences), construction, lists,
alignment (lem:alignment, lem:good-pairs), alignment-proof, coefficient (prop:aligned-bound),
parameters (proof of thm:main). Places where 1/8, 1/32, 64 or the three-colouring occur:
1. eq:clique-test and eq:edge (threshold 1/8). Exact comparison via integer multiples of 1/D.
2. lem:completeness: dist(x,Tx) >= 1/2 and adjacent phases >= 3/8 apart; three arcs.
3. eq:independent-separation: dist(A,TA) > 1/8 (from missing edges + failed clique test).
4. eq:bumps: slope 32, giving f in [-1,1], odd, =1 on A (needs dist(Tx,A) >= 1/32 for x in A),
   constant across zero links, 64-Lipschitz within copies. "Set L=64".
5. Everything later uses only: F_q L-Lipschitz, values in [-1,1], odd under T, grid restriction
   equals f, f constant across zero links (compatibility), f = 1 on A. lem:influences, thm:junta are
   stated for every finite L. lem:alignment and its proof do not involve L or the threshold.
   parameters.tex chooses beta,K,m,lambda,s,gamma,P,d,r,mu,sigma in order from (L, eps) only.
   delta<1/3 is used only for meaningfulness; any delta>0 can be replaced by min(delta,1/4).
Replacement: threshold rho = 1/(4k+2), bump (1 - dist/rho)_+, L = 2/rho = 8k+4.
- f = 1 on A: dist(Tx,A) = dist(x,TA) >= dist(A,TA) > rho, so second bump vanishes.
- Lipschitz: each bump is (1/rho)-Lipschitz for dist, dist <= sup metric within a copy, T an isometry.
- Completeness: phi nonexpanding, phi(Tx)=phi(x)+1/2. Clique test fails since 1/2 > rho.
  Edge => d_T(phi(y), phi(x)+1/2) <= rho = 1/(2N), N = 2k+1. If phi(x) in [i/N,(i+1)/N), then
  phi(x)+1/2 in [(i+k)/N + 1/(2N), (i+k+1)/N + 1/(2N)), so phi(y) lies in the half-open window
  [(i+k)/N, (i+k+2)/N) of length 2/N < 1; its arc index is i+k or i+k+1 = i-k (mod N).
  i ~ i +- k on Z_N is a cycle of length N because gcd(k,N)=1. Hence G -> C_N.
Conclusion of audit: no step of soundness depends on the value 1/8 beyond items 3-4. Feasible.

## Step 5: literature and history status (prefreeze)
- KOWZ arXiv 2003.11351v3, lines 255-300: Conjecture 1.2 (Brakensiek-Guruswami): PCSP(H,G) NP-hard
  for all non-bipartite loopless H -> G; equivalent to PCSP(C_k,K_c) for all odd k, c (sandwich).
  Thm 1.3: G = K3 case. Lines 1579-1583: iterating delta cannot give PCSP(C5,K_c) from PCSP(K3,K_c).
- Avvakumov et al. arXiv 2504.07592 (abstract only): G = K4 / 4-colourable case.
- Banakh-Barsukov-Nakajima arXiv 2605.09815v2 (18 Oct 2026, HTML, extracted text): states BG
  conjecture follows from their Thm 1.8 (r=2) ASSUMING the Rich 2-to-1 Conjecture; footnote 2 says
  approximate graph homomorphism is not known to have a full classification; cites FMW and OpenAI
  2-to-1 / UG preprints. So, as of that version, BG is described as open unconditionally.
- FMW ECCC TR26-179 / arXiv 2610.12378v1: no mention of Brakensiek, odd cycles or homomorphisms in
  the text or TeX source. Remark 1.13 supplementary material (ChatGPT 5.6 applications): not
  found by search; unread (access limit).
- Source 106 intro: only k-colourable vs not c-colourable; no odd-cycle/homomorphism corollary.
  105 intro lines 185-255: no odd-cycle statement.
- Brakensiek-Guruswami CCC 2016 abstract (Dagstuhl): 2t-2 colours; no BG-conjecture proof.
- Wrochna-Zivny arXiv 1907.00872 abstract: box-complex topology; circular cliques for H side.
- Project history: rg over frontier/proposals/scouts/notes/findings/experiments/iterations (hidden,
  no-ignore, no size cutoff) for brakensiek|odd-cycle colouring|promise graph homomorphism|PCSP(|
  approximate graph colouring|independent-set density, excluding active r97/r130 and this root
  and copied primary/upstream/src/source/literature/inputs bodies: only bibliographic hits
  (i103 web1.json, i25 target-search.json, r113 Guruswami-Kopparty, r88 operations brief text).
  No authored work on this mechanism.

Strongest integrated reduction without opening the source proof:
- thm:main (106) as a black box + sandwich gives BG for every H containing a triangle.
- KOWZ Thm 1.3/1.4 give G = K3 (and Z2-map-to-S^1 targets); Avvakumov et al. give 4-colourable G.
- Left open: H of odd girth >= 5 and chi(G) >= 5. Adjoint Lambda_k/Gamma_k fails since
  Gamma_k K_c has loops (c>=3); KOWZ: delta iteration cannot reach C5.
Operation used: open the 106 proof; shrink the half-shift threshold to 1/(4k+2) and colour by
2k+1 arcs, then re-verify the threshold-uniform soundness interface. Honest note: mechanically this
is a constant change inside the source proof; the contribution reviewer decides whether it is
TECHNICAL. Decision: freeze Theorem A + Corollary B (separate file) and write the full proof.

## Step 6: freeze
frozen-statement.md written 2026-10-20T15:51Z, SHA256 72654d283495baa80aba6349b1b5ebb9a4634ba268d7499a6187ecdd1e311256.
No source or history reads after freezing except re-reading already-cited source passages for labels.

## Step 7: proof and packet
- proof.md written after the freeze: modified construction (rho = 1/(4k+2), L = 8k+4), completeness
  by 2k+1 arcs and j -> -2j, soundness interface table, parameter order, Corollary B by odd cycle
  in H and fibre counting. Self-check of the Claim in Section 2 with lifts: window
  [(i+k)/N, (i+k+2)/N) has length 2/N < 1, so the arc index is well defined.
- Sanity check (not a proof): for fixed k the graphs have unbounded degree, so the hyperplane
  rounding of the C_N vector colouring (cuts each edge with probability 1 - 1/N) gives no
  linear independent set; no conflict with known algorithms was found.
- Primary receipts: packet/private/primary/primary-receipts.json. Reading limits, rights, report.
- Seal: MANIFEST over packet/, FINAL binding outside REPORT, MANIFEST, public report, proof and the
  frozen statement; verify.py (read-only, explicit frozen and tree anchors); controls.py runs on
  copies inside this root and writes artifact-controls.json outside the packet.
