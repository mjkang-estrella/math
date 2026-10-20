# Structural r133 public report: frozen author-proof nominee (family 106)

Runner: provider Factory Droid, model claude-opus-5-5 (high). Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
No correctness, contribution, acceptance, count or priority verdict is assigned here.

## Nominee (frozen before proof; `frozen-statement.md`, SHA256 72654d283495baa80aba6349b1b5ebb9a4634ba268d7499a6187ecdd1e311256)

**Theorem A.** For every fixed integer k >= 1 and real delta > 0 there is a deterministic
polynomial-time reduction from 3-CNF formulas to graphs such that satisfiable formulas give graphs
admitting a homomorphism to the odd cycle C_{2k+1}, and unsatisfiable formulas give graphs with
independence ratio below delta.

**Corollary B (Brakensiek-Guruswami conjecture, KOWZ Conjecture 1.2).** For all finite loopless
graphs H, G with H non-bipartite and H -> G, PCSP(H, G) is NP-hard (decision; search under Turing
reductions). Also: H-colourable vs independence ratio < delta is NP-hard for each fixed delta > 0.

Full author proof: `proof.md`. Notes, feasibility audit and literature status: `working-notes.md`.

## Mechanism
Family 106 (`Hardness of finding large independent sets in three-colorable graphs`) builds a graph
from Label Cover phase spaces with a pseudometric `dist` and a half-shift T; edges join x, y with
dist(x, Ty) <= 1/8. Completeness evaluates phases at a satisfying labelling; soundness turns an
independent set into an odd bump function and uses only its Lipschitz constant L = 64 thereafter.

This round replaces 1/8 by rho = 1/(4k+2) in the clique test and edge rule, uses bump slope 1/rho and
L = 8k+4, and reruns the source's parameter order with this L. Completeness: adjacent vertices have
phases within rho of antipodal, so the 2k+1 arcs [i/(2k+1), (i+1)/(2k+1)) differ by +-k, and
j -> -2j (mod 2k+1) is a homomorphism to C_{2k+1}. Soundness: every later source step consumes only
(f odd, [-1,1]-valued, = 1 on the independent set, constant on zero links, L-Lipschitz in copies);
`proof.md` Section 3 tabulates this interface step by step. Corollary B follows from C_{odd girth} -> H
and fibre counting for loopless G.

## Strongest integrated reduction and what is unpaid by it
- 106 `thm:main` as a black box covers only H containing a triangle.
- KOWZ Thm 1.3/1.4 (G = K_3) and Avvakumov et al. 2504.07592 (4-colourable G) cover chi(G) <= 4.
- Open by these: odd girth(H) >= 5 with chi(G) >= 5. The Lambda/Gamma subdivision adjoints give a
  looped right side from K_c; KOWZ state that iterating their delta reduction cannot obtain
  PCSP(C_5, K_c) from PCSP(K_3, K_c).
- The operation here opens the 106 proof. It is mechanically a threshold change plus a new
  completeness colouring. Whether that is substantial or TECHNICAL is for the contribution review.

## Literature status found (limited search)
arXiv 2605.09815v2 (Banakh-Barsukov-Nakajima, 18 Oct 2026, after FMW and the OpenAI 2-to-1 / UG
preprints) says the Brakensiek-Guruswami conjecture follows from their Theorem 1.8 assuming the Rich
2-to-1 Conjecture, and that approximate graph homomorphism is not known to have a full
classification. FMW's text and TeX source do not mention it; their supplementary material was not
found. Source 106 and companion 105's introduction do not state an odd-cycle version. Project
history shows no work on this mechanism. New to this project; no worldwide-priority claim.

## Limits
See `reading-limits.md` and `rights.md`. Constants depend on (k, delta). The proof relies on the
pinned 106 lemmas, re-read to confirm they use only the listed interface. No formal, manuscript,
release, publication or upload work was done.
