# r134 working notes (durable; original prose)

Provenance: Factory Droid / claude-opus-5-5 / high, authorized mathematical discovery, 2026-10-20 round r134.
Exclusive root: frontier/campaigns/2026-10-14/fresh-structural-discovery-r134/.

## Inputs read in full
- AGENTS.md; expanded-target-2026-10-17/research-brief-2026-10-20.txt; expanded-target-2026-10-17/fresh-structural-r134-brief.txt (re-read after a context reset).
- T106O133 disposition: discovery-structural-r133-parent/{assessment.md, intake.json, proof-r1-adoption.json, contribution-r1-adoption.json}; t106o133-contribution-r1/packet/public/{review.md, reading-limits.md}. Not read: r133 proof.md / frozen-statement.md bodies (no mechanism overlap with the direction finally chosen).
- sources/upstream.json (pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb); frontier/NEW-TEN-2026-10-14.md lines 1-60 (acceptance rules); sources/CONTENTS.md titles of all 372 families (scratch/family-titles.txt) plus full entries for the families screened below.

## Isolation disclosures
- One temporary file /tmp/r134_titles.txt was written and removed (outside the root) early in the round. The harness itself stores command output under /tmp/droid-terminal-*.
- Active roots arithmetic r98 and analytic r132 were excluded from all history searches and not read.

## Screen (navigation only)
History mention counts were made over authored files, excluding 595 files that copy the catalogue (scratch/catalogue-copies.txt), the two active roots and this root.
- 181 Erdos-Gallai: r33 directed version unresolved, r45 directed routing technical -> excluded.
- 192 Gopalan-Servedio: r25 cyclic-invariant version technical; r118 monotone screen; monotone Boolean case looks genuinely hard (FHKL 1404.3396v3 read lines 600-720: Lemmas 3.14-3.15, Thm 3.16, Conj 3.17, Prop 3.18) -> not pursued.
- 189, 190, 118: repeatedly screened in r115/r119, r23/r53/r123, r110/r116 -> excluded.
- 162 Ryser all-large-r counterexample: no history found; not developed.
- 248 Thompson F, 185 infinite matroids: intros read; not pursued.
- 184 (AEKS independence / AKS correspondence colouring): history only old F002 (edge/genus corollary) and a proposals note. Chosen for derivation.

## Family 184 source facts (independence paper, pinned)
- thm:main: r>=4, K_r-free, average degree d>=2 => alpha >= c_r n log d / d.
- F_G(w) = sum w_v(1-log w_v) - M_G(w); maximizer w has 0<w_v<=1 and stationarity log(1/w_v) = w(N(v)) (lem:optimizer).
- eq:optimizer-triangle: T_G(w) <= B_r M_G(w) at a maximizer (K_r-free G).
- prop:maximum-degree: alpha >= F*/(D_r log Delta), D_r = 3 + 1.5 B_r; closure picks v ~ w/W with deletion cost w(A_v)+M_{G[A_v]}(w).
- Identity at a maximizer: F* = W + M, 2M = sum_v w_v log(1/w_v).
- Deletion-cost identity w(A_v)+M_{G[A_v]}(w) holds equally for the fugacity functional sum w_v(1+log lambda_v - log w_v) - M(w).
- Blow-up (independent twins) of v into k copies realizes fugacity lambda_v = k; K_r-freeness, T and M depend only on totals, so the triangle bound transfers to integer fugacities >= 1.

## Direction under study: degree-sequence (local) AEKS
Target shape: alpha(G) >= c_r sum_v log(d_v)/d_v (Shearer-1991 type), cf. DMS2012 (loglog loss).
- Naive dyadic reduction from the max-degree bound loses a loglog factor (profile S_j = 1/j); for a general hereditary class
  no black-box reduction is apparent, so a genuinely local closure step is needed.
- Test weight p_v = log d_v / d_v gives F* >= (1/4) sum_v (log d_v)^2/d_v (local).
- Averaging gives a vertex with deletion cost <= C(1 + log(1/w_v)); unresolved: an accounting that charges F* by level.

## Late history discovery (before freezing)
A widened alias search (local demand, degree-sequence, Martinsson, AEKS, clique-free independence) found family-184
history that the first keyword count missed:
- r114 packet/public/screen-184.md (read in full): unrestricted local-degree correspondence palettes are false
  (bipartite recursive obstruction after DdJKP 1812.01534v2); no target frozen. Different output (colouring, not counting).
- r121 repeats that screen; r124/r125 packing-feasibility (full correspondence packing, global Delta) - only grep lines read;
  I22 combinatorial discovery treats a Hadwiger DP interface. None concerns counting independent sets or degree-sequence
  independence bounds.
The earlier "history only F002" statement is therefore superseded.

## Primary reads for the counting direction
- Davies, arXiv 2609.04654v1 (sha256 82940b92...), lines 1-449 read: Theorems 1-7, Lemma 8. Theorem 2 needs a uniform
  weighted triangle density Theta(G) <= b over ALL weights; K_r-free graphs (r>=4) violate it (complete tripartite).
  Theorems 5 and 7 give degree-sequence log Z bounds for mad-bounded / fractionally r-colourable neighbourhoods only.
- Cooper-Mubayi (UIC final PDF, sha256 0d81eb88...), lines 1-180: triangle-free count, sharpness via (2).
- Cooper-Dutta-Mubayi arXiv 1310.6672v1 (sha256 a866ea9b...), lines 80-204: Theorem 4 (hereditary transfer
  alpha -> count, average degree) and Remark 5: an AEKS bound implies i(G) >= exp(Omega(n ln^2 t / t)) for K_r-free.
  => the GLOBAL average-degree count for K_r-free is a routine composition of source184 with CDM Theorem 4.
- Buys-van den Heuvel-Kang arXiv 2503.10002v1 (sha256 ae3aadcd...), lines 1-140: triangle-free average-degree count,
  Theorem 1 redux upper bound (sharpness of order).

## Prefreeze feasibility calculations (counting direction)
Notation: w maximizer of F_G, W = w(V), l_v = log(1/w_v) = w(N(v)), A_v = {v} u N(v),
c_v = w(A_v) + M_{G[A_v]}(w) (source eq:closed-neighborhood-cost).
1. Deleting v alone: divergence identity with q = w off v, q_v = 0 gives F*_{G-v} >= F*_G - w_v (M(q-w)=0, no loops).
2. Branching recurrence i(G) = i(G-v) + i(G-A_v).  Induction target i(G) >= exp(c F*_G) needs
   exp(-c w_v) + exp(-c c_v) >= 1, which follows from c w_v <= exp(-c c_v).
3. Self-normalised vertex choice: E_{w/W}[c_v] <= (W + (4+3B)M)/W and E_{w/W}[l_v] = 2M/W, so with C = 2 + 1.5B
   some v has c_v <= C(1 + log(1/w_v)).  Then exp(-c c_v) >= e^{-cC} w_v^{cC} >= e^{-1/3} w_v for c = 1/(3C),
   and e^{-1/3} >= 1/6 >= c.  No maximum degree enters.
4. Local test weight p_v = log y_v / y_v with y_v = d_v + 16: M(p) <= (1/2) sum p_v log y_v, so
   F*_G >= sum p_v (1 + s_v/2 - log s_v) >= (1/4) sum (log y_v)^2 / y_v (1 + s/4 - log s >= 2 - log 4 > 0).
5. h(y) = (log y)^2 / y has h'' = (2L^2 - 6L + 2)/y^3, convex once L >= (3+sqrt5)/2 ~ 2.618; log 16 ~ 2.773.
   Jensen gives the average-degree corollary; for d >= 2, (log(d+16))^2/(d+16) >= (log d)^2/(9d).
6. Why not routine: the source closure charges every deletion against one global log(Delta); CDM Theorem 4 samples
   uniformly and needs an average-degree alpha bound for every sampled subgraph.  A degree-sequence count needs a
   closure without a global scale; the max-subgraph / dyadic-class reductions lose (profile analysis: masses at
   lower levels are discounted by (s/j)^2 2^{j-s}).  Steps 1-3 supply that closure.
7. Not obtained: a degree-sequence bound for alpha itself (the counting recurrence does not give it); fugacity /
   multivariate versions (would require re-running lem:cross-mass for the fugacity functional) are not claimed.
