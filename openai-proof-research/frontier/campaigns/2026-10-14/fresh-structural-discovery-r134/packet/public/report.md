# r134 structural discovery report (public)

Provenance: Factory Droid / claude-opus-5-5 / high; authorized mathematical discovery; pin
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb stipulated true. No correctness, contribution, acceptance or count is
self-assigned.

## Outcome
FULL AUTHOR-PROOF NOMINEE (frozen before proof). Family 184 (clique-free independence / correspondence colouring).

Frozen statement (frozen-statement.md, SHA-256 4d491e34d80254c3b6b0d4d7a289500505bb2826fc4e4db4b3de55a92913221c):
for every r >= 3 and every finite K_r-free graph G, with C_r = 2 + (3/2)B_r and B_r the constant of the source's
`eq:optimizer-triangle`,

1. log i(G) >= F*_G / (3C_r);
2. log i(G) >= (12C_r)^{-1} * sum_v (log(d_v+16))^2/(d_v+16);
3. average-degree corollaries, including log i(G) >= n (log d)^2/(108 C_r d) for d >= 2.

Here i(G) is the number of independent sets and F*_G the maximum of the source functional
sum w_v(1 - log w_v) - M_G(w).

## Proof idea
Pick a maximizer w of F_G. Averaging the source's closed-neighbourhood cost c_v against w and using the source
triangle bound gives a vertex with c_v <= C_r(1 + log(1/w_v)). In the counting recurrence
i(G) = i(G - v) + i(G - N[v]), deleting v alone costs only w_v in F*, while the other branch loses at most c_v.
With c = 1/(3C_r) the two branches satisfy e^{-c w_v} + e^{-c c_v} >= 1, so i(G) >= exp(c F*_G) follows by
induction with no degree scale. A test weight log(y_v)/y_v, y_v = d_v + 16, gives the degree-sequence form.

## Strongest reduction and claimed increment
- Routine: the average-degree count (part 3, up to constants) is source `thm:main` plus Cooper-Dutta-Mubayi
  (arXiv:1310.6672v1) Theorem 4 / Remark 5.
- Claimed new operation: a counting closure normalised vertex by vertex (Lemma 2 + Proposition 3 of proof.md),
  which removes the global log(Delta) of the source closure and yields the mean-field bound log i >= c F* and the
  degree-sequence bound. The clique hypothesis is essential (complete graphs violate log i >= c F*).
- For triangle-free graphs (r = 3), degree-sequence counting bounds already exist (Davies arXiv:2609.04654v1,
  Theorem 5, a = 0); novelty is not claimed for r = 3. Davies' framework needs a uniform weighted triangle
  density or fractionally colourable neighbourhoods, which K_r-free graphs (r >= 4) lack.
- Whether this increment is substantial rather than technical is for the separate contribution review. It is a
  project-novelty observation; no new-to-literature or priority claim is made beyond the limited searches listed
  in reading-limits.md.

## Not obtained
A degree-sequence bound for alpha(G) (local AEKS) remains open here: the counting recurrence does not give it,
and dyadic or maximal-subgraph reductions from the source lose a log log-type factor. Multivariate/fugacity versions
(which would require re-running `lem:cross-mass` for a fugacity functional) and explicit constants are not claimed.

## Other directions screened this round
181, 189, 190, 118 (prior archives), 192 (monotone Gopalan-Servedio judged hard), 162 (Ryser for all large r, not
developed), 248 (Thompson F; consequences for groups containing F looked like routine containment arguments, not checked
against primaries), 185.

## Files
working-notes.md (durable notes and prefreeze calculations), frozen-statement.md, proof.md, reading-limits.md,
rights.md, sanity.py (bounded algebra check, not a gate), verify.py (read-only artifact verifier), fetch.py,
family_map.py.
