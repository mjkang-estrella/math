# T184I134 independent substantial-contribution review, round 1

Provenance: Factory Droid / claude-opus-5-5 / high, 2026-10-20. Role: contribution review only, conditional on
correctness, at the ENTIRE unchanged frozen scope. No correctness gate, acceptance, count, priority or parent verdict is
assigned here. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb is stipulated true, including its proof operations.

## Verdict

**TECHNICAL** (conditional on correctness).

The claimed new operation, a vertex-by-vertex normalised counting closure turning weighted triangle control at
optimizer maximisers into log i(G) >= F*/C, is an actual prior statement: Lemma 2.2 ("From triangle control to
counting") of R. J. Kang, *Ode to the Ajtai-Erdos-Komlos-Szemeredi conjecture*, Zenodo record 23351325, v1, published
13 October 2026, seven days before round r134. Kang's Theorem D states the resulting mean-field bound for every finite
K_r-free graph, r >= 4, at every fugacity. Composing Kang's Lemma 2.2 with the pinned source display
`eq:optimizer-triangle` gives part 1 at the exact frozen constant in a few lines (Section 2 below). Parts 2 and 3 are a
standard test-weight evaluation and Jensen's inequality. What is not found stated verbatim is the degree-sequence
display (part 2) and the exact packaging of constants; both are one-step corollaries. Nothing nonroutine remains.

I do not label the whole statement REDISCOVERED, because I found no prior display of part 2 itself. I do record that the
claimed increment's operation and the mean-field form of part 1 are rediscovered. Even if the Kang deposit were
disregarded, Section 4 gives a source-plus-primary reduction (source closure plus Davies Section 3) under which the
operation is a one-line modification of already-paid steps; on that route alone I would still judge TECHNICAL, with
moderate rather than high confidence.

## 1. Frozen claim (unchanged)

Frozen statement SHA-256 4d491e34d80254c3b6b0d4d7a289500505bb2826fc4e4db4b3de55a92913221c; proof SHA-256
0ec0b117efaeba1e692265d7f62810dedaf5010bc47f5b640bad066f63ea46e2. For every integer r >= 3 and every finite simple
K_r-free G (zero-vertex graph allowed), with F_G(w) = sum_v w_v(1 - log w_v) - M_G(w), F*_G = max_{w>=0} F_G(w),
B_r = C_triangle(16 r^2) from source `eq:optimizer-triangle`, C_r = 2 + (3/2)B_r:

1. log i(G) >= F*_G/(3C_r);
2. log i(G) >= (12C_r)^{-1} sum_v log^2(d_v+16)/(d_v+16);
3. for n >= 1 and average degree d: log i(G) >= n log^2(d+16)/(12C_r(d+16)), and for d >= 2,
   log i(G) >= n log^2 d/(108 C_r d).

The author concedes part 3 (up to constants) and the case r = 3. The claimed increment is parts 1-2.

## 2. Strongest integrated reduction (route A: actual prior statement plus pinned source)

**Inputs.**
- (S1) Source `lem:optimizer` (optimizer.tex): maximisers exist on nonempty graphs, are positive, satisfy
  log(1/w_v) = w(N(v)), and the divergence identity `eq:optimizer-divergence`.
- (S2) Source `eq:optimizer-triangle` (coupling.tex, after the proof of `thm:weighted-triangles`): for every maximiser
  w of F_G on a finite K_r-free graph, T_G(w) <= B_r M_G(w). The cross-mass input `lem:cross-mass` is stated for every
  integer r >= 2.
- (K) Kang, Zenodo 23351325 v1, Lemma 2.2: assume C >= 4, G finite, lambda > 0, rho = C lambda/(1+lambda), and every
  nonempty induced subgraph H of G has a global maximiser w of Psi_{H,rho}(w) = sum_v w_v(1 + log rho - log w_v) - e_w(H)
  with t_w(H) <= (C/2) e_w(H). Then log Z_G(lambda) >= Psi*_{G,rho}/C.

**Derivation of part 1.** Let r >= 3 and G be finite K_r-free; the zero-vertex case is trivial. Put C = max{4, 2B_r}
and lambda = 1/(C-1), so 0 < lambda <= 1/3 and rho = C lambda/(1+lambda) = 1. Then Psi_{H,1} = F_H and t_w = T_H(w),
e_w = M_H(w). Every nonempty induced subgraph H is finite and K_r-free, has a maximiser by (S1), and every maximiser
satisfies T_H(w) <= B_r M_H(w) <= (C/2) M_H(w) by (S2). Lemma (K) gives log Z_G(1/(C-1)) >= F*_G/C. Since
lambda <= 1, Z_G(lambda) <= Z_G(1) = i(G). Finally 3C_r = 6 + (9/2)B_r >= max{4, 2B_r} = C and F*_G >= F_G(0) = 0, so

    log i(G) >= F*_G / max{4, 2B_r} >= F*_G/(3C_r).

This is part 1 with a constant at least as good as the frozen one.

**Reviewer check of (K).** I verified the proof of Lemma 2.2 line by line; it uses only C >= 4 and the stated
hypothesis. Averaging gives sum_u w_u (e_w(H[N(u)]) - (C-1) deg_w(u)) = 3t_w - 2(C-1)e_w <= 0, so some v has
e_w(H[N(v)]) <= (C-1) deg_w(v). Then c_v = w(N[v]) + e_w(H[N[v]]) = w_v(1 + deg_w v) + deg_w v + e_w(H[N(v)])
<= rho + C deg_w(v) = rho + C log(rho/w_v) <= C log(C lambda/w_v), using (1+x)e^{-x} <= 1 and
rho <= C log(1+lambda). The deletion identity (Kang Lemma 2.1 = source `eq:optimizer-divergence` specialised) bounds the
losses by w_v and c_v, and lambda e^{-c_v/C} >= w_v/C >= 1 - e^{-w_v/C}. At rho = 1 the inequality
rho <= C log(1+lambda) reads 1 <= C log(C/(C-1)), true since log(C/(C-1)) >= 1/C. Kang's Section 2 preamble fixes
C = 512r for later use, but Lemma 2.2 itself is stated under "Assume C >= 4" and its proof is valid for every such C.
If a reader insists on the preamble value, the literal prior statement is Theorem D at lambda = 1:
log i(G) >= Psi*_{G,256r}/(512r) >= F*_G/(512r) for r >= 4 (Psi_{G,rho}(w) = F_G(w) + w(V) log rho >= F_G(w) for
rho >= 1). Matching the frozen constant then is a constant substitution in an already-verified five-line proof.
I do not audit Kang's Theorem C; route A uses only Lemma 2.2 and the stipulated source.

**Part 2.** For any graph and y_v >= max(d_v, e), the weight p_v = log(y_v)/y_v gives F*_G >= (1/4) sum_v
log^2(y_v)/y_v. This is the author's Lemma 4. It is the source's own `prop:maximum-degree` test computation
(constant weight (log Delta)/Delta, the same 1 + t/4 - log t >= 2 - log 4 estimate) after the per-vertex separation
2w_u w_v <= w_u^2 + w_v^2 used by Davies to pass from (3.4) to the degree-sequence bound (3.5) in the proof of
Theorem 17. Kang Section 4.2 step <1>1 evaluates the same potential at a constant weight L/D. Combining with part 1
at y_v = d_v + 16 gives part 2.

**Part 3.** The convexity of h(x) = log^2(x+16)/(x+16) on [0, oo) and Jensen give the first inequality; d + 16 <= 9d
for d >= 2 gives the second. Davies Proposition 20 performs the same convexity-to-average-degree step for his
degree-sequence summands. Independently, Kang (18) / Theorem A already state log Z_G >= 2^{-11} n log^2(2d)/(rd) for
K_r-free G, r >= 4, d >= 2, and the author concedes the Cooper-Dutta-Mubayi route.

**r = 3.** Davies Theorem 17 with a = 0 (so C = 1) and lambda_v = 1 gives log i(G) >= max_w sum_v w_v(1 + log(log 2/w_v))
- M_G(w). Substituting w = (log 2)u for a maximiser u of F_G (so u_v <= 1) gives log i(G) >= (log 2)^2 F*_G, stronger
than part 1 for r = 3; Davies Theorem 5 (a = 0) gives degree-sequence forms. The author already concedes r = 3.

## 3. Operation-by-operation comparison with the author's proof

| Author step | Strongest prior operation |
|---|---|
| Lemma 1: F*_{G-A} >= F*_G - w(A) - M_{G[A]}(w); A = {v} and A = N[v] | Source `eq:optimizer-divergence` / `eq:closed-neighborhood-cost`; Kang Lemma 2.1 (8)-(9) states it for every A |
| Lemma 2: weighted averaging of c_v with 3T <= 3B_r M and 2M = sum w_v l_v gives c_v <= C_r(1 + l_v) | Source `eq:averaged-deletion-cost` (same expansion, same triangle term) plus `eq:optimizer-edge-weight`'s identity 2M/W = sum (w_v/W) log(1/w_v), used termwise instead of through Jensen; Kang Lemma 2.2 steps <2>2-<2>3 (same averaging, same conclusion c_v <= C log(C lambda/w_v)) |
| Proposition 3: i(G) = i(G-v) + i(G-N[v]), induction on exp(cF*), e^{-c w_v} + e^{-c c_v} >= 1 | Kang Lemma 2.2 step <2>3 (identical recurrence and closing inequality); Davies (3.1)-(3.2), Theorem 17 induction (3.7) on the maximum of the same potential; Davies 3.3.1 pivot by averaging so that e^{X_out} + lambda e^{X_in} >= 1 |
| Lemma 4: test weight log(y_v)/y_v | Source `prop:maximum-degree` second inequality; Davies (3.4) -> (3.5) separation; Kang 4.2 <1>1 |
| Part 3 Jensen | Davies Proposition 20 and the average-degree remarks after Theorems 5 and 7; Kang (18) / Theorem A for r >= 4 |

The author's constant 1/(3C_r) is weaker than the 1/max{4, 2B_r} obtained in route A, so the frozen statement adds no
constant improvement either.

## 4. Route B: reduction without the Kang deposit

This is the comparison the brief requests against the source-cited Davies Section 3.3 / proof of Theorem 17.

*What Davies Theorem 17 does.* Hypotheses: V nonempty, mad(G[N(v)]) <= a for every v, fugacities lambda_v > 0;
l_v = log(1 + lambda_v), L = max l_v, C = e^{aL}. Conclusion (3.4)-(3.5): log Z_G(lambda) >= max_w Phi_G(w),
Phi_H(w) = sum w(x)(1 + log(l_x/w(x))) - C sum_{xy} w(x)w(y), then a degree-sequence sum. Proof: induction over
induced subgraphs H of the claim log Z_H >= max Phi_H; at a maximiser choose the MAXIMUM-WEIGHT pivot v (m = w(v));
on H - v boost weights on N(v) by e^m, on H - N[v] restrict; combine with the entropy identity (3.2) at p = 1 - e^{-m}
and Lemma 16; the loss is B = (C-1)mS - C(e^m - 1)R with S = w(N(v)), R the edge mass inside N(v); R is bounded
POINTWISE for the max-weight pivot by the mad hypothesis (R <= amS/2) and by 2R <= S^2 with stationarity, and Lemma 18
gives B >= 0. The coefficient on the entropy term is sharp.

*Why it does not transfer verbatim to K_r-free graphs, r >= 4.* There is no pointwise bound on R at the max-weight
pivot (K_4-free complete tripartite graphs have dense complete-bipartite neighbourhoods), and the source supplies only
the averaged bound T <= B_r M at maximisers of the unit functional. So the pivot must be chosen by averaging, and a
constant factor must be conceded.

*Why the remaining step is routine.* Both replacements are already present. The source closure already chooses the
pivot by w/W-averaging of exactly c_v and already pays the triangle term by `eq:optimizer-triangle`; it already
records 2M/W = E_{w/W} log(1/w_v). Davies 3.3.1 (for a = 0, precisely the Buys-van den Heuvel-Kang induction) already
chooses a pivot for the two-branch recurrence by averaging closed-neighbourhood deletions, including the -3|T(H)| term
(3.22), and closes with a two-term exponential inequality (3.12)/(3.20). Accepting a constant factor removes Davies'
boost and Lemma 18 entirely: with restricted weights on both branches, the exact losses are w_v and c_v, and
stationarity e^{-l_v} = w_v makes the in-branch weight e^{-c c_v} >= e^{-1/3} w_v^{1/3} dominate the out-branch loss
c w_v. In Davies' language this is the crude-constant form of the balance between the entropy gain p log(1/p),
p ~ w_v, and p times the in-branch loss. The only line that differs from the source closure is stopping before Jensen.

## 5. Answer to the key review question

After the strongest integrated reduction, the vertexwise counting / mean-field step is a reuse of already-paid
averaging plus standard branching. It is not merely "similar": the exact step (averaged neighbourhood edge mass at an
entropy-minus-edge maximiser, a vertex with self-normalised closed-neighbourhood cost, the recurrence
i(G) = i(G-v) + i(G-N[v]), and the closing inequality e^{-w/C} + (w/C) >= 1) is Kang's Lemma 2.2, and its K_r-free
mean-field consequence is Kang's Theorem D. I did not infer routineness from the short proof. The degree-sequence
consequence (part 2) is new as a display only, and its derivation from part 1 is the standard separation/test-weight
step that Davies uses to pass from a potential bound to a degree-sequence bound. Under unchanged campaign criteria
(routine source/classical compositions, parameter substitutions and equivalent formulations do not count) the full
statement is TECHNICAL.

## 6. What remains and what is not claimed here

- Remaining operation after reduction: none nonroutine. Not found verbatim: the exact display of part 1 with the source
  constant B_r (a specialisation lambda = 1/(C-1) of Kang Lemma 2.2), and part 2 for K_r-free graphs, r >= 4. Kang
  Section 7.4 states no local statement for his n log d/(rd) bound (that remark concerns local demands for alpha, not
  counting); Davies' degree-sequence bounds need sparse or fractionally colourable neighbourhoods.
- No correctness verdict. Route A assumes Kang's Lemma 2.2, whose short proof I checked; it does not rely on Kang's
  Theorem C. No audit of the pinned source.
- Priority limits: the Kang deposit is a non-refereed Zenodo working paper (v1, 13 October 2026), self-declared as
  AI-assisted ("rinsing" the OpenAI output). Its existence and date are what matter for a prior statement. I make no
  worldwide-priority statement for or against part 2. Unread potentially relevant items are listed in reading-limits.md.
- The author's two web searches did not find the Kang deposit; this is a late discovery relative to the author's
  record, not an integrity finding.

## 7. Evidence

- Author artifacts authenticated read-only against the detached anchors; author root unchanged (stat and SHA-256
  snapshot before and after).
- Pinned source TeX independently fetched from raw GitHub at the pin and authenticated by Git blob SHA-1 against the
  complete 13223-entry tree (22 files, packet/private/source/receipts.json).
- Primary PDFs independently downloaded; the three arXiv files match the author's receipts byte-for-byte; the Kang
  deposit is new to this review (packet/private/primary/receipts.json).
- History search: packet/private/history/history-search.md.
