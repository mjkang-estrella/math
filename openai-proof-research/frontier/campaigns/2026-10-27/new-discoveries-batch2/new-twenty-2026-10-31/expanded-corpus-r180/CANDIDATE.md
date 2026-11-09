# No qualifying candidate nominated

All twenty dispositions carry zero credit. There is no strong surviving lead and therefore no Lean packet or surrogate Lean endpoint.

## 356748: classical Golay obstruction — excluded

Let g(x)=x^11+x^9+x^7+x^6+x^5+x+1 over F_2, and let a_i be the residue of x^i modulo g, for 0<=i<23. The saved columns are distinct nonzero vectors in F_2^11. The script checks all 1+23+253+1771=2048 restricted sums of at most three columns and obtains 2048 distinct vectors. Thus these columns form a perfect restricted 3-basis of size 23 in C_2^11. For these parameters the source's listed groups have orders 2^23, 15 and 64, so this contradicts its printed classification.

This is the standard perfect binary Golay syndrome construction, with no new mechanism. Its classical origin was identified before enumerating the syndrome certificate. Verdict: zero credit, no formalization investment. See `outputs/golay.json`, `scripts/codes_inversion.py`, `logs/golay.log` and the source Conjecture 22 in `sources/2211.01893.txt`.

## 357849: swap-potential proof — excluded

Fix any edge labeling by n+1,...,n+q, and let b(v) be the sum on incident edges. Among vertex permutations p:V -> {1,...,n}, minimize

    P(p) = sum_{uv in E} p(u)p(v) + sum_v b(v)p(v).

For an adjacent pair u,v with labels a,b and equal total-open-neighborhood weights, transposing their labels changes P by -(a-b)^2. This contradicts minimality. Hence every adjacent pair has different weights, proving the source's full existence claim in ordinary mathematics.

However, the public proof archived at https://probxiv.com/problems/super-total-local-antimagic-coloring-of-graphs-9 (dated 2026-08-17) already proves the arbitrary-offset permutation lemma by exactly this potential. Its displayed application uses super-edge labels; taking its offsets to be the incident sums of edge labels n+1,...,n+q immediately proves the reserved super-vertex statement. Verdict: prior-public-lemma bridge, zero credit. Public machine judgements were not trusted; the proof body and algebra were checked directly. No prior Lean proof is asserted. See `sources/super-proof.txt`, its hashed HTML receipt, and `outputs/literature-search-4.json`.

## 381984: edgeless obstruction — excluded as a discovery route

The printed axiom quantifies over nonempty digraphs but requires positive outdegree. A one-vertex edgeless graph is a literal obstruction. Definition 5 explicitly handles arc-empty graphs separately; hence this is a formulation correction, not a substantive refutation of the intended nonempty-arc property. Searches of that intended property found no counterexample. No endpoint is nominated.

## Finite certificates not promoted

The C_2^3 x C_5 zero-sum partitions and C_3 square C_4 / C_3 square C_5 magic labelings are finite existence diagnostics. They do not prove their universal conjectures. No novel or full-scope Lean result is claimed.
