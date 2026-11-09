# expanded-corpus-r236 (Claude lane): summary

Twenty reserved MathDB IDs (349986–350926; `reservation.json`). Literal statements were extracted with exact raw lines and hashes (`extracted.json`, `raw/`).
No Lean, lake, leanchecker or SAT/ILP binary was run. Every computation was a single capped foreground `python3 -I -B` call.
Nothing was written outside this lane. 337062 was not touched.

## Candidate (1)

**350432: Contreras-Mendoza–Hernández-Cruz uniqueness conjecture (arXiv:2104.07852, Conjecture 1): PROVED (ordinary proof).**
For $1\le i\le c-2\le k$ the unique cograph minimal $(\infty,k)$-polar obstruction of type $(c,i)$ is
$iK_1+(c-i-1)K_2+X$, where $X=K_{i,i}$ ($c=k+2$), $X=\overline{K_2}\oplus(K_2+iK_1)$ ($c=k+1$), and $X=K_1\oplus((k-c+2)K_2+iK_1)$ ($c\le k$).
The proof is self-contained and elementary, about three pages (CANDIDATE.md §3). It does not use the source's recursion theorem.
* Status: still open in the authors' 2023 doctoral thesis (Conjecture 3.27). The 2024 follow-up and web searches show no resolution, and the registry screens show none.
* Corroboration: an exhaustive cograph census through order 12 matches the source's totals (23 obstructions for $k=2$, 49 for $k=3$). A targeted census for $k\le7$ found 0 mismatches. Machine checks of all intermediate lemmas pass (38,736 instances).
* Risk: the proof is short and elementary, so root must weigh it against the short source-ingredient precedents. Lean cost is high, and the draft is UNCOMPILED: `lean-draft/PolarUniqueness.lean` gives the statement and plan, with `sorry` placeholders. Seinsche's decomposition is already in Lean Pool.

## Excluded (4)
* 350476: proved in its own source (Ng, Discrete Math. 2021).
* 350693: disproved in its own source (Hartman–Pokorná Theorem 10). For the TAG 2022 paper, zbMATH and OpenAlex give only the abstract, and its full text is only on a denied host.
* 350421: settled by Nandi–Sen–Taruni (arXiv:2306.08052).
* 350802: settled by Kovács–Somlai (arXiv:2509.02778) together with Conder–Li (D₁₈) and DCI ⇒ CI.
* Note on 350420 and 350421: the literal $(m,n)=(0,1)$ failures are zero-credit corrections and were not pursued.

## Parked (15)
* 350880: exhaustive search through every eligible tree of order ≤ 17 (6,878 trees) found no counterexample.
* 350189: open; the MathDB "solved" status is wrong. Orders n ≤ 8 are covered by theorems. The n = 9, ℓ = 5 search is infeasible in pure Python under the caps.
* 350420: the relative version is open.
* 350311: ill-posed.
* Deep, analytic or famous; disposed quickly: 349986, 350085, 350166, 350599, 350643, 350663, 350816, 350862, 350919, 350924, 350926.

Files: `results.json` (20 entries), `CANDIDATE.md`, `outputs/` (censuses, registry and history screens), `scripts/`, `logs/`, `sources/` (receipts, never overwritten), `artifact-hashes.json`.
