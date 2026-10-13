# I297 — reading, failed routes, and operational limits

The workspace was restricted to `/home/mj-kang/Documents/Dev/math/openai-proof-research`. `AGENTS.md` and `sources/upstream.json` were read first. The two completed candidate proofs and their supplied SHA-256 values were authenticated. R016, R019, completed I245/I246 and I291/I292 review records were read; the I245 detailed analytic check and completed I246 primary-source extracts were used. No live GAD/Gaussian or other live sibling work was read. The initial filename inventory was restricted to AGENTS/upstream and the four completed review IDs; unrelated inventory names were not opened.

## Decisive primary reading

The external search found Leake–Lins–Spitkovsky's 2014 paper. The web PDF open returned `Failed to fetch https://files.ele-math.com/articles/oam-08-39.pdf: (400) Timeout fetching`. A direct in-memory urllib retrieval succeeded; the bytes were piped through `pdftotext -layout - -`, with no full PDF or extracted section written to disk.

The first Section 5 display used an imprecise end search that stopped at the start of Example 5.6. A second attempt also hit that example number. The delimiter was corrected to an anchored section-heading regular expression, and the remainder through the end of Section 5 was read without truncation. Sections 1–4 were then read in full. The statement and proof of Theorem 5.7 and all its local supporting lemmas were read, not just the abstract. PDF text extraction drops some overbars and inequality symbols; none of those ambiguous formulas is used as a newly derived calculation. The old theorem's statement is unambiguous, and the new support-projection calculation is written independently in analysis.md.

Actual source scope: printed pages 699–718, Sections 1–5, including their statements and proofs. Figures were not visually inspected. Sections 6–8 were not claimed read. Theorem 5.11's reducible elliptical-arc alternatives were checked so that an irreducibility hypothesis was not silently extended to all size-five matrices.

The pinned direct and structural manuscripts were fetched from immutable raw URLs in memory. SHA-256, Git blob SHA-1, byte length, and exact selected tree entries match. Actual direct reading: lines 37–76, 162–452. Actual structural reading: lines 92–147, 863–966, 977–1065. The latter distinguishes the similar-matrix mass-one density from the original field.

ACV v3 Sections 5, 7 and 11 were read in full from completed I246 retained primary extractions. A fresh raw HTML fetch reproduced the recorded version hash. These sections were checked at their statements and proofs, including Theorem 5.3, Proposition 5.4, the dimension-three equality proof, and Section 11's scalar statements. No full external section was recopied into I297.

Jin v2 was read from the completed retained primary extraction at physical file lines 1–80, 185–287, 621–653 (primary page line labels recorded in the manifest). This includes Theorem 1, all of Lemma 4 and its proof, and the final Theorem 1 proof. The live versioned page redirects to the base page and confirms v2. The intermediate results cited inside Jin's final proof are covered by the credited reviewed input, not a new whole-proof audit in I297.

Lawrence v2 Section 4 was fetched and read in memory, including Lemma 7's proof, the old LSS family, quantum tensor-pencil construction and discriminant argument. An initial extraction attempted `bs4`, which is unavailable (`ModuleNotFoundError: No module named 'bs4'`). A standard-library extraction succeeded. Its first rendering dropped the literal `<` in the parameter condition after math conversion; the actual raw MathML/TeX annotation was reopened to read `c<1/2` and the normalization `2A=H+iK`. No code or numerical checks from the source's scan-like discriminant calculation were rerun. The original 1998 LSS full article was not newly obtained; the completed I292 access limit is inherited and stated as a limit, not evidence of absence.

## Mathematical routes examined and rejected

- The lead `(2,1,2)` / quadratic-squared-times-linear determinant was not promoted to a lemma. The old finite-boundary theorem directly rules out persistent repeated maximal support in an irreducible size-five pencil. No factor-to-reducibility inference is needed.
- A single repeated support direction does not imply a multiply generated curved arc: it can support a flat segment. The new calculation uses an interval of constant maximal multiplicity and proves positive curvature by a projection identity.
- Odd spin/tripotent classifications were not invoked. The only Clifford-type step is a fully displayed elementary two-generator block decomposition, used at the exact half-dimensional rank boundary. It assumes scalar squares and a scalar anticommutator, rather than a linear branch.
- R019 prevents generalizing size-five reducibility to dimension six. The six-dimensional norming rank-two configuration is preserved, and supplies sharpness for the ancillary rank ceiling.
- A constant coefficient compression is not an arbitrary scalar polynomial. The scalar disk theorem is applied only after extracting u,v from the actual singular pair. No strict scalar-supremum gap was inferred from individual polynomial nonattainment.
- The similarity-density endpoint route was not used to assert original numerical-range geometry or polynomial attainment.
- After the early old-theorem collision, a broader structural boundary was sought and proved: the all-dimensional Schmidt-rank ceiling for every norming pair, sharp at six. Its contribution status is deliberately unassigned; the proof reuses the same inverse mechanism and elementary block algebra. No nonroutine new construction or full classification was found.

## Validation and limits

Validation consists of the explicit projection differentiation, finite algebraic exceptional-set argument, inertia estimate, paired block decomposition, base-first tensor calculation, and scalar interpolation completion in analysis.md, together with byte authentication. There was no numerical scan, random example search, floating-point norm certificate, giant history replay, staging, commit, publication, shared-index edit or subagent. No test file or full-source cache was created. The runtime identifies GPT-6.1 Sol at high effort; no provider/model delegation was requested or performed. The user requested Standard service, which this research record does not independently certify as a transport setting.

The output resolves E5 within its dependencies. Independent proof and contribution review remain necessary before acceptance; count 13/20 is unchanged. The broader rank ceiling is not claimed new to the literature on the basis of search absence. Source-response hashes and precise semantic extents are in the authentication manifest; hashes do not imply unread sections were read.
