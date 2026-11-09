# W028 parity-circuit review read scope

Frozen 2026-10-08. No experiment was run. The optional one-certificate budget was not used: the load-bearing identities closed by direct expansion, and the n=4 boundary below was calculated by hand.

## Load-bearing parent texts

Hashes are of the files at freeze. Both still matched after this review was written.

- `research/findings/W028-rational-newton-coefficient.md`, SHA-256 `cdd5f1d84a543baca09b4251ce886615b5f6989543e68f964ca3d1d9ef0dc370`
- `research/findings/W028-parity-state.md`, SHA-256 `b02a036e8be6dffa10c8712e29c7633b93f89c3b3c04680c723cc8aa58705abd`

Copies live in `inputs/research/findings/`.

## Governance read in full

- `AGENTS.md` `dc826260f9df986dd899270772d05443d6e3a3b6db521921969ccf1c370cc094`
- `RESEARCH_TEAM.md` `b460bb1785ef5f2514a475054962d515f2210a855b474497a5291e524bf53185`
- `RESEARCH_LOOP.md` `a1491eabfb67a9df1eb76ed5eb689c5165173ae995c859baa3d8b5f3436a46e1`
- `README.md` `b91bb2101c18e59706959612683e9b8c18b7bbdafe02bddfce7abbf705c3344f`
- `docs/SPECIFICATION.md` `aedc55d05b447c895e193b131043e107db1b6cdfad732996030a08c23ea6b71a`

## Primary sources actually used

- Bostan–Mori, author PDF `sources/BoMo21.pdf`, SHA-256 `9643b42053b86f41a376af10aa040c761d5a907fc946d2b0e65d05069c7d7029`, 15 pages, dated in the file 26 Nov 2020. Read: footnote 0, the (C)/(P) distinction in §1.1, Theorem 1, §2.1, Algorithms 1 and 2, and footnote 8. The parent window at default `pdftotext` lines 454–548 was inspected and is recorded in `sources/BoMo21-locations.md`. Sections 3–4 were not audited beyond that window.
- Bostan–Christol–Dumas, arXiv:1602.00545v2, local PDF SHA-256 `f198bec8ff4c733124d71dd566ea787bf234766dd45aedf384b5573c21e45943`, already stored under `research/findings/W022-binomial-separator-review-evidence/sources/`. Read only the abstract and introduction through the binomial Mahler examples (text-extract lines 1–180): characteristic-zero cost, prime-field hypothesis, and the stated O(log N) bound after a p-dependent precomputation. Their proofs were not reproduced. The W022 review that stores this PDF was not read.

## Seen and not used as premises

- `research/STATE.md` near the W028 next-step paragraph.
- The opening of `research/findings/W026-affine-exception-review.md`, for report shape only.

## Deliberately not re-audited

W022, W023, W026, and W027, except the BCD pages named above. No solver, Lean, STATE, or task file was edited. No package was installed. No subagent was started.
