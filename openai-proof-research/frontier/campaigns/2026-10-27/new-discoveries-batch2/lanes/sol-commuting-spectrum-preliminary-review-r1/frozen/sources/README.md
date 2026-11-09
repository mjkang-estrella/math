# Frozen source bindings and access limits

All successful retrievals were written and byte-hashed before body extraction/reading. The HTTP original is represented by URL, retrieval time and frozen bytes; no claim of re-fetching an unchanged live original is made. Local original/copy pairs and reused immutable references receive separate after-reading verification.

## Primary bodies

- [1602.00208.pdf](https://arxiv.org/pdf/1602.00208v3): SHA256 `250daacc1b157043cd9c7345036eb332fc69fee8e48a12ba81eddcc2b91995b7`, frozen 2026-10-30T14:54:25.343736+00:00.
- [1603.00673.pdf](https://arxiv.org/pdf/1603.00673v2): SHA256 `a7528ff80078fa3a6593182998433fe4c3c59bd0cfd5cd55fb53425715e0b5f3`, frozen 2026-10-30T14:54:25.816143+00:00.
- [1603.05815v2.pdf](https://arxiv.org/pdf/1603.05815v2): SHA256 `ac2388d25128521afd5c3346dc4e1ff22266771110d633c7b2ad0446ad079e60`, frozen 2026-10-30T15:01:03.172462+00:00.
- [1610.09165v1.pdf](https://arxiv.org/pdf/1610.09165v1): SHA256 `5e2b994b54e68effd75f6652e94d9f4e2530fa268d648061ffad15e6ae1896fd`, frozen 2026-10-30T15:01:04.511131+00:00.
- [1901.00084.pdf](https://arxiv.org/pdf/1901.00084v1): SHA256 `9ef0e7dc3baf05f764b9d47ce2cb302211e7f3686b50ba7e80cf4e7ecf36eb55`, frozen 2026-10-30T14:54:22.348759+00:00.
- [1901.02479.pdf](https://arxiv.org/pdf/1901.02479v1): SHA256 `cf6852f618c11a2d226d77337c10a4d8a2e5a2e78c8bb6ea82ba4ecb60ac9f6d`, frozen 2026-10-30T14:54:22.911362+00:00.
- [1901.03112.pdf](https://arxiv.org/pdf/1901.03112v1): SHA256 `201c6c7f0170a43b1b9a7481057f63350f82546f39f46a33f1232858f41a5040`, frozen 2026-10-30T14:54:23.752939+00:00.
- [1901.03451.pdf](https://arxiv.org/pdf/1901.03451v1): SHA256 `70eb643e155e8d456c7d57b42aee34507a539c05e39514e575df956f22d4ea53`, frozen 2026-10-30T14:54:24.523793+00:00.
- [2301.02041.pdf](https://arxiv.org/pdf/2301.02041v2): SHA256 `0ce94072050395e6192e105892adb3373a6807da4183772643991103794ae4ff`, frozen 2026-10-30T14:54:26.294256+00:00.
- [2301.04428.pdf](https://arxiv.org/pdf/2301.04428v1): SHA256 `bee50fb8413e8930cc506f0f8ee5f77087e9bf87e26605d53bcb542341f3056a`, frozen 2026-10-30T14:54:26.786852+00:00.
- [2301.06242.pdf](https://arxiv.org/pdf/2301.06242v3): SHA256 `a4339b7809717566c399cb13d9bfe552fe5d86f8044d8058a562d7c6b7856e57`, frozen 2026-10-30T14:54:28.563339+00:00.
- [2401.08271.pdf](https://arxiv.org/pdf/2401.08271v2): SHA256 `bc03cc9feb99bb1a6e3250ec47135b096adaffdd027feb680feafe1b15558686`, frozen 2026-10-30T14:54:29.142339+00:00.
- [2401.09497.pdf](https://arxiv.org/pdf/2401.09497v1): SHA256 `6e1e027f65d317e7165206c94b3a71904f1a362517552e106767e1e9fb0a2a24`, frozen 2026-10-30T14:54:29.650998+00:00.
- [2401.11152.pdf](https://arxiv.org/pdf/2401.11152v2): SHA256 `8fd2da8c8306ecd68636e7f1b01ac2197a119d73b56c621b453cb76ad9f8d0d9`, frozen 2026-10-30T14:54:30.110283+00:00.
- [2401.12883.pdf](https://arxiv.org/pdf/2401.12883v2): SHA256 `c9a496d7261cba38f91d87c92c3939565c90f98bfda210999eae7436da26c5ff`, frozen 2026-10-30T14:54:30.762654+00:00.
- [buckley.pdf](https://archive.maths.nuim.ie/staff/sbuckley/Papers/bm_g-vs-r.pdf): SHA256 `4b6b0356978c6010d592ff925888c103aae4b09cf509716eb7cb1e93d60721c4`, frozen 2026-10-30T14:56:09.095702+00:00.
- [juras-published.pdf](https://jacodesmath.com/index.php/jacodesmath/article/download/148/135): SHA256 `162e28fb07e548e3af38c971186d6adde3e76e478f3d2992644863de2a4b7ca2`, frozen 2026-10-30T14:57:00.355373+00:00.
- [juras.pdf](https://arxiv.org/pdf/2010.01188v1): SHA256 `309c90a72f1c19e1759a99a1e884ff4cc229cfac826d3b7a5f6a62184106075e`, frozen 2026-10-30T14:55:52.220410+00:00.
- [shadow.pdf](https://arxiv.org/pdf/2505.05807v2): SHA256 `c3607266ad1870e86d8fc7d873b4fe600632e3726dd22d1b1160663c58104c4d`, frozen 2026-10-30T14:55:17.598023+00:00.

## Dated chronology and boundedness

Juráš–Ursul: arXiv first2Oct2020; publisher received25May2020, accepted30Sep2021, volume9(1)(2022), pp9–15. Equation(2), p12, explicitly open. The same content survives in the fetched published body. Buckley–MacHale author PDF is the original conjecture source; its precise release date was not independently established. Later sources cite it as2014. Mendelsohn v2 is1Nov2023. MacLean target-successor first9May2025/latest4Oct2025, prior to this campaign. Mantica regularity proof and sourcev2 both carry28Oct2016. Exact feed dates are recorded in chronology.json.

The known Mendelsohn citation missing from the OpenAlex published-record citer list demonstrates that the single reported citer is incomplete. No OpenAlex absence is treated as novelty evidence. Live OpenAI/Omega/D5/Problems registry heads are NOT cleared: forbidden GitHub API/raw/codeload/diff/patch routes were not retried. Pinned OpenAI revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb is a dated catalogue/path screen only; no relevant registry theorem body was inferred from titles. Buckley2015 and Mal’cev remain uninspected. The author papers DIRECTORY returned403; this failure is preserved and no bypass or retry was attempted. The two directly cited author PDFs had already succeeded before that denial.
