Initial guarded bind.py exited 1: r304 manifest uses a list rather than an object with files. TypeError at manifest(), before scientific assessment or preflight output. Guard: reason null, sampled peak RSS 64942080, wall 0.401s. Corrected local parser to support both actual manifest schemas; no upstream verifiers executed.

Second guarded preflight exited 1: r304 entries have hashes only; size comparison against absent field failed (README.md hash matched). Guard peak 64368640, wall 0.481s, reason null. Parser now checks upstream size when present and always records actual size.

Web service PDF retrieval for EMS deformations and integration returned timeout errors; normal direct requests to those same public PDF URLs succeeded, with bytes retained. These were not 403/429/challenges.

The institutional 393897 successor PDF request returned HTTP 403. Stopped without retry or alternate route. Its failed attempt is retained in successor-provenance.json. The independently planned Labute and matching successor documents concern different assigned problems; both succeeded. No MathDB requests, no 429, no upstream verifier executions. Public search returned unsolicited ScienceDirect results, which were not opened or relied on.
