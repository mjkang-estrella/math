# Preserved failures and negative checks

- Source https://arxiv.org/pdf/1803.03947v3 returned HTTP404; recorded in retrieval.jsonl. A different v1 body has an internal2024 date; not used as a nominee or historical-priority evidence.
- Initial query helper failed TypeError unsupported operand / for str and str before retrieval. Corrected module import; no source mutation or cap raise.
- First HiGHS run aborted with exit134, terminate called without an active exception, sampled groupRSS89,239,552 bytes. Explicit single-thread HiGHS option then succeeded under the identical guard; scipy warns that this option is forwarded verbatim. Both retained here; no cap was increased.
- Finite tournament top-two mass at N1,2,3,4,6,8,12,16,24 does not violate1/2. finite-tournament.json preserves direct first calculations; binomial-collapse.json retains extended checks. N24 gives approximately.5009261; N32 separates. These failures prompted exact binomial-collapse rather than expanded brute-force enumeration.
- Initial broad phrase query returned many unrelated records; preserved XML/JSON, replaced with bounded more precise title/author combinations. No irrelevant hit used as prior clearance.
- Inherited denied GitHub/ScienceDirect/Google routes were parked without retry, not silently marked clear.
