# Preserved failures and access limits

First checks.py execution failed at JSON serialization: numpy.int64 max_numeric_nonreal was not serializable. Guard exit 1, peak sampled group RSS 43,601,920 bytes, wall 1.444 seconds. No scientific conclusion was emitted. Conversion to native int applied and identical seed rerun. Failure preserved rather than suppressed.

First hankel.py execution computed positive exact pivots 0..35 and a negative pivot36, then failed while serializing a Fraction exceeding Python's 4300-decimal-digit conversion limit. Guard exit1; sampled groupRSS15,376,384 bytes; wall2.204 seconds. The conversion limit was NOT raised. Corrected representation uses hexadecimal numerator/denominator strings. Identical exact calculation rerun; separate verifier reconstructs fractions.

{"url": "https://github.com/the-omega-institute/trureturing", "utc": "2026-10-30T18:56:31.876748+00:00", "status": 200, "final_url": "https://github.com/the-omega-institute/trureturing", "failure": "ValueError('challenge STOP')"}
{"url": "https://github.com/openai/math", "utc": "2026-10-30T18:56:32.707981+00:00", "status": 200, "final_url": "https://github.com/openai/math", "failure": "ValueError('challenge STOP')"}
{"url": "https://math.hawaii.edu/~tom/mathfiles/cc6.pdf", "utc": "2026-10-30T18:57:56.896980+00:00", "failure": "<HTTPError 404: 'Not Found'>"}
{"kind": "source mismatch", "file": "craven1995.pdf", "actual": "Yatsenko, Volterra integral equations, pp408-419", "intended": "Craven-Csordas pp420-441", "action": "retained, not relied on; next article is a distinct lawful URL"}

The unrelated article is preserved as craven1995.pdf and not used as mathematical support. Correct1995 primary is craven1995-correct.pdf. Detection on GitHub200 pages is recorded conservatively as a challenge-detector stop, not proof of a403 response; these routes were not retried. No absent source or failed search is counted as novelty clearance.
