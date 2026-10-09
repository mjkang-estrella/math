# I18 literature activity, 2026-10-09

This is a human-readable log of queries actually made in the research turn. Earlier tool output was read in session; it is not falsely represented here as a retained verbatim search response. `final-search.json` retains the final additional raw tool response and its queries. Versioned HTML documents and hashes are in `manifest.json`; derived `.txt` files are conveniences, not replacement primary sources.

Early queries:

- simultaneous largest prime factors p-1 p+1 primes smooth shifted primes
- Poisson Dirichlet distribution p-1 p+1 prime neighbors joint

Follow-up/final queries after analysis of the analytic gap:

- "p-1" "p+1" "Poisson" joint prime factors
- "p-1" "p+1" simultaneously smooth primes Wang largest prime factor
- "Poisson-Dirichlet" conditional primality joint shifted primes
- "p-1" "p+1" largest prime factors 2609.35610 2609.15166
- Wang "p-1" "p+1" "0.1779"
- "joint" "smooth" "shifted primes" number theory
- "prime factors" "p-1 and p+1" distribution Wang

The final additional domain-restricted queries are recorded exactly in `final-search.json`. Search results included irrelevant material. Only relevant primary statements actually read are used in the report. No worldwide nonexistence or priority inference is drawn from search failure.

Actual-statement read targets:

1. https://arxiv.org/html/2609.35610v1 — Zhao, Theorem 1.1; Propositions 3.5 and 3.6; the cofactor parametrization and three-form local root counts; the uniform-in-width sieve application; concluding ordering argument. This is the direct prior work on both orderings and narrow near-diagonal strips.
2. https://arxiv.org/html/2609.15166v1 — Yang, statements around Conjecture 1.3 and Theorems 1.4–1.7; Lemma 2.1 upper-sieve hypotheses and Lemma 2.3 BV form. The distinction between truncated and untruncated factors is material.
3. https://arxiv.org/html/2402.11884v4 — Bharadwaj–Rodgers, sequence hypotheses, Proposition 2, Theorem 7, Lemma 8, Remark 9. Restricted simplex and full PD hypotheses were distinguished.
4. https://arxiv.org/html/2408.03803v4 — Ford, shifted-prime probability model and Theorem 1, including its distribution hypothesis, truncation scale, and total-variation bound. This is not a full joint two-neighbor PD statement.

HTML was retrieved by Python urllib with a user-agent, versioned URL, timestamp, SHA-256, and byte length. Text was derived using standard-library HTML/math-alttext extraction. An initial extraction that failed to escape '<' inside math alttext was corrected before the statements were finalized; the retained HTML was unaffected. The final artifact seal hashes the corrected text too. An initial attempt to use an unavailable bs4 module produced no primary-document writes.

Other search hits, including specialized distribution bounds for smooth shifted primes and references to older Wang work, were not silently elevated from snippets or second-hand citations into theorem dependencies. The report consequently makes neither a claim to the strongest known exponent for every modulus family nor a claim to have comprehensively exhausted the literature.
