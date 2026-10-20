# REPORT r134 (outside packet)

Provenance: Factory Droid / claude-opus-5-5 / high. Authorized mathematical discovery, round r134, 2026-10-20.
Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb stipulated true. No self-gates, no correctness/contribution verdict, no count.

Status: FROZEN_AUTHOR_PROOF_NOMINEE (full scope, frozen before proof drafting).

Claim (packet/public/frozen-statement.md, SHA-256 4d491e34d80254c3b6b0d4d7a289500505bb2826fc4e4db4b3de55a92913221c):
for every r >= 3 and every finite K_r-free graph G, log i(G) >= F*_G/(3C_r) and
log i(G) >= (12C_r)^(-1) sum_v (log(d_v+16))^2/(d_v+16), with C_r = 2 + 1.5 B_r from the source's eq:optimizer-triangle;
average-degree corollary log i(G) >= n (log d)^2/(108 C_r d) for d >= 2.

Proof: packet/public/proof.md (SHA-256 0ec0b117efaeba1e692265d7f62810dedaf5010bc47f5b640bad066f63ea46e2).
Strongest reduction: the average-degree count is routine (source thm:main + Cooper-Dutta-Mubayi arXiv:1310.6672v1 Thm 4/Rem 5).
Claimed increment: a vertexwise-normalised counting closure (cost c_v <= C_r(1+log 1/w_v) and the recurrence
i(G) = i(G-v) + i(G-N[v])) that removes the global degree scale and gives the mean-field and degree-sequence bounds.
Not claimed: novelty for r = 3 (Davies arXiv:2609.04654v1 Thm 5), a degree-sequence bound for alpha(G), fugacity versions,
explicit constants, worldwide priority.
Unresolved (outside the frozen claim): degree-sequence AEKS for alpha(G).

Read limits: packet/public/reading-limits.md. Late discoveries: r114/r121/r124/r125/I22 family-184 history found by a widened
alias search before freezing; counting-alias history search after freezing (no overlap). Disclosed /tmp slip: /tmp/r134_titles.txt
written and removed early in the round.

Packet MANIFEST SHA-256: 4264a6d43c8848418f01353f0cf3b8bb144b8dcc3943251712e8782cf6d967b0
Public report SHA-256: 2b6a8b6485e8b7cca7b53f419a1d02dce9b2dbad9dbcd4d0a22f088c81867af3
Verifier: python3 -B packet/public/verify.py --root <this root> --project <openai-proof-research> --finalhash <FINAL.sha256>
