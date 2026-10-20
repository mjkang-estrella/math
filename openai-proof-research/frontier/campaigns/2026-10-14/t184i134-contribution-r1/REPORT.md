# REPORT T184I134 contribution review round 1 (outside packet)

Provenance: Factory Droid / claude-opus-5-5 / high, 2026-10-20. Independent substantial-contribution review only.
No correctness gate, acceptance, count, priority or parent verdict. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb stipulated true.

Verdict (conditional on correctness, entire unchanged frozen scope): TECHNICAL.

Author (immutable, authenticated read-only): FINAL 27ee1a396bda9f1bf61a24177cf8a8e753033c5e73234c78071a74fa928bbdf9,
MANIFEST 4264a6d43c8848418f01353f0cf3b8bb144b8dcc3943251712e8782cf6d967b0, REPORT 60c0a4806dd4135466d1b4cb553039ef01cac230db775424fc0bd9f72aab5b2f,
scope 4d491e34d80254c3b6b0d4d7a289500505bb2826fc4e4db4b3de55a92913221c, proof 0ec0b117efaeba1e692265d7f62810dedaf5010bc47f5b640bad066f63ea46e2.

Strongest reduction: Kang, Zenodo 23351325 v1 (13 Oct 2026), Lemma 2.2 (triangle control at entropy-minus-edge maximisers
implies log Z_G(lambda) >= Psi*_(G,rho)/C, same averaging, same recurrence i(G)=i(G-v)+i(G-N[v]), same closing inequality),
applied at C = max(4, 2B_r), lambda = 1/(C-1), rho = 1, with source eq:optimizer-triangle, gives log i(G) >= F*_G/max(4,2B_r)
>= F*_G/(3C_r) (part 1). Kang Theorem D states the K_r-free mean-field bound (r >= 4). Part 2 is the standard test weight
(source prop:maximum-degree computation after Davies' (3.4)->(3.5) separation); part 3 is Jensen (and Kang (18) / CDM).
Without Kang: source eq:averaged-deletion-cost used termwise (no Jensen) plus Davies Section 3 averaged-pivot recurrence.
Davies Section 3.3 / proof of Theorem 17 read in full: max-weight pivot, boosted weights, pointwise mad control of
neighbourhood edges; does not transfer verbatim to r >= 4, and the needed replacements are already paid.
Remaining: no nonroutine operation; part 2's display not found verbatim (one-step corollary). Not REDISCOVERED as a whole.

Review: packet/public/review.md SHA-256 bc2962e70cb1ebde10d62446bd5cf06b97cd3a75bd612a81b8d76f3e31c34bb7
Reading limits: packet/public/reading-limits.md SHA-256 36171a5c24bd198ad466fbd1158dfc24d600528a58e9aee75f9c135027236fbb
Packet MANIFEST SHA-256: 18f91f008f36a0b58893c9fecce1e2ec3d6702ca3e8df415f92638b8c3bdef0c
Verifier: python3 -B packet/public/verify.py --root <this root> --project <openai-proof-research> --final <FINAL.sha256> --manifest <MANIFEST sha> --report <REPORT sha>
Disclosed isolation slip: /tmp/x (history path list) written and deleted during the review.
