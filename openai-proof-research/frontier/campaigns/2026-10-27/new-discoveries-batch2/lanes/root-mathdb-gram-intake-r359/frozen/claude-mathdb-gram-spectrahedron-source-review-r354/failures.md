# Preserved failures and limits (r354)

1. **r349 T1 is false**: exact counterexample f = x^4 (n=2). It is preserved in `checks/check_t1_t2_counterexamples.py`.
2. **r349 T2 proof is false**: exact counterexample f = x^2y^2 + y^4 (n=2, m=2). Its numerical bound survives
   only through a different argument (Lemma C), which is unconditional only for n <= 8.
3. **No general degree-4 filling reference.** Nenashev Theorem 1 (d=k=2) needs z >= C(n+3,4)/N + N, far above m*(n).
4. **n = m = 4 probe negative.** 1180 exact samples (random + structured perturbations) gave signatures only
   in {0, ±2, ±4}, with no definite pairing. This is bounded evidence, not a proof. m(4) is undecided.
5. **EKL degree remark unverified.** The identification of the A_2 signature with the map degree was not
   checked against a source and is not relied on.
6. **Not inspected.** The numerical data behind Blomenhofer Figure 1 and Conj. 4.10/4.12 (GitHub barred;
   Zenodo record 8238688 not accessed).
7. **Prior-art search is bounded** and is not a clearance.
8. **No full-scope mechanism**, so the target is parked.
