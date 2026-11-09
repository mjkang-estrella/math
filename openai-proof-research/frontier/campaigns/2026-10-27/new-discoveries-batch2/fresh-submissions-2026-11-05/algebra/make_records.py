import json, hashlib
raw = json.load(open('literal-records-raw.json'))
disp = {
 352655: ("not_attempted", "Adelberg-Lengyel Stirling 2-adic valuation family; needs their full machinery; no mechanism tried"),
 353030: ("not_attempted", "Guo-Li cubic binomial supercongruence mod p^{2r+2}; no mechanism tried"),
 353195: ("probable_public_resolution_unverified", "source is Tang arXiv:2201.01642 titled 'A conjecture of Baruah and Begum...'; body not read; treat as excluded until checked"),
 355133: ("not_attempted", "Wang-Sun permanent congruence per[|j-k|+delta] = 1/2 mod p"),
 356252: ("not_attempted", "Burson-Eichhorn copartition positivity; follow-up literature not checked"),
 358163: ("not_attempted", "Krattenthaler-Mueller Romik d(n) vanishing bound"),
 358661: ("not_attempted", "C. Wang 7F6 supercongruence mod p^5"),
 360461: ("not_attempted", "Guo fifth-order q-supercongruence mod Phi_n^3"),
 361205: ("not_attempted", "weak primary pseudoperfect uniqueness; source itself calls it substantially harder"),
 362111: ("COUNTEREXAMPLE_n_170", "2^170-1 has exactly 7 distinct primes; see 362111-counterexample.md, verify_170.py"),
 362288: ("proved_q_ge_9_but_not_claimed", "alpha(PSL2(q))>=q via double counting over the q(q-1)/2 non-split torus normalizers for q>=9; upper bound is the source's Thm; literal q=5 fails since PSL2(5)=A5 has alpha=3 (source table). Judged a routine extension of the source's own prime-case argument plus a domain correction: insufficient significance"),
 362564: ("infeasible", "Erdos-Straus-strength covering statement; no finite mechanism"),
 362918: ("record_defective", "MathDB statement has an empty $$ placeholder for the inequality; literal content not recoverable from the record"),
 363818: ("not_attempted", "Beierle-Beyne planar-monomial digit-sum conjecture"),
 364499: ("not_attempted", "Chen-Sun Jacobi symbol of c_p"),
 366674: ("not_attempted", "Guo-Wang q-analogue mod [n]Phi_n^3"),
 366806: ("not_attempted", "Evans-Veselov-Winn Markov-polynomial factor 4"),
 367325: ("not_attempted", "Wang-Zhang Hankel shifted periods of Motzkin powers"),
 372149: ("public_resolution", "He-Zhang arXiv:2512.17195 'Proof of a conjecture of Baruah and Sarma' (the MathDB source itself)"),
 372890: ("not_attempted", "Kalinin-Zottor Gaussian power sum valuation"),
 373310: ("public_resolution", "de Weger live page math.deweger.net/eulerliars states both parts as theorems (proof with P. Monticone, write-up in preparation); also derivable from Monier's formula. Excluded"),
 373547: ("infeasible", "FKMS analytic counting conjecture"),
 373736: ("not_attempted", "Hare-Hichri Parry powers"),
 374072: ("not_attempted", "McNew-Pomerance strong matchability"),
 374120: ("public_resolution", "Cui-Tang arXiv:2604.08839 abstract: resolves the Andrews-Dixit-Schultz-Yee conjecture"),
 374432: ("strong_target_open_gap", "necessity of A=0, B=2 mod 4; see REPORT section 3: reduction to APs with 4|A, B !=2 mod 4; S(N) odd iff N=2k^2; scaling identity for S(4N); character-sum identities; empirical check for all A<=1000 up to N<=2e5; gap: general class-group-level control"),
 374837: ("public_resolution", "the MathDB statement itself says it was proved by Cui and Tang"),
 375404: ("read_source_no_mechanism", "Sun arXiv:2606.18234v5 Conj 1.1; (i) sizes n,n+1; (ii) w_2(n)=4n-3; source read, nothing resolved; no full mechanism found"),
 381482: ("not_attempted", "q-trinomial congruence mod [p]^2"),
 381971: ("not_attempted", "2-adic constant-term valuation"),
}
out = []
for k in sorted(raw, key=int):
    r = raw[k]; i = int(k)
    assert i % 3 == 2
    out.append({"mathdb_id": i, "mod3": i % 3, "title": r["title"], "canonical_url": r["canonical_url"],
                "source_url": r["source_url"], "first_stated_year": r["first_stated_year"],
                "mirror_status": r["status"], "retrieval_source": r["retrieval_source"],
                "statement_sha256": hashlib.sha256(r["statement"].encode()).hexdigest(),
                "disposition": disp[i][0], "note": disp[i][1]})
assert len(out) == 30
json.dump(out, open('literal-records.json', 'w'), indent=1)
print(len(out), sum(1 for o in out if o['disposition'].startswith('COUNTER')))
