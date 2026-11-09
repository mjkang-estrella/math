# Rejected diagnostic: MathDB370483

Verdict: zero-credit elementary endpoint correction; no strong candidate nominated.

The source Conjecture1.2 says i>=1,n>=0,odd r>0. Put i1,r1,n0 in the residue4 clause. Odd-part overpartition counts at weights0..4 are1,2,2,4,6: each ordinary odd partition has2^d overlining choices, d the number of distinct part sizes. The ordered pair count at weight4 is therefore6+8+4+8+6=32, which is not divisible by64.

More generally, coefficient4 of F(q)^k is
6k+10k(k-1)+4k(k-1)(k-2)+16 binom(k,4)
=2k^2(k^2+8)/3.
For k2r,r odd, its2-adic valuation is5. For k2^i*r,i>=2, its valuation is2i+4. Thus the first discrepancy is a lower-parameter defect, exactly the kind excluded by the binding campaign credit rule. We do not claim that restricting to i>=2 proves the entire corrected conjecture.

Source fidelity:2509.17705 Conjecture1.2 agrees with its cited2312.12011 Conjecture8.1 and2409.02929 Conjecture1.1. Source Theorem1.11 separately proves residue7. These bodies and their receipts are in sources/ and outputs/http.jsonl. Full journal/citation and public-proof subsumption clearance is not claimed. The current LeanPool/GitHub screen is recorded in outputs/registry-screen.json.

Validation: outputs/overpartition-independent.json independently enumerates the small odd partitions; outputs/overpartition.json is a corrected modular generating-function sweep. The earlier overpartition-invalid.json is invalid and retained solely for audit. No Lean packet: no credit-eligible endpoint was nominated, and a truncated coefficient check must not be presented as a literal Lean theorem about all overpartition tuples.
