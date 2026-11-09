# REPORT_F — independent audit of the nd-sym closures (target 14112, 121 configurations of dimension 6–7)

Auditor: review sub-agent F. Everything is in `verification/indep4/`; stdlib Python, run as `bash -c 'ulimit -v 8000000; python3 -I …'`. Nothing outside `indep4/` was modified (the one side effect is that importing `check_sym.py` for the differential test was done with `sys.dont_write_bytecode=True`; `indep2/` and `highdim/` untouched). Nothing was committed.

## Verdict

**All 121 closures are independently confirmed.** My own checker `check_sym_F.py` (written from `notes/highdim_sym.md` and first principles before `check_sym.py`/`gen_sym.py` were opened) accepts all 121 certificates, and my own coverage map (own enumeration of the 1640 configurations of target 14112, checked equal to E's) puts each of the 121 configurations inside exactly one accepted certificate with the right K, groups and domain. M's `check_sym.py` and mine never disagree on any test I could construct (see §4).

| kill type | verdict |
|---|---|
| (a) multiset classes / lifts | **sound** |
| aligned prime kill (`ord_p(10) | M`) incl. 3/7 signatures | **sound** |
| (b) sumset kill (`ord_p(10) ∤ M`) | **sound** (conditions: sumset over all `q mod d` compatible with the class mod `gcd(d,M)`, *every* element must miss the necessary set) |
| mod-8 pin (`pin2`) | **sound with condition** `qmin ≥ v2(K)+3` (enforced by both checkers) |
| (c) decimal-tail coset (`pin_digits = k`) | **sound with condition** `k ≤ min(3, qmin)`; the 2-adic part of the modulus is `2^{max(k−t0,0)}` (divide by `2^{t0}` once) |
| (d) size leaves and brute box | **sound**. (All 84 size leaves of these certificates have `N ≤ 250047 < 10^8 ≤ min X`, hence are empty for trivial size reasons; the brute box is a consistency check, not part of the proof) |

No unsound kill type was found, and no certificate was rejected.
