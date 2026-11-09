# F02 unguarded helper calls during first final-receipt assembly (disclosed deviation)
UTC ~2026-10-31T12:5xZ. The three verifier runs themselves were guarded (scripts/g.sh -> helper_guard.py) and gave
EXIT=0 (with in-memory negative tests all detected), EXIT=1 (on-disk stray file NEGATIVE-TEST-STRAY.tmp detected
as manifest-membership extra), EXIT=0 (after removal). But the receipt JSON was assembled with three UNGUARDED
`python3 -I -c` string-escaping calls. That receipt is preserved verbatim as
failures/F02-final-receipt-attempt1-unguarded-assembly.json. The receipt was then regenerated with
scripts/final_receipt.sh + scripts/receipt_json.py, all Python under the guard, after re-generating the manifest.
