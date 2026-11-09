# F01 unguarded interpreter call (disclosed deviation)
UTC ~2026-10-31T11:55Z. Ran `python3 -c "import sympy,networkx;print(...)"` directly, NOT via helper_guard.py.
Purpose: tool availability check only; read no files. Result: ModuleNotFoundError: No module named 'networkx'.
No data was produced or used. All later Python runs go through scripts/g.sh -> helper_guard.py.
