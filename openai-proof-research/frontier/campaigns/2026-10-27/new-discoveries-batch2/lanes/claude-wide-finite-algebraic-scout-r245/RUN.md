# Reproduction (all via ./g.sh = fixed helper_guard, caps unchanged)
- Theorem 1 check:      cd diagnostics && ../g.sh python3 -P apfamily.py verify 30
- n=4 exhaustive:       cd diagnostics && ../g.sh python3 -P apirr.py exhaustive 4
- n=5 exact MILP:       cd diagnostics && (ulimit -s 1024; LC_ALL=C MALLOC_ARENA_MAX=1 taskset -c 0 ../g.sh python3 -P apmilp.py 5 180)
- random hits:          cd diagnostics && ../g.sh python3 -P apirr.py random 5 3000 5
- Cayley screen n<=8:   cd diagnostics && ../g.sh python3 -P intcay.py gen 8 && ../g.sh python3 -P intcay.py test 8
  (n=9: levels 9 0 12 / 12 16 / 16 18, then testlevels in ranges; firstfail.py; special9.py)
- DBG Conj 3.3:         cd diagnostics && LC_ALL=C ../g.sh python3 -P jtff.py
- Integrity:            ./g.sh python3 -P verify.py build ; ./g.sh python3 -P verify.py check
