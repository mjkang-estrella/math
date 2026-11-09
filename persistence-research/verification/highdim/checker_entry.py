"""Execute an unchanged checker without writing imported bytecode outside highdim."""
import sys
sys.dont_write_bytecode = True
import os, runpy, functools
checker = sys.argv[1]
sys.argv = sys.argv[1:]
# Both checker sources still run unchanged. Cache the trusted helper's exact
# trial-division verdict rather than repeating it at millions of residue lifts.
sys.path.insert(0, os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'indep'))
import nt
nt.isprime = functools.cache(nt.isprime)
# Repeated exact modular powers dominate the unchanged serial v14 checker.
# This is a bounded memo table for Python's builtin, not a replacement test.
exact_pow = functools.lru_cache(maxsize=500000)(pow)
runpy.run_path(checker, run_name='__main__', init_globals={'pow': exact_pow})
