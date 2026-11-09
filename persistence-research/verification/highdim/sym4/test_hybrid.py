"""Independent labelled-lift comparison and search witness-order invariance."""
import sys
sys.dont_write_bytecode = True
import itertools
import json
import math
import pathlib
import random

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
from gen_sym import Generator
from gen_precomputed import PrecomputedGenerator


def main():
    supply = json.loads((HERE.parent/'supply_B.json').read_text())
    patterns = [(9,), (9,18), (9,9), (9,9,18), (9,18,18,54),
                (9,9,9,18,18,54), (9,9,9,9,9,9,54,54)]
    rng = random.Random(417)
    cases = labelled = 0
    for cs in patterns:
        old = Generator(cs,1223,3,supply=supply,seconds=300)
        new = PrecomputedGenerator(cs,1223,3,supply=supply,seconds=300)
        for M in (1,2,3):
            point = tuple(rng.randrange(M) for _ in range(len(cs)+1))
            r = old.key(point,M)
            for f in (2,3):
                expected = set()
                for ts in itertools.product(range(f),repeat=len(r)):
                    child = tuple(q+M*t for q,t in zip(r,ts))
                    expected.add(old.key(child,M*f))
                    labelled += 1
                actual = list(new.lifts_of(r,M,f))
                assert len(actual)==len(set(actual))==new.lift_count(r,f)
                assert set(actual)==set(old.lifts_of(r,M,f))==expected
                cases += 1
    compares = 0
    for cs in patterns[:6]:
        old = Generator(cs,1223,3,supply=supply,seconds=300)
        new = PrecomputedGenerator(cs,1223,3,supply=supply,seconds=300)
        for M in (6,12,18,30,42,60):
            for _ in range(12):
                r = old.key(tuple(rng.randrange(M) for _ in range(len(cs)+1)),M)
                a,w = old.sig(r,M)
                assert new.sig(r,M)==(a,w)
                assert {e[0] for e in old.aligned(M,a,w)}=={e[0] for e in new.aligned(M,a,w)}
                assert bool(old.kill(r,M,a,w))==bool(new.kill(r,M,a,w))
                compares += 1
    out = {'result':'PASS','hybrid_cases':cases,'labelled_lifts':labelled,
           'witness_order_comparisons':compares,
           'deeper_decimal_pins_used':False}
    (HERE/'hybrid_test_results.json').write_text(json.dumps(out,indent=1)+'\n')
    print(json.dumps(out))


if __name__ == '__main__':
    main()
